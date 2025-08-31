#include <boost/asio.hpp>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include <memory>
#include <string>
#include <thread>
#include <vector>
#include <sstream>
#include <mutex>
#include <cstdlib>
#include <deque>
#include <stack>
#include <condition_variable>
#include <atomic>
#include <chrono>
#include <unordered_map>
#include <random>
#include <limits>

#include "KICachePolicy.h"
#include "KArcCache/KArcCache.h"

// ====== MySQL Connector/C++ ======
#include <mysql_driver.h>
#include <mysql_connection.h>
#include <cppconn/driver.h>
#include <cppconn/exception.h>
#include <cppconn/prepared_statement.h>
#include <cppconn/resultset.h>

using boost::asio::ip::tcp;

// ========================== 实用函数 ==========================
static uint64_t env_u64(const char* name, uint64_t defv) {
    if (const char* p = std::getenv(name)) {
        try { return std::stoull(p); } catch (...) { return defv; }
    }
    return defv;
}
static std::string quotedIdent(const std::string& ident) { return "`" + ident + "`"; }

// ========================== 全局统计 ==========================
struct Stats {
    std::atomic<uint64_t> reqs{0};
    std::atomic<uint64_t> gets{0};
    std::atomic<uint64_t> sets{0};
    std::atomic<uint64_t> setexs{0};
    std::atomic<uint64_t> hits{0};        // 正缓存命中
    std::atomic<uint64_t> neg_hits{0};    // 负缓存命中
    std::atomic<uint64_t> misses{0};
    std::atomic<uint64_t> mysql_err{0};
    std::atomic<uint64_t> active_conns{0};
    std::atomic<uint64_t> bloom_block{0}; // 被 Bloom 拦截的 GET
    std::atomic<uint64_t> sf_waits{0};    // singleflight 等待次数
} g_stats;

// ========================== Bloom 过滤器 ==========================
class Bloom {
public:
    explicit Bloom(size_t m_bits = (1u << 22), size_t k = 6) // 约 4M 位，6 个哈希
        : bits_((m_bits + 63) / 64), m_(m_bits), k_(k) {}

    void add(uint64_t x) {
        std::lock_guard<std::mutex> lk(mu_);
        for (size_t i = 0; i < k_; ++i) set(h(x, i) % m_);
    }
    bool maybe_contains(uint64_t x) const {
        std::lock_guard<std::mutex> lk(mu_);
        for (size_t i = 0; i < k_; ++i) if (!get(h(x, i) % m_)) return false;
        return true;
    }
private:
    static uint64_t h(uint64_t x, size_t i) {
        // 简单的多重哈希（黄金比例扰动）
        x ^= (0x9e3779b97f4a7c15ULL + (x << 6) + (x >> 2) + i * 0x165667b19e3779f9ULL);
        x ^= (x >> 33); x *= 0xff51afd7ed558ccdULL;
        x ^= (x >> 33); x *= 0xc4ceb9fe1a85ec53ULL;
        x ^= (x >> 33);
        return x;
    }
    void set(size_t pos) { bits_[pos >> 6] |= (1ULL << (pos & 63)); }
    bool get(size_t pos) const { return (bits_[pos >> 6] >> (pos & 63)) & 1ULL; }

    mutable std::mutex mu_;
    std::vector<uint64_t> bits_;
    size_t m_, k_;
};

// ========================== SingleFlight（请求合并） ==========================
struct LookupResult {
    bool found{false};          // 是否找到正值
    std::string value;          // 找到时的值
};

class SingleFlight {
public:
    // 加入某 key 的合并；leader 表示是否由自己执行实际 DB 查询
    std::shared_future<LookupResult> join(int key, bool& leader) {
        std::lock_guard<std::mutex> lk(mu_);
        auto it = inflight_.find(key);
        if (it != inflight_.end()) {
            leader = false;
            g_stats.sf_waits++;
            return it->second->get_future().share();
        }
        leader = true;
        auto p = std::make_shared<std::promise<LookupResult>>();
        auto fut = p->get_future().share();
        inflight_[key] = p;
        return fut;
    }

    void done(int key, const LookupResult& r) {
        std::shared_ptr<std::promise<LookupResult>> p;
        {
            std::lock_guard<std::mutex> lk(mu_);
            auto it = inflight_.find(key);
            if (it == inflight_.end()) return;
            p = it->second;
            inflight_.erase(it);
        }
        p->set_value(r);
    }

    void fail(int key, const std::exception_ptr& e) {
        std::shared_ptr<std::promise<LookupResult>> p;
        {
            std::lock_guard<std::mutex> lk(mu_);
            auto it = inflight_.find(key);
            if (it == inflight_.end()) return;
            p = it->second;
            inflight_.erase(it);
        }
        p->set_exception(e);
    }

private:
    std::mutex mu_;
    std::unordered_map<int, std::shared_ptr<std::promise<LookupResult>>> inflight_;
};

// ========================== MySQL 配置/连接池 ==========================
struct MySQLConfig {
    std::string host   = std::getenv("MYSQL_HOST")  ? std::getenv("MYSQL_HOST")  : "tcp://127.0.0.1:3306";
    std::string user   = std::getenv("MYSQL_USER")  ? std::getenv("MYSQL_USER")  : "root";
    std::string pass   = std::getenv("MYSQL_PASS")  ? std::getenv("MYSQL_PASS")  : "";
    std::string db     = std::getenv("MYSQL_DB")    ? std::getenv("MYSQL_DB")    : "cache";
    std::string table  = std::getenv("MYSQL_TABLE") ? std::getenv("MYSQL_TABLE") : "kv";
};

class MySQLPool {
public:
    explicit MySQLPool(const MySQLConfig& cfg, size_t max_size)
        : cfg_(cfg), driver_(sql::mysql::get_driver_instance()), max_size_(max_size) {}

    std::unique_ptr<sql::Connection> acquire() {
        std::unique_lock<std::mutex> lk(mu_);
        for (;;) {
            if (!pool_.empty()) {
                auto con = std::move(pool_.top());
                pool_.pop();
                lk.unlock();
                return con;
            }
            if (created_ < max_size_) {
                ++created_;
                lk.unlock();
                try {
                    return create_one();
                } catch (...) {
                    // 连接创建失败，回滚计数
                    std::lock_guard<std::mutex> lk2(mu_);
                    --created_;
                    cv_.notify_one(); // 防止有人在等
                    throw;
                }
            }
            // 带谓词的等待（可防止伪唤醒）
            cv_.wait(lk, [&]{ return !pool_.empty() || created_ < max_size_; });
        }
    }

    void release(std::unique_ptr<sql::Connection> con) {
        if (!con) return;
        std::lock_guard<std::mutex> lk(mu_);
        pool_.push(std::move(con));
        cv_.notify_one();
    }

private:
    std::unique_ptr<sql::Connection> create_one() {
        try {
            auto con = std::unique_ptr<sql::Connection>(driver_->connect(cfg_.host, cfg_.user, cfg_.pass));
            con->setSchema(cfg_.db);
            return con;
        } catch (const sql::SQLException& e) {
            g_stats.mysql_err++;
            std::cerr << "[MySQLPool] connect error: " << e.what() << std::endl;
            throw;
        }
    }
    MySQLConfig cfg_;
    sql::Driver* driver_{nullptr};
    size_t max_size_{8};

    std::mutex mu_;
    std::condition_variable cv_;
    std::stack<std::unique_ptr<sql::Connection>> pool_;
    size_t created_{0};
};

class MySQLClient {
public:
    explicit MySQLClient(MySQLConfig cfg, size_t pool_size)
        : cfg_(std::move(cfg)), pool_(std::make_shared<MySQLPool>(cfg_, pool_size)) {}

    bool get(int key, std::string &value) {
        try {
            auto con = pool_->acquire();
            std::string sql = "SELECT v FROM " + quotedIdent(cfg_.table) + " WHERE k=? LIMIT 1";
            std::unique_ptr<sql::PreparedStatement> ps(con->prepareStatement(sql));
            ps->setInt(1, key);
            std::unique_ptr<sql::ResultSet> rs(ps->executeQuery());
            if (rs->next()) { value = rs->getString(1); pool_->release(std::move(con)); return true; }
            pool_->release(std::move(con));
        } catch (const sql::SQLException& e) {
            g_stats.mysql_err++;
            std::cerr << "[MySQL GET] " << e.what() << std::endl;
        }
        return false;
    }

    bool upsert(int key, const std::string& value) {
        try {
            auto con = pool_->acquire();
            std::string sql =
                "INSERT INTO " + quotedIdent(cfg_.table) + " (k, v) VALUES (?, ?) "
                "ON DUPLICATE KEY UPDATE v=VALUES(v)";
            std::unique_ptr<sql::PreparedStatement> ps(con->prepareStatement(sql));
            ps->setInt(1, key);
            ps->setString(2, value);
            ps->execute();
            pool_->release(std::move(con));
            return true;
        } catch (const sql::SQLException& e) {
            g_stats.mysql_err++;
            std::cerr << "[MySQL UPSERT] " << e.what() << std::endl;
        }
        return false;
    }

    bool del(int key) {
        try {
            auto con = pool_->acquire();
            std::string sql = "DELETE FROM " + quotedIdent(cfg_.table) + " WHERE k=?";
            std::unique_ptr<sql::PreparedStatement> ps(con->prepareStatement(sql));
            ps->setInt(1, key);
            ps->execute();
            pool_->release(std::move(con));
            return true;
        } catch (const sql::SQLException& e) {
            g_stats.mysql_err++;
            std::cerr << "[MySQL DEL] " << e.what() << std::endl;
        }
        return false;
    }

private:
    MySQLConfig cfg_;
    std::shared_ptr<MySQLPool> pool_;
};

// ========================== ARC 缓存（携带 TTL/负缓存标记） ==========================
struct CacheEntry {
    std::string v;
    std::chrono::steady_clock::time_point exp; // 到期时间
    bool negative{false};                       // 是否为负缓存
};

class ArcCacheStore {
public:
    explicit ArcCacheStore(size_t capacity) : arc_(capacity), capacity_(capacity) {}

    enum class Hit { Positive, Negative, Miss };

    Hit probe(int key, std::string& value) {
        std::lock_guard<std::mutex> lk(mu_);
        CacheEntry e;
        if (!arc_.get(key, e)) return Hit::Miss;
        auto now = std::chrono::steady_clock::now();
        if (now > e.exp) return Hit::Miss; // 过期视为 miss
        if (e.negative) { return Hit::Negative; }
        value = e.v; return Hit::Positive;
    }

    void put_positive(int key, const std::string& value, std::chrono::seconds ttl) {
        std::lock_guard<std::mutex> lk(mu_);
        CacheEntry e{value, std::chrono::steady_clock::now() + ttl, false};
        arc_.put(key, e);
    }
    void put_negative(int key, std::chrono::seconds ttl) {
        std::lock_guard<std::mutex> lk(mu_);
        CacheEntry e{"", std::chrono::steady_clock::now() + ttl, true};
        arc_.put(key, e);
    }

    size_t capacity() const { return capacity_; }

private:
    std::mutex mu_;
    KamaCache::KArcCache<int, CacheEntry> arc_;
    size_t capacity_{0};
};

// ========================== 网络层 ==========================
class Server;

class Session : public std::enable_shared_from_this<Session> {
public:
    Session(boost::asio::io_context& io,
            tcp::socket socket,
            std::shared_ptr<ArcCacheStore> cache,
            std::shared_ptr<MySQLClient> mysql,
            std::shared_ptr<Bloom> bloom,
            std::shared_ptr<SingleFlight> sflight,
            uint32_t base_ttl_s,
            uint32_t jitter_s,
            uint32_t neg_ttl_s)
        : io_(io),
          socket_(std::move(socket)),
          cache_(std::move(cache)),
          mysql_(std::move(mysql)),
          bloom_(std::move(bloom)),
          sflight_(std::move(sflight)),
          base_ttl_s_(base_ttl_s),
          jitter_s_(jitter_s),
          neg_ttl_s_(neg_ttl_s),
          strand_(io_.get_executor()) {
        g_stats.active_conns++;
    }

    ~Session() {
        g_stats.active_conns--;
    }

    void start() { read_line(); }

private:
    // ---- 协议状态机 ----
    enum class ReadState { LINE, BULK_VALUE };

    // 随机 TTL（base + [0..jitter]）
    std::chrono::seconds rand_ttl() {
        if (jitter_s_ == 0) return std::chrono::seconds(base_ttl_s_);
        thread_local std::mt19937 rng{std::random_device{}()};
        std::uniform_int_distribution<uint32_t> dist(0, jitter_s_);
        return std::chrono::seconds(base_ttl_s_ + dist(rng));
    }

    void read_line() {
        auto self = shared_from_this();
        boost::asio::async_read_until(socket_, boost::asio::dynamic_buffer(inbuf_), '\n',
            boost::asio::bind_executor(strand_,
                [this, self](boost::system::error_code ec, std::size_t /*n*/) {
                    if (ec) { close(); return; }
                    while (true) {
                        auto pos = inbuf_.find('\n');
                        if (pos == std::string::npos) break;
                        std::string line = inbuf_.substr(0, pos);
                        inbuf_.erase(0, pos + 1);
                        if (!line.empty() && line.back() == '\r') line.pop_back();
                        boost::algorithm::trim(line);
                        if (!line.empty()) {
                            if (!process_line(line)) { // 进入 BULK 模式
                                return;
                            }
                        }
                    }
                    read_line();
                }
            )
        );
    }

    void read_bulk_then_set(int key, std::chrono::seconds ttl) {
        auto self = shared_from_this();
        const std::size_t need = pending_len_ + 1; // payload + '\n'
        boost::asio::async_read(socket_, boost::asio::dynamic_buffer(inbuf_),
                                boost::asio::transfer_exactly(need),
            boost::asio::bind_executor(strand_,
                [this, self, need, key, ttl](boost::system::error_code ec, std::size_t /*n*/) {
                    if (ec) { close(); return; }
                    if (inbuf_.size() < need) { send("-ERR protocol (short bulk)\n"); state_ = ReadState::LINE; read_line(); return; }
                    std::string payload = inbuf_.substr(0, pending_len_);
                    char tail = inbuf_[pending_len_];
                    inbuf_.erase(0, need);
                    if (tail != '\n') { send("-ERR protocol (bulk tail)\n"); state_ = ReadState::LINE; read_line(); return; }
                    // 执行 SET/SETEX
                    handle_set_like(key, payload, ttl);
                    state_ = ReadState::LINE;
                    read_line();
                }
            )
        );
    }

    // true = 继续行模式；false = 进入 bulk 读取
    bool process_line(const std::string& line) {
        g_stats.reqs++;
        auto toks = split_ws(line);
        if (toks.empty()) return true;
        std::string cmd = toks[0]; boost::algorithm::to_upper(cmd);

        if (cmd == "GET") {
            if (toks.size() != 2) { send("-ERR bad-arg\n"); return true; }
            int key; if (!safe_stoi(toks[1], key)) { send("-ERR bad-arg\n"); return true; }
            g_stats.gets++;
            // 1) 先查缓存（正/负）
            std::string v;
            auto h = cache_->probe(key, v);
            if (h == ArcCacheStore::Hit::Positive) {
                g_stats.hits++;
                send("$" + std::to_string(v.size()) + "\n" + v + "\n");
                return true;
            } else if (h == ArcCacheStore::Hit::Negative) {
                g_stats.neg_hits++;
                send("$-1\n");
                return true;
            }
            g_stats.misses++;

            // 2) Bloom 过滤：明确“不在集合”则快速返回（并写入负缓存，避免下一次 Bloom 还得判断）
            if (!bloom_->maybe_contains(static_cast<uint64_t>(key))) {
                cache_->put_negative(key, std::chrono::seconds(neg_ttl_s_));
                g_stats.bloom_block++;
                send("$-1\n");
                return true;
            }

            // 3) SingleFlight 合并 DB 查询
            bool leader = false;
            auto fut = sflight_->join(key, leader);
            if (leader) {
                LookupResult res;
                std::string dbv;
                if (mysql_ && mysql_->get(key, dbv)) {
                    res.found = true;
                    res.value = dbv;
                    // 正缓存 + TTL 抖动
                    cache_->put_positive(key, dbv, rand_ttl());
                    bloom_->add(static_cast<uint64_t>(key));
                } else {
                    // 负缓存
                    cache_->put_negative(key, std::chrono::seconds(neg_ttl_s_));
                    res.found = false;
                }
                sflight_->done(key, res);
                if (res.found) {
                    send("$" + std::to_string(res.value.size()) + "\n" + res.value + "\n");
                } else {
                    send("$-1\n");
                }
                return true;
            } else {
                // 等待同一查询结果
                try {
                    auto res = fut.get();
                    if (res.found) {
                        send("$" + std::to_string(res.value.size()) + "\n" + res.value + "\n");
                    } else {
                        send("$-1\n");
                    }
                } catch (...) {
                    send("-ERR mysql\n");
                }
                return true;
            }
        }
        else if (cmd == "SET" || cmd == "SETEX") {
            bool is_setex = (cmd == "SETEX");
            if ((is_setex && toks.size() < 3) || (!is_setex && toks.size() < 2)) { send("-ERR bad-arg\n"); return true; }
            int key; if (!safe_stoi(toks[1], key)) { send("-ERR bad-arg\n"); return true; }

            std::chrono::seconds ttl = rand_ttl(); // 默认 TTL
            if (is_setex) {
                long long tll = 0;
                if (!safe_stoll(toks[2], tll) || tll < 0) { send("-ERR bad-arg\n"); return true; }
                ttl = std::chrono::seconds(static_cast<uint64_t>(tll));
                g_stats.setexs++;
            } else {
                g_stats.sets++;
            }

            size_t idx_val_token = is_setex ? 3 : 2;
            if (toks.size() > idx_val_token && !toks[idx_val_token].empty() && toks[idx_val_token][0] == '$') {
                // Bulk 模式
                long long len;
                if (!safe_stoll(toks[idx_val_token].substr(1), len) || len < 0) { send("-ERR bad-arg\n"); return true; }
                pending_len_ = static_cast<size_t>(len);
                state_ = ReadState::BULK_VALUE;
                read_bulk_then_set(key, ttl);
                return false; // 暂停行模式
            } else {
                // 旧格式（不含换行）
                int parsed_key; std::string value;
                if (!parse_set_legacy(line, is_setex, parsed_key, ttl, value) || parsed_key != key) {
                    send("-ERR bad-arg\n"); return true;
                }
                if (value.find('\n') != std::string::npos || value.find('\r') != std::string::npos) {
                    send("-ERR protocol (legacy set no newline)\n"); return true;
                }
                handle_set_like(key, value, ttl);
                return true;
            }
        }
        else if (cmd == "DEL") {
            send("-ERR not-supported\n");
            return true;
        }
        else if (cmd == "STATS") {
            std::ostringstream oss;
            oss << "+STAT engine=ARC"
                << " reqs=" << g_stats.reqs.load()
                << " gets=" << g_stats.gets.load()
                << " sets=" << g_stats.sets.load()
                << " setexs=" << g_stats.setexs.load()
                << " hits=" << g_stats.hits.load()
                << " neg_hits=" << g_stats.neg_hits.load()
                << " misses=" << g_stats.misses.load()
                << " bloom_block=" << g_stats.bloom_block.load()
                << " sf_waits=" << g_stats.sf_waits.load()
                << " mysql_err=" << g_stats.mysql_err.load()
                << " active_conns=" << g_stats.active_conns.load()
                << " cap=" << cache_->capacity()
                << "\n";
            send(oss.str());
            return true;
        }
        else {
            send("-ERR unknown command\n");
            return true;
        }
    }

    void handle_set_like(int key, const std::string& v, std::chrono::seconds ttl) {
        // 1) 先写缓存（正缓存）
        cache_->put_positive(key, v, ttl);
        bloom_->add(static_cast<uint64_t>(key));
        // 2) 写透 DB（失败只告警）
        if (mysql_ && !mysql_->upsert(key, v)) {
            std::cerr << "[WARN] SET cache ok, mysql upsert failed (key=" << key << ")\n";
        }
        send("+OK\n");
    }

    static std::vector<std::string> split_ws(const std::string& line) {
        std::istringstream iss(line);
        std::vector<std::string> v; std::string t;
        while (iss >> t) v.push_back(std::move(t));
        return v;
    }

    static bool safe_stoi(const std::string& s, int& out) {
        try {
            size_t idx=0;
            long long v = std::stoll(s, &idx, 10);
            if (idx != s.size() || v < std::numeric_limits<int>::min() || v > std::numeric_limits<int>::max())
                return false;
            out = static_cast<int>(v); return true;
        } catch (...) { return false; }
    }

    static bool safe_stoll(const std::string& s, long long& out) {
        try {
            size_t idx=0;
            long long v = std::stoll(s, &idx, 10);
            if (idx != s.size()) return false;
            out = v; return true;
        } catch (...) { return false; }
    }

    // 解析旧格式：
    //   SET   <key> <value...>
    //   SETEX <key> <ttl> <value...>
    static bool parse_set_legacy(const std::string& line, bool is_setex, int& key, std::chrono::seconds& ttl, std::string& value) {
        size_t i = 0;
        auto skip_ws = [&](size_t& p){ while (p < line.size() && (line[p]==' '||line[p]=='\t')) ++p; };
        auto read_token = [&](size_t& p)->std::string{
            size_t b = p; while (p < line.size() && !(line[p]==' '||line[p]=='\t')) ++p;
            return line.substr(b, p-b);
        };

        skip_ws(i);
        if (line.compare(i,5,"SETEX")==0) {
            i+=5;
            skip_ws(i);
            auto kstr = read_token(i);
            int k; if (!safe_stoi(kstr, k)) return false;
            key = k;
            skip_ws(i);
            auto tstr = read_token(i);
            long long tll; if (!safe_stoll(tstr, tll) || tll < 0) return false;
            ttl = std::chrono::seconds(static_cast<uint64_t>(tll));
            skip_ws(i);
            if (i >= line.size()) { value.clear(); return true; }
            value = line.substr(i);
            if (!value.empty() && value.back()=='\r') value.pop_back();
            return true;
        } else if (line.compare(i,3,"SET")==0) {
            i+=3;
            skip_ws(i);
            auto kstr = read_token(i);
            int k; if (!safe_stoi(kstr, k)) return false;
            key = k;
            skip_ws(i);
            if (i >= line.size()) { value.clear(); return true; }
            value = line.substr(i);
            if (!value.empty() && value.back()=='\r') value.pop_back();
            return true;
        }
        return false;
    }

    // ---- 写队列，保证回包顺序且避免并发 write ----
    void send(const std::string &msg) {
        bool start = false;
        outq_.push_back(msg);
        if (!writing_) { writing_ = true; start = true; }
        if (start) do_write();
    }

    void do_write() {
        if (outq_.empty()) { writing_ = false; return; }
        auto self = shared_from_this();
        boost::asio::async_write(socket_, boost::asio::buffer(outq_.front()),
            boost::asio::bind_executor(strand_,
                [this, self](boost::system::error_code ec, std::size_t) {
                    if (ec) { close(); return; }
                    outq_.pop_front();
                    if (!outq_.empty()) {
                        do_write();
                    } else {
                        writing_ = false;
                    }
                }
            )
        );
    }

    void close() {
        boost::system::error_code ignored;
        socket_.shutdown(tcp::socket::shutdown_both, ignored);
        socket_.close(ignored);
        outq_.clear();
        inbuf_.clear();
    }

    // ---- 成员 ----
    boost::asio::io_context& io_;
    tcp::socket socket_;
    std::shared_ptr<ArcCacheStore> cache_;
    std::shared_ptr<MySQLClient> mysql_;
    std::shared_ptr<Bloom> bloom_;
    std::shared_ptr<SingleFlight> sflight_;

    uint32_t base_ttl_s_;
    uint32_t jitter_s_;
    uint32_t neg_ttl_s_;

    boost::asio::strand<boost::asio::io_context::executor_type> strand_;
    std::string inbuf_;

    std::deque<std::string> outq_;
    bool writing_ = false;

    ReadState state_ = ReadState::LINE;
    size_t pending_len_ = 0;
};

class CacheServer {
public:
    CacheServer(boost::asio::io_context& io, unsigned short port,
                std::shared_ptr<ArcCacheStore> cache,
                std::shared_ptr<MySQLClient> mysql,
                std::shared_ptr<Bloom> bloom,
                std::shared_ptr<SingleFlight> sflight,
                uint32_t base_ttl_s, uint32_t jitter_s, uint32_t neg_ttl_s)
        : io_(io),
          acceptor_(io, tcp::endpoint(tcp::v4(), port)),
          cache_(std::move(cache)),
          mysql_(std::move(mysql)),
          bloom_(std::move(bloom)),
          sflight_(std::move(sflight)),
          base_ttl_s_(base_ttl_s),
          jitter_s_(jitter_s),
          neg_ttl_s_(neg_ttl_s) {
        accept();
    }

private:
    void accept() {
        acceptor_.async_accept([this](boost::system::error_code ec, tcp::socket s) {
            if (!ec) {
                std::make_shared<Session>(io_, std::move(s), cache_, mysql_, bloom_, sflight_, base_ttl_s_, jitter_s_, neg_ttl_s_)->start();
            }
            accept();
        });
    }

    boost::asio::io_context& io_;
    tcp::acceptor acceptor_;
    std::shared_ptr<ArcCacheStore> cache_;
    std::shared_ptr<MySQLClient> mysql_;
    std::shared_ptr<Bloom> bloom_;
    std::shared_ptr<SingleFlight> sflight_;
    uint32_t base_ttl_s_, jitter_s_, neg_ttl_s_;
};

// ========================== main ==========================
int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <port> <arc_capacity> [mysql_pool_size]\n";
        return 1;
    }

    unsigned short port = static_cast<unsigned short>(std::stoi(argv[1]));
    size_t capacity = static_cast<size_t>(std::stoull(argv[2]));
    size_t pool_size = 8;
    if (argc >= 4) {
        pool_size = static_cast<size_t>(std::stoull(argv[3]));
    } else if (const char* env = std::getenv("MYSQL_POOL")) {
        try { pool_size = static_cast<size_t>(std::stoull(env)); } catch (...) {}
    }
    if (pool_size == 0) pool_size = 1;

    // TTL 配置
    uint32_t base_ttl_s = static_cast<uint32_t>(env_u64("CACHE_TTL", 300));
    uint32_t jitter_s   = static_cast<uint32_t>(env_u64("CACHE_JITTER", 60));
    uint32_t neg_ttl_s  = static_cast<uint32_t>(env_u64("CACHE_NEG_TTL", 60));

    auto cache = std::make_shared<ArcCacheStore>(capacity);
    auto mysql = std::make_shared<MySQLClient>(MySQLConfig{}, pool_size);
    auto bloom = std::make_shared<Bloom>();
    auto sflight = std::make_shared<SingleFlight>();

    boost::asio::io_context io;

    // 可选：优雅退出
    // boost::asio::signal_set signals(io, SIGINT, SIGTERM);
    // signals.async_wait([&](auto, int){ io.stop(); });

    CacheServer server(io, port, cache, mysql, bloom, sflight, base_ttl_s, jitter_s, neg_ttl_s);

    unsigned n = std::thread::hardware_concurrency();
    if (n < 2) n = 2; // 最少两个线程
    std::vector<std::thread> workers;
    workers.reserve(n);
    for (unsigned i = 0; i < n; ++i) workers.emplace_back([&]{ io.run(); });
    for (auto& t : workers) t.join();
    return 0;
}
