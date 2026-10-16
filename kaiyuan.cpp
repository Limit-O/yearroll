// ============================================================
// 开源史 · 108 件大事 —— 终端播放器（合并版 · 单模式）
// 视觉：全屏星空微闪 + 连续滚动 + 年代大字卡 + 年代配色 HUD
// build:  g++ -std=c++17 -O2 -Wall -o kaiyuan kaiyuan.cpp
// run:    ./kaiyuan              自动播放
//         ./kaiyuan --wait       开场暂停，空格开始
//         ./kaiyuan --speed 2    初始倍速
//         ./kaiyuan --list       列出全部事件
//         ./kaiyuan --dump 30    无终端预览前 30 行
// keys:   空格 暂停 │ ↑↓ 滚动 │ ←→ 翻页 │ +/- 速度 │ r 重播 │ q 退出
// ============================================================
#include "events_data.h"

#include <algorithm>
#include <chrono>
#include <cctype>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include <fcntl.h>
#include <poll.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>

using std::string;
using std::vector;

// ---------------- 调色板（与 HTML 版一致） ----------------
struct EraMeta { const char* id; const char* label; int r, g, b; };
static const EraMeta ERAS[] = {
    {"60s", "1960s", 251, 191, 36}, {"70s", "1970s", 245, 158, 11},
    {"80s", "1980s", 0, 229, 255},  {"90s", "1990s", 52, 211, 153},
    {"00s", "2000s", 59, 130, 246}, {"10s", "2010s", 168, 85, 247},
    {"20s", "2020s", 255, 45, 149}};
static const int N_ERAS = (int)(sizeof(ERAS) / sizeof(ERAS[0]));
static const EraMeta* eraMeta(const string& id) {
    for (int i = 0; i < N_ERAS; i++)
        if (id == ERAS[i].id) return &ERAS[i];
    return &ERAS[0];
}
static const int GOLD[3] = {212, 184, 150};
static const int DIMC[3] = {138, 138, 165};
static const int TXTC[3] = {220, 220, 232};

// ---------------- 选项 ----------------
static bool opt_color = true, opt_wait = false, opt_list = false;
static bool g_truecolor = true;
static double opt_speed = 1.0;
static long opt_dump = -1;

// ---------------- 颜色 ----------------
static int to256(int r, int g, int b) {
    int R = r * 5 / 255, G = g * 5 / 255, B = b * 5 / 255;
    return 16 + 36 * R + 6 * G + B;
}
static string fg3(int r, int g, int b, double k = 1.0) {
    if (!opt_color) return "";
    int R = std::min(255, (int)(r * k)), G = std::min(255, (int)(g * k)),
        B = std::min(255, (int)(b * k));
    char buf[48];
    if (g_truecolor)
        snprintf(buf, sizeof buf, "\033[38;2;%d;%d;%dm", R, G, B);
    else
        snprintf(buf, sizeof buf, "\033[38;5;%dm", to256(R, G, B));
    return buf;
}
static const string BOLD = "\033[1m";
static const string RESET = "\033[0m";

// ---------------- UTF-8 宽度（数据已规范化：CJK/全角宽，制表符/ASCII 窄） ----------------
static int utf8_next(const string& s, size_t i, int& len) {
    unsigned char c = (unsigned char)s[i];
    if (c < 0x80) { len = 1; return c; }
    if ((c & 0xE0) == 0xC0) { len = 2; return c & 0x1F; }
    if ((c & 0xF0) == 0xE0) { len = 3; return c & 0x0F; }
    if ((c & 0xF8) == 0xF0) { len = 4; return c & 0x07; }
    len = 1; return '?';
}
static int cp_width(int cp) {
    if (cp < 0x80) return 1;
    if (cp >= 0x2500 && cp <= 0x25FF) return 1;   // 制表符/方块
    if (cp >= 0x2E80) return 2;                    // CJK、全角、「」
    return 1;
}
static int strw(const string& s) {
    int w = 0;
    for (size_t i = 0; i < s.size();) {
        unsigned char c = (unsigned char)s[i];
        if (c == 0x1b) {  // ANSI 转义：不计宽
            size_t j = i + 1;
            while (j < s.size() && !isalpha((unsigned char)s[j])) j++;
            if (j < s.size()) j++;
            i = j;
            continue;
        }
        int len, cp = utf8_next(s, i, len);
        w += cp_width(cp);
        i += len;
    }
    return w;
}

// ---------------- 数据规范化（消歧义宽度字符） ----------------
static void rep_all(string& s, const string& a, const string& b) {
    size_t p;
    while ((p = s.find(a)) != string::npos) s.replace(p, a.size(), b);
}
static string norm(string s) {
    rep_all(s, "\xe2\x80\x9c", "\xe3\x80\x8c");  // “ → 「
    rep_all(s, "\xe2\x80\x9d", "\xe3\x80\x8d");  // ” → 」
    rep_all(s, "\xe2\x80\x98", "\xe3\x80\x8c");  // ‘ → 「
    rep_all(s, "\xe2\x80\x99", "\xe3\x80\x8d");  // ’ → 」
    rep_all(s, "\xe2\x80\x94", "\xe2\x94\x80");  // — → ─
    rep_all(s, "\xe2\x80\xa6", "..");            // … → ..
    rep_all(s, "\xc2\xb7", ".");                 // · → .
    rep_all(s, "\xe2\x98\x85", "*");             // ★ → *
    return s;
}

struct Ev {
    int y;
    string t, d, lg, era;
    bool core;
};
static vector<Ev> EV;
static int N_CORE = 0;

// ---------------- 排版工具 ----------------
static string spaces(int n) { return n > 0 ? string((size_t)n, ' ') : ""; }
static string rep(const char* ch, int n) {
    string s;
    for (int i = 0; i < n; i++) s += ch;
    return s;
}
static string padCenter(const string& s, int rowW) {
    int pad = (rowW - strw(s)) / 2;
    if (pad < 0) pad = 0;
    return spaces(pad) + s;
}
static string truncw(const string& s, int maxw) {
    if (strw(s) <= maxw) return s;
    string out;
    int w = 0;
    for (size_t i = 0; i < s.size();) {
        unsigned char c = (unsigned char)s[i];
        if (c == 0x1b) {
            size_t j = i + 1;
            while (j < s.size() && !isalpha((unsigned char)s[j])) j++;
            if (j < s.size()) j++;
            out += s.substr(i, j - i);
            i = j;
            continue;
        }
        int len, cp = utf8_next(s, i, len);
        int cw = cp_width(cp);
        if (w + cw > maxw - 2) { out += ".." + string(RESET); break; }
        out += s.substr(i, len);
        w += cw;
        i += len;
    }
    return out;
}
static vector<string> wrapw(const string& s, int maxw) {
    vector<string> out;
    string cur;
    int cw = 0;
    size_t i = 0;
    while (i < s.size()) {
        int len, cp = utf8_next(s, i, len);
        int w = cp_width(cp);
        if (cw + w > maxw && cw > 0) {
            if (isalnum((unsigned char)cur.back())) {  // ASCII 词不折断
                size_t p = cur.find_last_not_of(
                    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789");
                if (p != string::npos && p + 1 < cur.size()) {
                    string tail = cur.substr(p + 1);
                    cur.resize(p + 1);
                    out.push_back(cur);
                    cur = tail;
                    cw = strw(tail);
                    i += len;
                    continue;
                }
            }
            out.push_back(cur);
            cur.clear();
            cw = 0;
            if (w > maxw) { out.push_back(s.substr(i, len)); i += len; continue; }
        }
        cur += s.substr(i, len);
        cw += w;
        i += len;
    }
    if (!cur.empty()) out.push_back(cur);
    return out;
}

// ---------------- 大字数字（年代卡） ----------------
static const char* DIG[10][5] = {
    {"███", "█ █", "█ █", "█ █", "███"}, {" █ ", "██ ", " █ ", " █ ", "███"},
    {"███", "  █", "███", "█  ", "███"}, {"███", "  █", "███", "  █", "███"},
    {"█ █", "█ █", "███", "  █", "  █"}, {"███", "█  ", "███", "  █", "███"},
    {"███", "█  ", "███", "█ █", "███"}, {"███", "  █", "  █", "  █", "  █"},
    {"███", "█ █", "███", "█ █", "███"}, {"███", "█ █", "███", "  █", "███"}};
static const char* DIGS[5] = {"   ", "███", "█  ", "███", "███"};  // s
static vector<string> bigtext(const string& s) {
    vector<string> rows(5);
    bool first = true;
    for (char c : s) {
        const char** g = nullptr;
        if (c >= '0' && c <= '9') g = DIG[c - '0'];
        else if (c == 's' || c == 'S') g = DIGS;
        if (!g) continue;
        for (int r = 0; r < 5; r++) rows[r] += (first ? "" : "  ") + string(g[r]);
        first = false;
    }
    return rows;
}

// ---------------- 帧缓冲 ----------------
struct Frame {
    string out;
    int w = 0, h = 0;
    void begin(int W, int H) { w = W; h = H; out.clear(); out += "\033[?2026h"; }
    void put(int row, const string& s) {
        if (row < 0 || row >= h) return;
        char b[16];
        snprintf(b, sizeof b, "\033[%d;1H", row + 1);
        out += b;
        out += s;
        out += RESET;
        out += "\033[K";
    }
    void putR(int row, const string& s) { put(row, spaces(w - 1 - strw(s)) + s); }
    void finish() { out += "\033[?2026l"; }
};

// ---------------- 终端 ----------------
static termios g_orig;
static bool g_tty = false;
static volatile sig_atomic_t g_resized = 0, g_quit = 0;
static void on_winch(int) { g_resized = 1; }
static void on_term(int) { g_quit = 1; }
static void raw_on() {
    termios t{};
    tcgetattr(0, &t);
    g_orig = t;
    t.c_lflag &= ~(ICANON | ECHO | ISIG | IEXTEN);
    t.c_iflag &= ~(IXON | ICRNL | BRKINT | INPCK | ISTRIP);
    t.c_cc[VMIN] = 0;
    t.c_cc[VTIME] = 0;
    tcsetattr(0, TCSANOW, &t);
}
static void raw_off() { tcsetattr(0, TCSANOW, &g_orig); }
struct Guard {
    ~Guard() {
        if (g_tty) {
            raw_off();
            const char* s = "\033[0m\033[?25h\033[?1049l\n";
            (void)!::write(1, s, strlen(s));
        }
    }
};
static void term_size(int& W, int& H) {
    winsize ws{};
    if (ioctl(1, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 4 && ws.ws_row > 4) {
        W = ws.ws_col;
        H = ws.ws_row;
    } else {
        W = 100; H = 30;
    }
}

// ---------------- 星空（全程氛围层） ----------------
struct Star { int x, y; const char* ch; int ph; };
static vector<Star> g_stars;
static void makeStars(int W, int H) {
    g_stars.clear();
    unsigned seed = 20251008;
    auto rnd = [&]() { seed = seed * 1103515245 + 12345; return (seed >> 16) & 0x7fff; };
    static const char* CH[] = {".", ".", "*", "+", ":"};
    int n = W * H / 150;
    for (int i = 0; i < n; i++)
        g_stars.push_back({(int)(rnd() % (unsigned)W), 2 + (int)(rnd() % (unsigned)std::max(1, H - 5)),
                           CH[rnd() % 5], (int)(rnd() % 47)});
}
static void drawStars(Frame& f, int tick) {
    for (const Star& st : g_stars) {
        bool bright = ((tick + st.ph) % 47) < 3;
        string col = bright ? fg3(GOLD[0], GOLD[1], GOLD[2])
                            : fg3(DIMC[0], DIMC[1], DIMC[2], .5);
        f.put(st.y, spaces(st.x) + col + st.ch + RESET);
    }
}

// ---------------- 文档流 ----------------
struct DocLine { string text; int ev; };
static vector<DocLine> doc;
static int docW = 96;

static void buildDoc(int W) {
    docW = std::min(100, std::max(60, W - 4));
    doc.clear();
    auto blank = [&]() { doc.push_back({"", -1}); };
    auto center = [&](const string& colored) {
        doc.push_back({padCenter(colored, docW), -1});
    };
    // 片头
    blank();
    blank();
    center(fg3(GOLD[0], GOLD[1], GOLD[2]) + BOLD + "开　源　改　变　世　界" + RESET);
    center(fg3(255, 255, 255) + BOLD + "108 件大事（合并版）" + RESET);
    blank();
    center(fg3(DIMC[0], DIMC[1], DIMC[2]) +
           "1969 ── 2025 │ 56 年 │ 29 个核心事件 │ 从 Unix 到开源 AI" + RESET);
    blank();
    blank();
    string lastEra = "";
    for (int e = 0; e < (int)EV.size(); e++) {
        const Ev& ev = EV[e];
        const EraMeta* em = eraMeta(ev.era);
        if (ev.era != lastEra) {  // 年代大字卡
            lastEra = ev.era;
            blank();
            vector<string> art = bigtext(em->label);
            for (auto& r : art) center(fg3(em->r, em->g, em->b) + BOLD + r + RESET);
            blank();
            center(fg3(em->r, em->g, em->b) + "年　代" + RESET);
            center(fg3(GOLD[0], GOLD[1], GOLD[2], .55) + rep("\xe2\x94\x80", 16) + RESET);
            blank();
        }
        // 标题行：YYYY │ Title            [CORE]
        string title = truncw(ev.t, docW - 9 - (ev.core ? 8 : 0));
        int tw = strw(title);
        string line = fg3(em->r, em->g, em->b) + BOLD + "  " + std::to_string(ev.y) + " " + RESET +
                      fg3(DIMC[0], DIMC[1], DIMC[2]) + "│ " + RESET +
                      fg3(255, 255, 255) + BOLD + title + RESET;
        int used = 9 + tw;
        if (ev.core) {
            line += spaces(std::max(0, docW - used - 8)) +
                    fg3(GOLD[0], GOLD[1], GOLD[2]) + "[CORE]" + RESET;
        } else {
            line += spaces(std::max(0, docW - used));
        }
        doc.push_back({line, e});
        // 正文
        string bodyText = ev.core && !ev.lg.empty() ? ev.lg : ev.d;
        for (auto& b : wrapw(bodyText, docW - 14))
            doc.push_back({spaces(12) + fg3(TXTC[0], TXTC[1], TXTC[2], .8) + b + RESET, e});
        blank();
    }
    // 片尾
    blank();
    blank();
    center(fg3(255, 255, 255) + BOLD + "56 年，108 个节点。" + RESET);
    blank();
    center(fg3(TXTC[0], TXTC[1], TXTC[2]) +
           "今天每一台服务器、每一部手机、每一次 AI 对话，背后都是开源。" + RESET);
    center(fg3(GOLD[0], GOLD[1], GOLD[2]) + BOLD + "它不是一个许可证，是一种做事的方式。" + RESET);
    blank();
    center(fg3(DIMC[0], DIMC[1], DIMC[2]) +
           "108 个里程碑 │ 56 年跨度 │ 29 个核心事件" + RESET);
    blank();
    center(fg3(DIMC[0], DIMC[1], DIMC[2], .7) + "── FIN ──" + RESET);
    blank();
    blank();
}

// ---------------- 镶边 ----------------
static void drawChrome(Frame& f, int W, int H, const EraMeta* em, const string& rightTop,
                       double frac, const string& botLeft, const string& botRight) {
    f.put(0, fg3(GOLD[0], GOLD[1], GOLD[2], .9) + BOLD + " 开源史 " + RESET +
             fg3(DIMC[0], DIMC[1], DIMC[2], .9) + "108 件大事" + RESET);
    f.putR(0, fg3(em->r, em->g, em->b) + BOLD + rightTop + RESET);
    int bw = W - 2, fill = (int)(frac * bw);
    if (fill < 0) fill = 0;
    if (fill > bw) fill = bw;
    f.put(1, " " + fg3(em->r, em->g, em->b) + rep("\xe2\x96\x88", fill) +
                 fg3(DIMC[0], DIMC[1], DIMC[2], .45) + rep("\xe2\x96\x91", bw - fill) + RESET);
    f.put(H - 2, padCenter(fg3(DIMC[0], DIMC[1], DIMC[2], .8) +
              "空格 暂停 │ ↑ ↓ 滚动 │ ← → 翻页 │ +/- 速度 │ r 重播 │ q 退出" + RESET, W));
    string bl = fg3(em->r, em->g, em->b) + BOLD + " >" + RESET + " " + botLeft;
    string full = bl + "   " + botRight;
    int maxw = W - 1;
    if (strw(bl) + strw(botRight) + 3 > maxw)
        full = truncw(bl, maxw - strw(botRight) - 5) + "   " + botRight;
    f.put(H - 1, " " + full);
}

// ---------------- 渲染一帧 ----------------
static void renderFrame(Frame& f, int W, int H, double offset, bool playing, double speed,
                        bool ended, int tick) {
    double maxOff = std::max(1.0, (double)doc.size() - (H - 6));
    double frac = std::min(1.0, std::max(0.0, offset / maxOff));
    // 当前事件：从视口中线向两侧找最近的事件行
    int center = (int)offset + (H - 6) / 2;
    int cur = -1;
    for (int d = 0; d < (int)doc.size() && cur < 0; d++) {
        if (center + d >= 0 && center + d < (int)doc.size() && doc[center + d].ev >= 0)
            cur = doc[center + d].ev;
        else if (center - d >= 0 && center - d < (int)doc.size() && doc[center - d].ev >= 0)
            cur = doc[center - d].ev;
    }
    const EraMeta* em = cur >= 0 ? eraMeta(EV[cur].era) : &ERAS[0];
    drawStars(f, tick);
    char pctbuf[16], spbuf[16], ib[32];
    snprintf(pctbuf, sizeof pctbuf, "%d%%", (int)std::lround(frac * 100));
    snprintf(spbuf, sizeof spbuf, "%.2gx", speed);
    string state = ended ? (string) "已结束"
                        : playing ? (string) "播放中 " + spbuf : (string) "暂停 " + spbuf;
    string botR = state + " │ " + pctbuf;
    string botL;
    if (cur >= 0) {
        snprintf(ib, sizeof ib, "%03d/%d", cur + 1, (int)EV.size());
        botL = fg3(255, 255, 255) + BOLD + ib + RESET +
               fg3(DIMC[0], DIMC[1], DIMC[2]) + " │ " + RESET +
               fg3(255, 255, 255) + std::to_string(EV[cur].y) + RESET +
               fg3(DIMC[0], DIMC[1], DIMC[2]) + " │ " + RESET +
               fg3(em->r, em->g, em->b) + em->label + RESET +
               fg3(DIMC[0], DIMC[1], DIMC[2]) + " │ " + RESET +
               fg3(255, 255, 255) + EV[cur].t + RESET;
    } else {
        botL = fg3(DIMC[0], DIMC[1], DIMC[2]) + "开场" + RESET;
    }
    drawChrome(f, W, H, em, em->label, frac, botL, botR);
    for (int r = 2; r < H - 2; r++) {
        int li = (int)offset + (r - 2);
        if (li < 0 || li >= (int)doc.size()) continue;
        f.put(r, " " + doc[li].text);
    }
}

// ---------------- 输入 ----------------
enum Act { A_NONE, A_TOGGLE, A_NEXT, A_PREV, A_UP, A_DOWN, A_QUIT, A_FASTER, A_SLOWER,
           A_RESTART };
static Act readKeys() {
    static char buf[64];
    static size_t blen = 0;
    pollfd p{0, POLLIN, 0};
    if (poll(&p, 1, 0) <= 0) return A_NONE;
    ssize_t n = ::read(0, buf + blen, sizeof buf - blen);
    if (n <= 0) return A_NONE;
    blen += n;
    size_t i = 0;
    while (i < blen) {
        char c = buf[i];
        Act a = A_NONE;
        if (c == 0x1b) {
            if (i + 2 < blen && buf[i + 1] == '[') {
                switch (buf[i + 2]) {
                    case 'C': a = A_NEXT; break;
                    case 'D': a = A_PREV; break;
                    case 'A': a = A_UP; break;
                    case 'B': a = A_DOWN; break;
                    default: break;
                }
                i += 3;
            } else if (blen - i == 1) {  // 孤立 ESC：等 8ms 确认
                pollfd p2{0, POLLIN, 0};
                if (poll(&p2, 1, 8) > 0) {
                    ssize_t m = ::read(0, buf + blen, sizeof buf - blen);
                    if (m > 0) { blen += m; continue; }
                }
                a = A_QUIT;
                i += 1;
            } else {
                i += 1;
            }
            if (a != A_NONE) { memmove(buf, buf + i, blen - i); blen -= i; return a; }
            continue;
        }
        switch (c) {
            case ' ': a = A_TOGGLE; break;
            case 'q': case 'Q': case 0x03: a = A_QUIT; break;
            case 'n': case 'l': a = A_NEXT; break;
            case 'p': case 'h': a = A_PREV; break;
            case 'j': a = A_DOWN; break;
            case 'k': a = A_UP; break;
            case '+': case '=': a = A_FASTER; break;
            case '-': case '_': a = A_SLOWER; break;
            case 'r': case 'R': a = A_RESTART; break;
            default: break;
        }
        i++;
        if (a != A_NONE) { memmove(buf, buf + i, blen - i); blen -= i; return a; }
    }
    blen = 0;
    return A_NONE;
}

// ---------------- main ----------------
int main(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "--wait") opt_wait = true;
        else if (a == "--list") opt_list = true;
        else if (a == "--no-color") opt_color = false;
        else if (a == "--256") g_truecolor = false;
        else if (a == "--speed" && i + 1 < argc) opt_speed = atof(argv[++i]);
        else if ((a == "--dump" || a == "--dumpscroll") && i + 1 < argc) opt_dump = atol(argv[++i]);
        else if (a == "--help" || a == "-h") {
            printf("用法: kaiyuan [--wait] [--speed x] [--256] [--no-color] [--dump N] [--list]\n");
            return 0;
        }
    }
    const char* ct = getenv("COLORTERM");
    if (!ct || (!strstr(ct, "truecolor") && !strstr(ct, "24bit"))) {
        const char* te = getenv("TERM");
        if (!te || !strstr(te, "256color")) g_truecolor = false;
    }

    EV.reserve(ky::N_EVENTS);
    for (int i = 0; i < ky::N_EVENTS; i++) {
        const auto& e = ky::EVENTS[i];
        EV.push_back({e.y, norm(e.t), norm(e.d), norm(e.lg), e.era, e.core});
        if (e.core) N_CORE++;
    }

    if (opt_list) {
        for (int i = 0; i < (int)EV.size(); i++)
            printf("%03d  %d  [%s]%s  %s\n", i + 1, EV[i].y, EV[i].era.c_str(),
                   EV[i].core ? "*" : " ", EV[i].t.c_str());
        return 0;
    }
    if (opt_dump >= 0) {  // 无终端预览
        int W = 100;
        buildDoc(W);
        for (int i = 0; i < (int)opt_dump && i < (int)doc.size(); i++)
            printf("%s\033[0m\n", doc[i].text.c_str());
        return 0;
    }
    if (!isatty(1)) {
        fprintf(stderr, "stdout 不是终端。调试请用 --dump N / --list\n");
        return 1;
    }

    g_tty = true;
    raw_on();
    {
        const char* s = "\033[?1049h\033[?25l\033[2J";
        (void)!::write(1, s, strlen(s));
    }
    Guard guard;
    signal(SIGWINCH, on_winch);
    signal(SIGINT, on_term);
    signal(SIGTERM, on_term);

    int W = 100, H = 30;
    term_size(W, H);
    if (W < 50 || H < 14) {
        fprintf(stderr, "终端太小（%dx%d），至少需要 50x14。\n", W, H);
        return 1;
    }
    buildDoc(W);
    makeStars(W, H);

    bool playing = !opt_wait, ended = false;
    static const double SPEEDS[] = {0.25, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0};
    int speedIdx = 2;
    for (int i = 0; i < 7; i++)
        if (SPEEDS[i] >= opt_speed) { speedIdx = i; break; }
    double speed = SPEEDS[speedIdx];
    double offset = 0;

    auto t0 = std::chrono::steady_clock::now();
    int tick = 0;
    Frame f;
    while (!g_quit) {
        if (g_resized) {
            g_resized = 0;
            int ow = W;
            term_size(W, H);
            if (W != ow) buildDoc(W);
            makeStars(W, H);
            const char* s = "\033[2J";
            (void)!::write(1, s, strlen(s));
        }
        auto now = std::chrono::steady_clock::now();
        double dt = std::chrono::duration<double>(now - t0).count();
        t0 = now;

        Act a;
        while ((a = readKeys()) != A_NONE) {
            switch (a) {
                case A_QUIT: g_quit = 1; break;
                case A_TOGGLE:
                    if (ended) { ended = false; offset = 0; playing = true; }
                    else playing = !playing;
                    break;
                case A_NEXT: offset += H / 2; break;
                case A_PREV: offset -= H / 2; break;
                case A_UP: offset -= 4; break;
                case A_DOWN: offset += 4; break;
                case A_FASTER: if (speedIdx < 6) speed = SPEEDS[++speedIdx]; break;
                case A_SLOWER: if (speedIdx > 0) speed = SPEEDS[--speedIdx]; break;
                case A_RESTART: ended = false; offset = 0; playing = true; break;
                default: break;
            }
            if (g_quit) break;
        }
        if (g_quit) break;

        if (playing && !ended) {
            offset += 1.3 * speed * dt;
            double maxOff = std::max(0.0, (double)doc.size() - (H - 6));
            if (offset >= maxOff) { offset = maxOff; playing = false; ended = true; }
        }
        if (offset < 0) offset = 0;

        f.begin(W, H);
        renderFrame(f, W, H, offset, playing, speed, ended, tick);
        f.finish();
        (void)!::write(1, f.out.data(), f.out.size());
        tick++;
        std::this_thread::sleep_for(std::chrono::milliseconds(28));  // ~33fps 上限
    }
    return 0;
}
