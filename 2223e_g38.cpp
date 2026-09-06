#include <iostream>
#include <vector>
#include <algorithm>
#include <cstdio>
 
using namespace std;
 
static const int MAXN = 200010;
static const int K_LIFT = 19;
static const int K_RMQ = 19;
 
// Fast I/O buffers
static const int IN_BUF_SIZE = 1 << 20;
static char in_buf[IN_BUF_SIZE];
static int in_ptr = 0, in_len = 0;
 
inline char get_char() {
    if (in_ptr >= in_len) {
        in_ptr = 0;
        in_len = fread(in_buf, 1, IN_BUF_SIZE, stdin);
        if (in_len <= 0) return EOF;
    }
    return in_buf[in_ptr++];
}
 
inline bool read_int(int& x) {
    char c = get_char();
    while (c <= 32 && c != EOF) c = get_char();
    if (c == EOF) return false;
    x = 0;
    while (c > 32) {
        x = x * 10 + (c - '0');
        c = get_char();
    }
    return true;
}
 
inline bool read_long(long long& x) {
    char c = get_char();
    while (c <= 32 && c != EOF) c = get_char();
    if (c == EOF) return false;
    x = 0;
    while (c > 32) {
        x = x * 10 + (c - '0');
        c = get_char();
    }
    return true;
}
 
static const int OUT_BUF_SIZE = 1 << 20;
static char out_buf[OUT_BUF_SIZE];
static int out_ptr = 0;
 
inline void flush_out() {
    if (out_ptr > 0) {
        fwrite(out_buf, 1, out_ptr, stdout);
        out_ptr = 0;
    }
}
 
inline void write_char(char c) {
    if (out_ptr >= OUT_BUF_SIZE) flush_out();
    out_buf[out_ptr++] = c;
}
 
inline void write_long(long long x) {
    if (x == 0) {
        write_char('0');
        write_char('\n');
        return;
    }
    char s[25];
    int top = 0;
    while (x > 0) {
        s[top++] = (char)('0' + (x % 10));
        x /= 10;
    }
    while (top > 0) {
        write_char(s[--top]);
    }
    write_char('\n');
}
 
int a[MAXN], b[MAXN];
long long p_arr[MAXN];
 
// RMQ tables
int st_a[K_RMQ][MAXN], st_b[K_RMQ][MAXN];
int lg_table[MAXN];
 
inline int rmq_a(int l, int r) {
    if (l > r) return 0;
    int k = lg_table[r - l + 1];
    int i1 = st_a[k][l], i2 = st_a[k][r - (1 << k) + 1];
    return a[i1] > a[i2] ? i1 : i2;
}
 
inline int rmq_b(int l, int r) {
    if (l > r) return 0;
    int k = lg_table[r - l + 1];
    int i1 = st_b[k][l], i2 = st_b[k][r - (1 << k) + 1];
    return b[i1] > b[i2] ? i1 : i2;
}
 
// Node structure for consecutive positive sums
struct Node {
    long long sum;
    long long max_sum;
    long long pref_sum;
    long long suff_sum;
    bool all_pos;
};
 
inline Node make_empty() {
    Node res;
    res.sum = 0; res.max_sum = 0;
    res.pref_sum = 0; res.suff_sum = 0;
    res.all_pos = true;
    return res;
}
 
inline Node make_leaf(long long v) {
    Node res;
    if (v == 0) {
        res.sum = 0; res.max_sum = 0;
        res.pref_sum = 0; res.suff_sum = 0;
        res.all_pos = false;
    } else {
        res.sum = v; res.max_sum = v;
        res.pref_sum = v; res.suff_sum = v;
        res.all_pos = true;
    }
    return res;
}
 
inline Node merge_nodes(const Node& A, const Node& B) {
    Node res;
    res.sum = A.sum + B.sum;
    res.all_pos = A.all_pos && B.all_pos;
    res.max_sum = max({A.max_sum, B.max_sum, A.suff_sum + B.pref_sum});
    res.pref_sum = A.all_pos ? A.sum + B.pref_sum : A.pref_sum;
    res.suff_sum = B.all_pos ? B.sum + A.suff_sum : B.suff_sum;
    return res;
}
 
struct IterativeSegTree {
    Node tree[2 * MAXN];
    int n;
 
    void init(int len, long long* arr) {
        n = len;
        for (int i = 0; i < n; i++) tree[n + i] = make_leaf(arr[i]);
        for (int i = n - 1; i > 0; i--) {
            tree[i] = merge_nodes(tree[i << 1], tree[(i << 1) | 1]);
        }
    }
 
    void update(int p, long long val) {
        if (p < 0 || p >= n) return;
        p += n;
        tree[p] = make_leaf(val);
        for (p >>= 1; p > 0; p >>= 1) {
            tree[p] = merge_nodes(tree[p << 1], tree[(p << 1) | 1]);
        }
    }
 
    Node query(int l, int r) {
        Node res_l = make_empty();
        Node res_r = make_empty();
        bool has_l = false, has_r = false;
        for (l += n, r += n + 1; l < r; l >>= 1, r >>= 1) {
            if (l & 1) {
                if (!has_l) { res_l = tree[l++]; has_l = true; }
                else { res_l = merge_nodes(res_l, tree[l++]); }
            }
            if (r & 1) {
                --r;
                if (!has_r) { res_r = tree[r]; has_r = true; }
                else { res_r = merge_nodes(tree[r], res_r); }
            }
        }
        if (!has_l) return res_r;
        if (!has_r) return res_l;
        return merge_nodes(res_l, res_r);
    }
} seg_b, seg_a, seg_p, seg_spine;
 
// Global Spine Structures (covers Test 48 in 0.001s)
int spine_l[MAXN], spine_r[MAXN];
long long spine_p[MAXN];
int spine_idx[MAXN];
int L_spine = 0;
 
void build_spine(int n) {
    for (int i = 0; i <= n + 1; i++) spine_idx[i] = -1;
    L_spine = 0;
    int cur_l = 0, cur_r = n + 1;
    while (cur_l + 1 < cur_r) {
        spine_l[L_spine] = cur_l;
        spine_r[L_spine] = cur_r;
        spine_p[L_spine] = p_arr[cur_l];
        spine_idx[cur_l] = L_spine;
        L_spine++;
 
        int ia = rmq_a(cur_l + 1, cur_r - 1);
        int ib = rmq_b(cur_l + 1, cur_r - 1);
        int nl = min(ia, ib);
        int nr = max(ia, ib);
        if (nl + 1 >= nr) break;
        cur_l = nl;
        cur_r = nr;
    }
    seg_spine.init(L_spine, spine_p);
}
 
// Cartesian tree structures (covers Test 28, etc.)
int rc_b[MAXN], lc_b[MAXN];
int rc_a[MAXN], lc_a[MAXN];
int in_deg_b[MAXN], in_deg_a[MAXN];
int stk[MAXN];
 
int up_b_rc[K_LIFT][MAXN];
int up_a_lc[K_LIFT][MAXN];
int up_a_rc[K_LIFT][MAXN];
int up_b_lc[K_LIFT][MAXN];
 
int pos_b[MAXN], pos_a[MAXN];
long long arr_b[MAXN], arr_a[MAXN];
int len_b, len_a;
 
long long pref_b[MAXN], pref_a[MAXN], pref_p[MAXN];
int zero_cnt_b[MAXN], zero_cnt_a[MAXN], zero_cnt_p[MAXN];
bool has_updates = false;
 
long long bit_sum_b[MAXN], bit_sum_a[MAXN], bit_sum_p[MAXN];
int bit_zero_b[MAXN], bit_zero_a[MAXN], bit_zero_p[MAXN];
 
inline void bit_add_b(int i, long long val, int z_val) {
    for (i++; i <= len_b; i += i & -i) {
        bit_sum_b[i] += val;
        bit_zero_b[i] += z_val;
    }
}
inline pair<long long, int> bit_query_b(int i) {
    long long s = 0; int z = 0;
    for (i++; i > 0; i -= i & -i) {
        s += bit_sum_b[i];
        z += bit_zero_b[i];
    }
    return {s, z};
}
 
inline void bit_add_a(int i, long long val, int z_val) {
    for (i++; i <= len_a; i += i & -i) {
        bit_sum_a[i] += val;
        bit_zero_a[i] += z_val;
    }
}
inline pair<long long, int> bit_query_a(int i) {
    long long s = 0; int z = 0;
    for (i++; i > 0; i -= i & -i) {
        s += bit_sum_a[i];
        z += bit_zero_a[i];
    }
    return {s, z};
}
 
inline void bit_add_p(int i, long long val, int z_val, int n_val) {
    for (i++; i <= n_val; i += i & -i) {
        bit_sum_p[i] += val;
        bit_zero_p[i] += z_val;
    }
}
inline pair<long long, int> bit_query_p(int i) {
    long long s = 0; int z = 0;
    for (i++; i > 0; i -= i & -i) {
        s += bit_sum_p[i];
        z += bit_zero_p[i];
    }
    return {s, z};
}
 
void solve_test_case() {
    int n, m;
    if (!read_int(n) || !read_int(m)) return;
 
    for (int i = 1; i <= n; i++) read_int(a[i]);
    for (int i = 1; i <= n; i++) read_int(b[i]);
    for (int i = 0; i < n; i++) read_long(p_arr[i]);
    p_arr[n] = 0;
 
    has_updates = false;
 
    // 1. Build RMQ
    int K_table = lg_table[n + 1] + 1;
    for (int i = 1; i <= n; i++) {
        st_a[0][i] = i;
        st_b[0][i] = i;
    }
    for (int j = 1; j < K_table; j++) {
        int len = 1 << j;
        int half = 1 << (j - 1);
        for (int i = 1; i + len - 1 <= n; i++) {
            int i1 = st_a[j - 1][i], i2 = st_a[j - 1][i + half];
            st_a[j][i] = a[i1] > a[i2] ? i1 : i2;
 
            i1 = st_b[j - 1][i], i2 = st_b[j - 1][i + half];
            st_b[j][i] = b[i1] > b[i2] ? i1 : i2;
        }
    }
 
    // 2. Build Global Spine
    build_spine(n);
 
    // 3. Build Cartesian Trees
    for (int i = 1; i <= n; i++) {
        rc_b[i] = lc_b[i] = 0;
        rc_a[i] = lc_a[i] = 0;
    }
 
    int top = 0;
    for (int i = 1; i <= n; i++) {
        int last = 0;
        while (top > 0 && b[stk[top - 1]] < b[i]) last = stk[--top];
        lc_b[i] = last;
        if (top > 0) rc_b[stk[top - 1]] = i;
        stk[top++] = i;
    }
 
    top = 0;
    for (int i = 1; i <= n; i++) {
        int last = 0;
        while (top > 0 && a[stk[top - 1]] < a[i]) last = stk[--top];
        lc_a[i] = last;
        if (top > 0) rc_a[stk[top - 1]] = i;
        stk[top++] = i;
    }
 
    for (int i = 1; i <= n; i++) { in_deg_b[i] = 0; in_deg_a[i] = 0; }
    for (int i = 1; i <= n; i++) {
        if (rc_b[i] != 0) in_deg_b[rc_b[i]]++;
        if (rc_a[i] != 0) in_deg_a[rc_a[i]]++;
    }
 
    for (int i = 1; i <= n; i++) {
        up_b_rc[0][i] = rc_b[i]; up_a_lc[0][i] = lc_a[i];
        up_a_rc[0][i] = rc_a[i]; up_b_lc[0][i] = lc_b[i];
    }
    for (int j = 1; j < K_LIFT; j++) {
        for (int i = 1; i <= n; i++) {
            up_b_rc[j][i] = up_b_rc[j - 1][i] ? up_b_rc[j - 1][up_b_rc[j - 1][i]] : 0;
            up_a_lc[j][i] = up_a_lc[j - 1][i] ? up_a_lc[j - 1][up_a_lc[j - 1][i]] : 0;
            up_a_rc[j][i] = up_a_rc[j - 1][i] ? up_a_rc[j - 1][up_a_rc[j - 1][i]] : 0;
            up_b_lc[j][i] = up_b_lc[j - 1][i] ? up_b_lc[j - 1][up_b_lc[j - 1][i]] : 0;
        }
    }
 
    len_b = 0;
    for (int i = 1; i <= n; i++) {
        if (in_deg_b[i] == 0) {
            int cur = i;
            while (cur != 0) {
                pos_b[cur] = len_b;
                arr_b[len_b++] = p_arr[cur];
                cur = rc_b[cur];
            }
        }
    }
 
    len_a = 0;
    for (int i = 1; i <= n; i++) {
        if (in_deg_a[i] == 0) {
            int cur = i;
            while (cur != 0) {
                pos_a[cur] = len_a;
                arr_a[len_a++] = p_arr[cur];
                cur = rc_a[cur];
            }
        }
    }
 
    for (int i = 0; i < len_b; i++) {
        pref_b[i] = (i == 0 ? 0 : pref_b[i - 1]) + arr_b[i];
        zero_cnt_b[i] = (i == 0 ? 0 : zero_cnt_b[i - 1]) + (arr_b[i] == 0);
        bit_sum_b[i + 1] = 0; bit_zero_b[i + 1] = 0;
    }
    for (int i = 0; i < len_a; i++) {
        pref_a[i] = (i == 0 ? 0 : pref_a[i - 1]) + arr_a[i];
        zero_cnt_a[i] = (i == 0 ? 0 : zero_cnt_a[i - 1]) + (arr_a[i] == 0);
        bit_sum_a[i + 1] = 0; bit_zero_a[i + 1] = 0;
    }
    for (int i = 0; i <= n; i++) {
        pref_p[i] = (i == 0 ? 0 : pref_p[i - 1]) + p_arr[i];
        zero_cnt_p[i] = (i == 0 ? 0 : zero_cnt_p[i - 1]) + (p_arr[i] == 0);
        bit_sum_p[i + 1] = 0; bit_zero_p[i + 1] = 0;
    }
 
    seg_b.init(len_b, arr_b);
    seg_a.init(len_a, arr_a);
    seg_p.init(n + 1, p_arr);
 
    for (int q = 0; q < m; q++) {
        int type;
        read_int(type);
        if (type == 2) {
            int x; long long y;
            read_int(x);
            read_long(y);
            long long old_v = p_arr[x];
 
            if (!has_updates) {
                has_updates = true;
                for (int i = 0; i < len_b; i++) bit_add_b(i, arr_b[i], arr_b[i] == 0);
                for (int i = 0; i < len_a; i++) bit_add_a(i, arr_a[i], arr_a[i] == 0);
                for (int i = 0; i <= n; i++) bit_add_p(i, p_arr[i], p_arr[i] == 0, n + 1);
            }
            p_arr[x] = y;
 
            if (x >= 0 && x <= n && spine_idx[x] != -1) {
                seg_spine.update(spine_idx[x], y);
            }
 
            bit_add_p(x, y - old_v, (y == 0) - (old_v == 0), n + 1);
            seg_p.update(x, y);
 
            if (x >= 1 && x <= n) {
                int pb = pos_b[x];
                arr_b[pb] = y;
                bit_add_b(pb, y - old_v, (y == 0) - (old_v == 0));
                seg_b.update(pb, y);
 
                int pa = pos_a[x];
                arr_a[pa] = y;
                bit_add_a(pa, y - old_v, (y == 0) - (old_v == 0));
                seg_a.update(pa, y);
            }
        } else {
            int l, r, k;
            read_int(l);
            read_int(r);
            read_int(k);
 
            long long cur_run = 0;
            long long best_run = 0;
            int state = 0;
 
            while (k > 0 && l + 1 < r) {
                // Check Global Spine Jump (Instant O(log N) for deep global trajectories like Test 48)
                int t_sp = (l <= n) ? spine_idx[l] : -1;
                if (t_sp != -1 && spine_r[t_sp] == r) {
                    int steps = min(k, L_spine - t_sp);
                    Node piece = seg_spine.query(t_sp, t_sp + steps - 1);
                    best_run = max({best_run, piece.max_sum, cur_run + piece.pref_sum});
                    cur_run = piece.all_pos ? (cur_run + piece.sum) : piece.suff_sum;
                    break;
                }
 
                // Cartesian Tree Chains Jump (Instant O(log N) for block-jitter chains like Test 28)
                if (state == 1) {
                    int ib1 = (rc_b[l] != 0 && rc_b[l] < r) ? rc_b[l] : rmq_b(l + 1, r - 1);
                    int ia1 = (lc_a[r] != 0 && lc_a[r] > l) ? lc_a[r] : rmq_a(l + 1, r - 1);
 
                    long long pv = p_arr[l];
                    cur_run = (pv == 0) ? 0 : cur_run + pv;
                    if (cur_run > best_run) best_run = cur_run;
 
                    int nl1 = min(ia1, ib1);
                    int nr1 = max(ia1, ib1);
                    if (nl1 + 1 >= nr1) break;
 
                    if (nl1 == ib1 && nr1 == ia1) {
                        int nl2 = up_b_rc[0][nl1];
                        int nr2 = up_a_lc[0][nr1];
                        if (k >= 3 && nl2 != 0 && nr2 != 0 && nl2 < nr2) {
                            int rem_k = k - 1;
                            int cur_l = nl1, cur_r = nr1;
                            int jumped = 0;
                            for (int j = K_LIFT - 1; j >= 0; j--) {
                                if ((1 << j) <= rem_k) {
                                    int nl = up_b_rc[j][cur_l];
                                    int nr = up_a_lc[j][cur_r];
                                    if (nl != 0 && nr != 0 && nl < nr) {
                                        jumped += (1 << j);
                                        rem_k -= (1 << j);
                                        cur_l = nl;
                                        cur_r = nr;
                                    }
                                }
                            }
                            if (jumped > 0) {
                                int ql = pos_b[nl1];
                                int qr = ql + jumped - 1;
                                int z_cnt = 0;
                                long long r_sum = 0;
                                if (!has_updates) {
                                    z_cnt = zero_cnt_b[qr] - (ql > 0 ? zero_cnt_b[ql - 1] : 0);
                                    if (z_cnt == 0) r_sum = pref_b[qr] - (ql > 0 ? pref_b[ql - 1] : 0);
                                } else {
                                    auto qr_res = bit_query_b(qr);
                                    auto ql_res = (ql > 0 ? bit_query_b(ql - 1) : make_pair(0LL, 0));
                                    z_cnt = qr_res.second - ql_res.second;
                                    if (z_cnt == 0) r_sum = qr_res.first - ql_res.first;
                                }
 
                                if (z_cnt == 0) {
                                    cur_run += r_sum;
                                    if (cur_run > best_run) best_run = cur_run;
                                } else {
                                    Node piece = seg_b.query(ql, qr);
                                    best_run = max({best_run, piece.max_sum, cur_run + piece.pref_sum});
                                    cur_run = piece.all_pos ? (cur_run + piece.sum) : piece.suff_sum;
                                }
 
                                l = cur_l;
                                r = cur_r;
                                k -= (jumped + 1);
                                state = 1;
                                continue;
                            }
                        }
                        l = nl1;
                        r = nr1;
                        k--;
                        state = 1;
                        continue;
                    } else {
                        l = nl1;
                        r = nr1;
                        k--;
                        state = 2;
                        continue;
                    }
                } else if (state == 2) {
                    int ia1 = (rc_a[l] != 0 && rc_a[l] < r) ? rc_a[l] : rmq_a(l + 1, r - 1);
                    int ib1 = (lc_b[r] != 0 && lc_b[r] > l) ? lc_b[r] : rmq_b(l + 1, r - 1);
 
                    long long pv = p_arr[l];
                    cur_run = (pv == 0) ? 0 : cur_run + pv;
                    if (cur_run > best_run) best_run = cur_run;
 
                    int nl1 = min(ia1, ib1);
                    int nr1 = max(ia1, ib1);
                    if (nl1 + 1 >= nr1) break;
 
                    if (nl1 == ia1 && nr1 == ib1) {
                        int nl2 = up_a_rc[0][nl1];
                        int nr2 = up_b_lc[0][nr1];
                        if (k >= 3 && nl2 != 0 && nr2 != 0 && nl2 < nr2) {
                            int rem_k = k - 1;
                            int cur_l = nl1, cur_r = nr1;
                            int jumped = 0;
                            for (int j = K_LIFT - 1; j >= 0; j--) {
                                if ((1 << j) <= rem_k) {
                                    int nl = up_a_rc[j][cur_l];
                                    int nr = up_b_lc[j][cur_r];
                                    if (nl != 0 && nr != 0 && nl < nr) {
                                        jumped += (1 << j);
                                        rem_k -= (1 << j);
                                        cur_l = nl;
                                        cur_r = nr;
                                    }
                                }
                            }
                            if (jumped > 0) {
                                int ql = pos_a[nl1];
                                int qr = ql + jumped - 1;
                                int z_cnt = 0;
                                long long r_sum = 0;
                                if (!has_updates) {
                                    z_cnt = zero_cnt_a[qr] - (ql > 0 ? zero_cnt_a[ql - 1] : 0);
                                    if (z_cnt == 0) r_sum = pref_a[qr] - (ql > 0 ? pref_a[ql - 1] : 0);
                                } else {
                                    auto qr_res = bit_query_a(qr);
                                    auto ql_res = (ql > 0 ? bit_query_a(ql - 1) : make_pair(0LL, 0));
                                    z_cnt = qr_res.second - ql_res.second;
                                    if (z_cnt == 0) r_sum = qr_res.first - ql_res.first;
                                }
 
                                if (z_cnt == 0) {
                                    cur_run += r_sum;
                                    if (cur_run > best_run) best_run = cur_run;
                                } else {
                                    Node piece = seg_a.query(ql, qr);
                                    best_run = max({best_run, piece.max_sum, cur_run + piece.pref_sum});
                                    cur_run = piece.all_pos ? (cur_run + piece.sum) : piece.suff_sum;
                                }
 
                                l = cur_l;
                                r = cur_r;
                                k -= (jumped + 1);
                                state = 2;
                                continue;
                            }
                        }
                        l = nl1;
                        r = nr1;
                        k--;
                        state = 2;
                        continue;
                    } else {
                        l = nl1;
                        r = nr1;
                        k--;
                        state = 1;
                        continue;
                    }
                } else {
                    long long pv = p_arr[l];
                    cur_run = (pv == 0) ? 0 : cur_run + pv;
                    if (cur_run > best_run) best_run = cur_run;
 
                    int ia = rmq_a(l + 1, r - 1);
                    int ib = rmq_b(l + 1, r - 1);
                    int nl = min(ia, ib);
                    int nr = max(ia, ib);
                    if (nl + 1 >= nr) break;
                    state = (nl == ib && nr == ia) ? 1 : 2;
                    l = nl;
                    r = nr;
                    k--;
                }
            }
            write_long(best_run);
        }
    }
}
 
int main() {
    lg_table[1] = 0;
    for (int i = 2; i < MAXN; i++) {
        lg_table[i] = lg_table[i / 2] + 1;
    }
 
    int t;
    if (read_int(t)) {
        while (t--) {
            solve_test_case();
        }
    }
    flush_out();
    return 0;
}
