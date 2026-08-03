// CF 2223E - Zhily and Permutation
//
// ---------------------------------------------------------------------------
// next((l,r)) = (min(i,j), max(i,j)),  i = argmax a on (l,r), j = argmax b on (l,r).
// f((l,r),k) walks the chain for k intervals; interval (l,r) emits p[l] ones, or a
// single 0 when p[l]==0.  Answer = longest run of ones.
//
// FRAME TREE.  Split (0,n+1) at its two argmaxes u<v into (l,u),(u,v),(v,r) and
// recurse.  O(n) frames, laminar.  mc(F)=(u_F,v_F) is the "middle child"; following
// mc gives the "middle path", which is exactly the chain started at F.
// Every position is a split point of exactly one frame, so the deepest frame
// containing an interval is an LCA in the frame tree.
//
// Facts used (all verified by brute force on small cases):
//  1. after one step every chain interval shares an endpoint with its deepest
//     containing frame F  (L-state: l=L_F, u_F<r<=v_F;  R-state: r=R_F, u_F<=l<v_F);
//  2. an interval containing both argmaxes of F steps to mc(F) and then follows the
//     middle path forever  => one segment tree range query;
//  3. a chain interval contributes p[left endpoint]; along a middle path frame F
//     contributes p[u_F] and each position is the argmax of <=2 frames, so updating
//     p[x] touches O(1) leaves;
//  4. while a chain shadows a middle path (a "run"), the orientation (which of a/b
//     owns v_F) cannot change: at a flip the chain lands exactly on a frame;
//  5. inside a run the free endpoint moves as d -> argmax_Y[L_t+1, d-1].  If the
//     unconstrained value lc_Y(d) (Cartesian-tree child) stays inside the frame, the
//     move equals that child, so the whole run is a child-chain descent and its
//     length is found by binary lifting.  The extreme state (d = v_F) instead keeps
//     riding the frame boundary, which is precomputed per frame.
//     L-runs emit canonical values (middle path); R-runs emit p[] along a
//     right-child chain of a Cartesian tree -> segment trees over those chains.
// ---------------------------------------------------------------------------
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

// ------------------------------ fast input ------------------------------
static char ibuf[1 << 25];
static size_t ipos = 0, ilen = 0;
static inline int gc() {
    if (ipos == ilen) { ilen = fread(ibuf, 1, sizeof(ibuf), stdin); ipos = 0; if (!ilen) return -1; }
    return ibuf[ipos++];
}
static inline ll readInt() {
    int c = gc();
    while (c != -1 && (c < '0' || c > '9') && c != '-') c = gc();
    int sg = 1; if (c == '-') { sg = -1; c = gc(); }
    ll x = 0;
    while (c >= '0' && c <= '9') { x = x * 10 + (c - '0'); c = gc(); }
    return x * sg;
}

// -------------------- monoid: longest run of positives --------------------
struct Node { ll best, pre, suf, tot; bool allp; };
static const Node IDN = {0, 0, 0, 0, true};
static inline Node mergeN(const Node &L, const Node &R) {
    Node z;
    z.best = max(max(L.best, R.best), L.suf + R.pre);
    z.pre = L.allp ? L.tot + R.pre : L.pre;
    z.suf = R.allp ? R.tot + L.suf : R.suf;
    z.tot = L.tot + R.tot;
    z.allp = L.allp && R.allp;
    return z;
}
static inline Node mk(ll v) {
    if (v > 0) return Node{v, v, v, v, true};
    return Node{0, 0, 0, 0, false};
}

// a family of chains, each with its own iterative segment tree (ordered merges)
struct ChainForest {
    vector<int> off, sz;
    vector<Node> seg;
    void init(const vector<int> &lens) {
        int c = (int)lens.size();
        off.resize(c); sz.resize(c);
        size_t tot = 0;
        for (int i = 0; i < c; i++) {
            int s = 1; while (s < max(1, lens[i])) s <<= 1;
            sz[i] = s; off[i] = (int)tot; tot += 2 * (size_t)s;
        }
        seg.assign(tot, IDN);
    }
    inline void setLeaf(int c, int i, const Node &nd) { seg[off[c] + sz[c] + i] = nd; }
    void buildAll() {
        for (size_t c = 0; c < off.size(); c++) {
            int o = off[c], s = sz[c];
            for (int i = s - 1; i >= 1; i--) seg[o + i] = mergeN(seg[o + 2 * i], seg[o + 2 * i + 1]);
        }
    }
    inline void update(int c, int i, const Node &nd) {
        int o = off[c], s = sz[c], rel = s + i;
        seg[o + rel] = nd;
        for (rel >>= 1; rel >= 1; rel >>= 1) seg[o + rel] = mergeN(seg[o + 2 * rel], seg[o + 2 * rel + 1]);
    }
    inline Node query(int c, int lo, int hi) const {
        int o = off[c], s = sz[c];
        Node rl = IDN, rr = IDN;
        for (int l = lo + s, r = hi + s + 1; l < r; l >>= 1, r >>= 1) {
            if (l & 1) { rl = mergeN(rl, seg[o + l]); l++; }
            if (r & 1) { --r; rr = mergeN(seg[o + r], rr); }
        }
        return mergeN(rl, rr);
    }
};

static int n;
static vector<int> P[2];              // the two permutations, 1..n
static vector<int> lg2tab;
static vector<int> sp[2][18];         // sparse tables of argmax positions

static inline int betterP(int w, int x, int y) { return P[w][x] > P[w][y] ? x : y; }
static inline int qmax(int w, int x, int y) {
    int k = lg2tab[y - x + 1];
    return betterP(w, sp[w][k][x], sp[w][k][y - (1 << k) + 1]);
}

#ifdef COUNT_ITERS
long long g_iters = 0, g_cur = 0, g_max = 0;
#endif

int main() {
    int T = (int)readInt();
    string out; out.reserve(1 << 22);
    while (T--) {
        n = (int)readInt();
        int m = (int)readInt();
        for (int w = 0; w < 2; w++) {
            P[w].assign(n + 2, 0);
            for (int i = 1; i <= n; i++) P[w][i] = (int)readInt();
        }
        vector<ll> pv(n + 2, 0);
        for (int i = 0; i < n; i++) pv[i] = readInt();

        lg2tab.assign(n + 2, 0);
        for (int i = 2; i <= n + 1; i++) lg2tab[i] = lg2tab[i >> 1] + 1;
        int K = lg2tab[max(1, n)] + 1;
        for (int w = 0; w < 2; w++) {
            sp[w][0].assign(n + 2, 0);
            for (int i = 1; i <= n; i++) sp[w][0][i] = i;
            for (int k = 1; k < K; k++) {
                sp[w][k].assign(n + 2, 0);
                for (int i = 1; i + (1 << k) - 1 <= n; i++)
                    sp[w][k][i] = betterP(w, sp[w][k - 1][i], sp[w][k - 1][i + (1 << (k - 1))]);
            }
        }
        // prev/next greater, Cartesian tree children
        vector<int> pg[2], ng[2], lch[2], rch[2];
        for (int w = 0; w < 2; w++) {
            pg[w].assign(n + 2, 0); ng[w].assign(n + 2, n + 1);
            vector<int> stk;
            for (int i = 1; i <= n; i++) {
                while (!stk.empty() && P[w][stk.back()] < P[w][i]) { ng[w][stk.back()] = i; stk.pop_back(); }
                pg[w][i] = stk.empty() ? 0 : stk.back();
                stk.push_back(i);
            }
            lch[w].assign(n + 2, 0); rch[w].assign(n + 2, 0);
            for (int i = 1; i <= n; i++) {
                if (pg[w][i] + 1 <= i - 1) lch[w][i] = qmax(w, pg[w][i] + 1, i - 1);
                if (i + 1 <= ng[w][i] - 1) rch[w][i] = qmax(w, i + 1, ng[w][i] - 1);
            }
        }
        // binary lifting over left / right child chains
        int LOG = 1; while ((1 << LOG) <= n) LOG++;
        vector<vector<int>> LCJ[2], RCJ[2];
        for (int w = 0; w < 2; w++) {
            LCJ[w].assign(LOG, vector<int>(n + 2, 0));
            RCJ[w].assign(LOG, vector<int>(n + 2, 0));
            for (int i = 0; i <= n + 1; i++) { LCJ[w][0][i] = (i >= 1 && i <= n) ? lch[w][i] : 0; RCJ[w][0][i] = (i >= 1 && i <= n) ? rch[w][i] : 0; }
            for (int k = 1; k < LOG; k++)
                for (int i = 0; i <= n + 1; i++) {
                    LCJ[w][k][i] = LCJ[w][k - 1][LCJ[w][k - 1][i]];
                    RCJ[w][k][i] = RCJ[w][k - 1][RCJ[w][k - 1][i]];
                }
        }

        // ---------------- frames ----------------
        vector<int> fl, fr, fu, fv, fmc, fpar, fpath, fidx, fown;  // fown: 1 if b owns v_F else 0
        fl.reserve(n + 1);
        vector<char> isMc;
        {
            vector<array<int, 4>> st;
            st.push_back({0, n + 1, -1, 0});
            while (!st.empty()) {
                array<int, 4> cu = st.back(); st.pop_back();
                int l = cu[0], r = cu[1], par = cu[2], ismc = cu[3];
                if (l + 1 >= r) continue;
                int i = qmax(0, l + 1, r - 1), j = qmax(1, l + 1, r - 1);
                int u = min(i, j), v = max(i, j);
                int id = (int)fl.size();
                fl.push_back(l); fr.push_back(r); fu.push_back(u); fv.push_back(v);
                fmc.push_back(-1); fpar.push_back(par); fpath.push_back(-1); fidx.push_back(-1);
                fown.push_back(v == j ? 1 : 0);
                isMc.push_back((char)ismc);
                if (par >= 0 && ismc) fmc[par] = id;
                st.push_back({v, r, id, 0});
                st.push_back({u, v, id, 1});
                st.push_back({l, u, id, 0});
            }
        }
        int F = (int)fl.size();
        // owner frame of each position (the frame where it is a split point)
        vector<int> own(n + 2, -1);
        for (int i = 0; i < F; i++) { own[fu[i]] = i; own[fv[i]] = i; }
        // frame-tree LCA by binary lifting
        int FLOG = 1; while ((1 << FLOG) <= F + 1) FLOG++;
        vector<int> fdep(F, 0);
        vector<vector<int>> up(FLOG, vector<int>(F, -1));
        for (int i = 0; i < F; i++) {           // frames are created parent-before-child
            up[0][i] = fpar[i];
            fdep[i] = fpar[i] < 0 ? 0 : fdep[fpar[i]] + 1;
        }
        for (int k = 1; k < FLOG; k++)
            for (int i = 0; i < F; i++) { int q = up[k - 1][i]; up[k][i] = q < 0 ? -1 : up[k - 1][q]; }
        auto flca = [&](int x, int y) {
            if (fdep[x] < fdep[y]) swap(x, y);
            int d = fdep[x] - fdep[y];
            for (int k = 0; k < FLOG; k++) if (d >> k & 1) x = up[k][x];
            if (x == y) return x;
            for (int k = FLOG - 1; k >= 0; k--) if (up[k][x] != up[k][y]) { x = up[k][x]; y = up[k][y]; }
            return fpar[x];
        };

        // ---------------- middle paths ----------------
        vector<int> pstart, plen;               // flattened path storage
        vector<int> flatFid, flatU, flatV, flatBlk, flatMaxFail, flatMinFail;
        {
            vector<int> lens;
            for (int h = 0; h < F; h++) {
                if (isMc[h]) continue;
                int pid = (int)lens.size();
                int len = 0;
                pstart.push_back((int)flatFid.size());
                for (int c = h; c != -1; c = fmc[c]) {
                    fpath[c] = pid; fidx[c] = len; flatFid.push_back(c); len++;
                }
                lens.push_back(len); plen.push_back(len);
            }
            int total = (int)flatFid.size();
            flatU.resize(total); flatV.resize(total);
            flatBlk.resize(total); flatMaxFail.resize(total); flatMinFail.resize(total);
            for (int i = 0; i < total; i++) { flatU[i] = fu[flatFid[i]]; flatV[i] = fv[flatFid[i]]; }
            for (size_t pid = 0; pid < plen.size(); pid++) {
                int s0 = pstart[pid], len = plen[pid];
                for (int t = len - 1; t >= 0; t--) {
                    int id = flatFid[s0 + t];
                    bool last = (t == len - 1);
                    bool sameOr = !last && (fown[id] == fown[flatFid[s0 + t + 1]]);
                    flatBlk[s0 + t] = sameOr ? flatBlk[s0 + t + 1] : t;
                    // maximal L-state rides the boundary?
                    bool okMax = false, okMin = false;
                    if (!last && sameOr) {
                        int G = flatFid[s0 + t + 1];
                        if (fu[G] < fv[G]) {                    // successor must admit L/R states
                            int Y = fown[id];                   // owner of v
                            int X = Y ^ 1;                      // owner of u
                            if (fl[id] + 1 <= fv[id] - 1)
                                okMax = qmax(Y, fl[id] + 1, fv[id] - 1) > fu[id];
                            if (fu[id] + 1 <= fr[id] - 1)
                                okMin = qmax(X, fu[id] + 1, fr[id] - 1) < fv[id];
                        }
                    }
                    flatMaxFail[s0 + t] = okMax ? flatMaxFail[s0 + t + 1] : t;
                    flatMinFail[s0 + t] = okMin ? flatMinFail[s0 + t + 1] : t;
                }
            }
        }
        ChainForest midTree;
        {
            vector<int> lens = plen;
            midTree.init(lens);
            for (int i = 0; i < F; i++) midTree.setLeaf(fpath[i], fidx[i], mk(pv[fu[i]]));
            midTree.buildAll();
        }
        // frames whose u equals x (at most two)
        vector<array<int, 2>> occ(n + 2, {-1, -1});
        for (int i = 0; i < F; i++) {
            int x = fu[i];
            if (occ[x][0] < 0) occ[x][0] = i; else occ[x][1] = i;
        }
        // ---------------- right-child chains of both Cartesian trees ----------------
        ChainForest rcTree[2];
        vector<int> rcChain[2], rcPos[2];
        for (int w = 0; w < 2; w++) {
            rcChain[w].assign(n + 2, -1); rcPos[w].assign(n + 2, -1);
            vector<char> isRc(n + 2, 0);
            for (int i = 1; i <= n; i++) if (rch[w][i]) isRc[rch[w][i]] = 1;
            vector<int> lens;
            for (int i = 1; i <= n; i++) {
                if (isRc[i]) continue;
                int cid = (int)lens.size(), len = 0;
                for (int c = i; c; c = rch[w][c]) { rcChain[w][c] = cid; rcPos[w][c] = len++; }
                lens.push_back(len);
            }
            rcTree[w].init(lens);
            for (int i = 1; i <= n; i++) rcTree[w].setLeaf(rcChain[w][i], rcPos[w][i], mk(pv[i]));
            rcTree[w].buildAll();
        }

        // ---------------- (l,r) -> frame id hash ----------------
        int hs = 4; while (hs < 4 * (F + 1)) hs <<= 1;
        int hmask = hs - 1;
        vector<ll> hkey(hs, -1);
        vector<int> hvl(hs, -1);
        auto hmix = [](ll k) -> size_t {
            unsigned long long x = (unsigned long long)k * 0x9E3779B97F4A7C15ULL;
            x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32;
            return (size_t)x;
        };
        for (int i = 0; i < F; i++) {
            ll k = (ll)fl[i] * (n + 2) + fr[i];
            size_t t = hmix(k) & hmask;
            while (hkey[t] != -1) t = (t + 1) & hmask;
            hkey[t] = k; hvl[t] = i;
        }
        auto frameOf = [&](int l, int r) -> int {
            ll k = (ll)l * (n + 2) + r;
            size_t t = hmix(k) & hmask;
            while (hkey[t] != -1) { if (hkey[t] == k) return hvl[t]; t = (t + 1) & hmask; }
            return -1;
        };

        for (int q = 0; q < m; q++) {
            int tp = (int)readInt();
            if (tp == 2) {
                int x = (int)readInt(); ll y = readInt();
                pv[x] = y;
                Node nd = mk(y);
                if (occ[x][0] >= 0) midTree.update(fpath[occ[x][0]], fidx[occ[x][0]], nd);
                if (occ[x][1] >= 0) midTree.update(fpath[occ[x][1]], fidx[occ[x][1]], nd);
                if (x >= 1 && x <= n) {
                    rcTree[0].update(rcChain[0][x], rcPos[0][x], nd);
                    rcTree[1].update(rcChain[1][x], rcPos[1][x], nd);
                }
                continue;
            }
            int l = (int)readInt(), r = (int)readInt(), k = (int)readInt();
            Node acc = IDN;
            int cl = l, cr = r, steps = k;
            while (steps > 0 && cl + 1 < cr) {
#ifdef COUNT_ITERS
                g_iters++; g_cur++;
#endif
                int fid = frameOf(cl, cr);
                if (fid >= 0) {                    // canonical: chain = middle path suffix
                    acc = mergeN(acc, mk(pv[cl]));
                    int pid = fpath[fid], s = fidx[fid];
                    int avail = plen[pid] - s;      // states from s to the path's end
                    int cnt = min(steps, avail);
                    if (cnt >= 2) acc = mergeN(acc, midTree.query(pid, s, s + cnt - 2));
                    steps = 0;
                    break;
                }
                int hf = flca(own[cl + 1], own[cr - 1]);
                int L = fl[hf], R = fr[hf], u = fu[hf], v = fv[hf];
                bool handled = false;
                if (cl < u && cr > v) {            // contains both argmaxes
                    acc = mergeN(acc, mk(pv[cl])); steps--;
                    cl = u; cr = v; handled = true;
                } else if (cl == L && cr > u && cr <= v) {          // L-state
                    int pid = fpath[hf], s = fidx[hf], s0 = pstart[pid];
                    int e = s, endx = cr;
                    if (cr == v) {
                        e = flatMaxFail[s0 + s];
                        endx = -1;                 // maximal: d_t = v_{F_t}
                    } else {
                        int Y = fown[hf];
                        if (pg[Y][cr] <= L) {
                            int lim = flatBlk[s0 + s], cur = cr;
                            for (int kk = LOG - 1; kk >= 0; kk--) {
                                int nt = e + (1 << kk);
                                if (nt > lim) continue;
                                int nx = LCJ[Y][kk][cur];
                                if (nx > 0 && nx > flatU[s0 + nt]) { e = nt; cur = nx; }
                            }
                            endx = cur;
                        }
                    }
                    int cnt = min(steps, e - s + 1);
                    acc = mergeN(acc, mk(pv[L]));
                    if (cnt >= 2) acc = mergeN(acc, midTree.query(pid, s, s + cnt - 2));
                    steps -= cnt;
                    if (steps > 0) {
                        int t = s + cnt - 1, tid = flatFid[s0 + t];
                        int dt;
                        if (endx < 0) dt = fv[tid];
                        else if (t == s) dt = cr;
                        else {
                            int Y = fown[hf], cur = cr, rem = t - s;
                            for (int kk = 0; rem; kk++, rem >>= 1) if (rem & 1) cur = LCJ[Y][kk][cur];
                            dt = cur;
                        }
                        int nl = fl[tid], nr = dt;
                        int i2 = qmax(0, nl + 1, nr - 1), j2 = qmax(1, nl + 1, nr - 1);
                        cl = min(i2, j2); cr = max(i2, j2);
                    }
                    handled = true;
                } else if (cr == R && cl >= u && cl < v) {          // R-state
                    int pid = fpath[hf], s = fidx[hf], s0 = pstart[pid];
                    int e = s, endc = cl;
                    bool minimal = (cl == u);
                    if (minimal) {
                        e = flatMinFail[s0 + s];
                        endc = -1;
                    } else {
                        int X = fown[hf] ^ 1;
                        if (ng[X][cl] >= R) {
                            int lim = flatBlk[s0 + s], cur = cl;
                            for (int kk = LOG - 1; kk >= 0; kk--) {
                                int nt = e + (1 << kk);
                                if (nt > lim) continue;
                                int nx = RCJ[X][kk][cur];
                                if (nx > 0 && nx < flatV[s0 + nt]) { e = nt; cur = nx; }
                            }
                            endc = cur;
                        }
                    }
                    int cnt = min(steps, e - s + 1);
                    if (minimal) {
                        acc = mergeN(acc, midTree.query(pid, s, s + cnt - 1));
                    } else {
                        int X = fown[hf] ^ 1;
                        acc = mergeN(acc, rcTree[X].query(rcChain[X][cl], rcPos[X][cl], rcPos[X][cl] + cnt - 1));
                    }
                    steps -= cnt;
                    if (steps > 0) {
                        int t = s + cnt - 1, tid = flatFid[s0 + t];
                        int ct;
                        if (minimal) ct = fu[tid];
                        else if (t == s) ct = cl;
                        else {
                            int X = fown[hf] ^ 1, cur = cl, rem = t - s;
                            for (int kk = 0; rem; kk++, rem >>= 1) if (rem & 1) cur = RCJ[X][kk][cur];
                            ct = cur;
                        }
                        int nl = ct, nr = fr[tid];
                        int i2 = qmax(0, nl + 1, nr - 1), j2 = qmax(1, nl + 1, nr - 1);
                        cl = min(i2, j2); cr = max(i2, j2);
                    }
                    handled = true;
                }
                if (!handled) {                    // generic single step
                    acc = mergeN(acc, mk(pv[cl])); steps--;
                    int i2 = qmax(0, cl + 1, cr - 1), j2 = qmax(1, cl + 1, cr - 1);
                    cl = min(i2, j2); cr = max(i2, j2);
                }
            }
#ifdef COUNT_ITERS
            if (g_cur > g_max) g_max = g_cur;
            g_cur = 0;
#endif
            out += to_string(acc.best);
            out += '\n';
        }
    }
    fwrite(out.data(), 1, out.size(), stdout);
#ifdef COUNT_ITERS
    fprintf(stderr, "iters=%lld max=%lld\n", g_iters, g_max);
#endif
    return 0;
}
