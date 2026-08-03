// CF 1578C - Cactus Lady and her Cing
// 2 x 400001 ladder embedding of a cactus.  See DERIVATION.md for the
// structure theorem this is built on.  O(n) total.

#include <cstdio>
#include <vector>
#include <algorithm>
#include <utility>
#include <pthread.h>
using namespace std;

static int n, m;
static vector<int> EU, EV;
static vector<vector<pair<int,int> > > adj;   // (neighbour, edge id)
static vector<int> degv;
static vector<char> isCycE;                   // edge lies on a cycle
static vector<int> cycIdOf, cycPosOf;         // -1 if not on a cycle
static vector<vector<int> > cycArr;           // cyclic vertex order per cycle
static vector<vector<int> > cycPend;          // positions carrying pendants
static vector<vector<int> > ncNbr;            // neighbours via bridge edges
static vector<int> chIdOf, chIdxOf;           // "chain" = deg-2 non-cycle run
static vector<vector<int> > chArr;
static vector<signed char> Fm, Pm;            // memo: F / isPath  (-1 unknown)
static vector<int> Pl;                        // path length
static vector<int> RX, RY;                    // answer coordinates

static inline int oth(int e, int v) { return EU[e] == v ? EV[e] : EU[e]; }
static inline int did(int e, int v) { return 2 * e + (EU[e] == v ? 0 : 1); }
static inline int findE(int a, int b) {
    for (size_t i = 0; i < adj[a].size(); ++i)
        if (adj[a][i].first == b) return adj[a][i].second;
    return -1;
}
static inline bool onCyc(int v) { return cycIdOf[v] >= 0; }
static inline bool isChain(int v) { return degv[v] == 2 && !onCyc(v); }

// ---------------------------------------------------------------- isPath ----
// comp(u) in G - e is a simple path having u as one of its endpoints.
static void pathCompute(int e, int u) {
    int d = did(e, u);
    if (Pm[d] >= 0) return;
    Pm[d] = 0; Pl[d] = 0;
    if (onCyc(u)) return;
    int cnt = 0, z = -1, ez = -1;
    for (size_t i = 0; i < adj[u].size(); ++i)
        if (adj[u][i].second != e) { ++cnt; z = adj[u][i].first; ez = adj[u][i].second; }
    if (cnt > 1) return;
    if (cnt == 0) { Pm[d] = 1; Pl[d] = 1; return; }
    pathCompute(ez, z);
    int d2 = did(ez, z);
    if (Pm[d2]) { Pm[d] = 1; Pl[d] = 1 + Pl[d2]; }
}
static inline bool pathOK(int e, int u) { pathCompute(e, u); return Pm[did(e, u)] == 1; }
static inline int  pathLen(int e, int u) { pathCompute(e, u); return Pl[did(e, u)]; }

// ----------------------------------------------------------------- chains ---
struct Run { int cnt, last, nxt, c, i, dir; };

// b must be a chain vertex; walk away from the other endpoint of e.
static Run chainRun(int e, int b) {
    int a = oth(e, b);
    int c = chIdOf[b], i = chIdxOf[b], sz = (int)chArr[c].size();
    int dir;
    if (i > 0 && chArr[c][i - 1] == a)            dir = 1;
    else if (i + 1 < sz && chArr[c][i + 1] == a)  dir = -1;
    else if (sz == 1)                             dir = 1;
    else if (i == 0)                              dir = 1;
    else                                          dir = -1;
    int cnt = (dir == 1) ? (sz - i) : (i + 1);
    int last = chArr[c][i + dir * (cnt - 1)];
    int prevV = (cnt >= 2) ? chArr[c][i + dir * (cnt - 2)] : a;
    int nxt = -1;
    for (size_t t = 0; t < adj[last].size(); ++t)
        if (adj[last][t].first != prevV) nxt = adj[last][t].first;
    Run r; r.cnt = cnt; r.last = last; r.nxt = nxt; r.c = c; r.i = i; r.dir = dir;
    return r;
}

// -------------------------------------------------------------- predicates --
static bool F(int e, int u);
static bool RightFromCap(int x, int y, int eXY, int exX, int exY);
static bool CaseC(int x0, int eid0);

// arm of length L in one row, then a bridge into a fresh full half-strip
static bool ContAt(int e, int y, int L) {
    if (L < 1 || !isChain(y)) return false;
    Run r = chainRun(e, y);
    if (L > r.cnt) return false;
    int zl, zl1;
    if (L == r.cnt) { zl = r.last; zl1 = r.nxt; }
    else { zl = chArr[r.c][r.i + r.dir * (L - 1)]; zl1 = chArr[r.c][r.i + r.dir * L]; }
    if (zl1 < 0) return false;
    int e2 = findE(zl, zl1);
    if (e2 < 0) return false;
    return F(e2, zl1);
}

// two arms leaving a fully occupied column, row0 -> A, row1 -> B
static bool PairArms(int eA, int A, int eB, int B) {
    if (A < 0 && B < 0) return true;
    if (B < 0) return F(eA, A);
    if (A < 0) return F(eB, B);
    if (pathOK(eA, A)) {
        int L = pathLen(eA, A);
        if (pathOK(eB, B) && pathLen(eB, B) == L) return true;
        if (ContAt(eB, B, L)) return true;
    }
    if (pathOK(eB, B)) {
        int L = pathLen(eB, B);
        if (pathOK(eA, A) && pathLen(eA, A) == L) return true;
        if (ContAt(eA, A, L)) return true;
    }
    return false;
}

// x at (0,c), y at (1,c), edge x-y is the vertical there.  exX / exY are the
// already-used left neighbours (-1 when column c is the leftmost one).
static bool RightFromCap(int x, int y, int eXY, int exX, int exY) {
    if (!isCycE[eXY]) {
        int A = -1, eA = -1, cA = 0, B = -1, eB = -1, cB = 0;
        for (size_t i = 0; i < adj[x].size(); ++i)
            if (adj[x][i].second != eXY && adj[x][i].first != exX)
                { ++cA; A = adj[x][i].first; eA = adj[x][i].second; }
        if (cA > 1) return false;
        for (size_t i = 0; i < adj[y].size(); ++i)
            if (adj[y][i].second != eXY && adj[y][i].first != exY)
                { ++cB; B = adj[y][i].first; eB = adj[y][i].second; }
        if (cB > 1) return false;
        return PairArms(eA, A, eB, B);
    }
    int cid = cycIdOf[x];
    int len = (int)cycArr[cid].size();
    if (len & 1) return false;
    int k = len / 2;
    if ((int)ncNbr[x].size() != (exX >= 0 ? 1 : 0)) return false;
    if ((int)ncNbr[y].size() != (exY >= 0 ? 1 : 0)) return false;
    int ix = cycPosOf[x], iy = cycPosOf[y];
    int dir = (iy == (ix - 1 + len) % len) ? 1 : -1;
    int P0 = ((ix + (k - 1) * dir) % len + len) % len;
    int P1 = ((ix - k * dir) % len + len) % len;
    if (cycPend[cid].size() > 4) return false;
    for (size_t t = 0; t < cycPend[cid].size(); ++t) {
        int p = cycPend[cid][t];
        if (p != ix && p != iy && p != P0 && p != P1) return false;
    }
    int v0 = cycArr[cid][P0], v1 = cycArr[cid][P1];
    if (ncNbr[v0].size() > 1 || ncNbr[v1].size() > 1) return false;
    int A = -1, eA = -1, B = -1, eB = -1;
    if (ncNbr[v0].size() == 1) { A = ncNbr[v0][0]; eA = findE(v0, A); }
    if (ncNbr[v1].size() == 1) { B = ncNbr[v1][0]; eB = findE(v1, B); }
    return PairArms(eA, A, eB, B);
}

// column 0 holds x0 and a leaf; two equal left arms converge on a vertical.
// eid0 = the bridge entering x0 from the left, or -1 when x0 is the root leaf.
static bool CaseC(int x0, int eid0) {
    int cnt = 0, z = -1, ez = -1;
    for (size_t i = 0; i < adj[x0].size(); ++i)
        if (adj[x0][i].second != eid0)
            { ++cnt; z = adj[x0][i].first; ez = adj[x0][i].second; }
    if (cnt != 1) return false;
    int L, xl, armPrev;
    if (!isChain(z)) { L = 1; xl = z; armPrev = x0; }
    else { Run r = chainRun(ez, z); L = r.cnt + 1; xl = r.nxt; armPrev = r.last; }
    if (xl < 0 || degv[xl] < 2) return false;
    int eArm = findE(armPrev, xl);
    if (eArm < 0) return false;
    for (size_t i = 0; i < adj[xl].size(); ++i) {
        if (adj[xl][i].first == armPrev) continue;
        int y = adj[xl][i].first, eXY = adj[xl][i].second;
        for (size_t j = 0; j < adj[y].size(); ++j) {
            if (adj[y][j].second == eXY) continue;
            int w = adj[y][j].first, ew = adj[y][j].second;
            if (pathOK(ew, w) && pathLen(ew, w) == L
                && RightFromCap(xl, y, eXY, armPrev, w)) return true;
        }
    }
    return false;
}

// comp(u) fits in columns >= 0 with u at (row,0); (p,u) is a bridge mapped to
// a horizontal grid edge, so comp(u) owns every column to the right.
static bool F(int e, int u) {
    int d = did(e, u);
    if (Fm[d] >= 0) return Fm[d] == 1;
    Fm[d] = 0;
    int p = oth(e, u);
    bool res = false;
    if (onCyc(u)) {
        if (ncNbr[u].size() == 1) {
            for (size_t i = 0; i < adj[u].size() && !res; ++i)
                if (isCycE[adj[u][i].second])
                    res = RightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1);
        }
    } else {
        int cnt = 0, z = -1, ez = -1;
        for (size_t i = 0; i < adj[u].size(); ++i)
            if (adj[u][i].second != e)
                { ++cnt; z = adj[u][i].first; ez = adj[u][i].second; }
        if (cnt == 0) res = true;
        else {
            if (cnt == 1 && F(ez, z)) res = true;                       // case A
            for (size_t i = 0; i < adj[u].size() && !res; ++i)          // case B
                if (adj[u][i].second != e)
                    res = RightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1);
            if (!res && cnt == 1) res = CaseC(u, e);                    // case C
        }
    }
    Fm[d] = res ? 1 : 0;
    return res;
}

// ---------------------------------------------------------------- builders --
static inline void put(int v, int r, int c) { RX[v] = r; RY[v] = c; }

static void buildF(int e, int u, int row, int col);
static void buildRightFromCap(int x, int y, int eXY, int exX, int exY, int rowX, int col);
static void buildCaseC(int x0, int eid0, int row, int col);

static void buildStraight(int e, int u, int row, int col, int dir) {
    int pe = e, cur = u, c = col;
    for (;;) {
        put(cur, row, c);
        int nx = -1, ne = -1;
        for (size_t i = 0; i < adj[cur].size(); ++i)
            if (adj[cur][i].second != pe) { nx = adj[cur][i].first; ne = adj[cur][i].second; }
        if (nx < 0) return;
        pe = ne; cur = nx; c += dir;
    }
}

static void buildContAt(int e, int y, int L, int row, int col) {
    int pe = e, cur = y, c = col;
    for (int t = 1;; ++t) {
        put(cur, row, c);
        int nx = -1, ne = -1;
        for (size_t i = 0; i < adj[cur].size(); ++i)
            if (adj[cur][i].second != pe) { nx = adj[cur][i].first; ne = adj[cur][i].second; }
        if (t == L) { buildF(ne, nx, row, c + 1); return; }
        pe = ne; cur = nx; ++c;
    }
}

static void buildF(int e, int u, int row, int col) {
    put(u, row, col);
    int p = oth(e, u);
    if (onCyc(u)) {
        for (size_t i = 0; i < adj[u].size(); ++i)
            if (isCycE[adj[u][i].second]
                && RightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1)) {
                buildRightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1, row, col);
                return;
            }
        return;
    }
    int cnt = 0, z = -1, ez = -1;
    for (size_t i = 0; i < adj[u].size(); ++i)
        if (adj[u][i].second != e) { ++cnt; z = adj[u][i].first; ez = adj[u][i].second; }
    if (cnt == 0) return;
    if (cnt == 1 && F(ez, z)) { buildF(ez, z, row, col + 1); return; }
    for (size_t i = 0; i < adj[u].size(); ++i)
        if (adj[u][i].second != e
            && RightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1)) {
            buildRightFromCap(u, adj[u][i].first, adj[u][i].second, p, -1, row, col);
            return;
        }
    if (cnt == 1) buildCaseC(u, e, row, col);
}

static void buildPairArms(int eA, int A, int eB, int B, int rowA, int col) {
    int rowB = 1 - rowA;
    if (A < 0 && B < 0) return;
    if (B < 0) { buildF(eA, A, rowA, col); return; }
    if (A < 0) { buildF(eB, B, rowB, col); return; }
    if (pathOK(eA, A)) {
        int L = pathLen(eA, A);
        if (pathOK(eB, B) && pathLen(eB, B) == L) {
            buildStraight(eA, A, rowA, col, 1); buildStraight(eB, B, rowB, col, 1); return;
        }
        if (ContAt(eB, B, L)) {
            buildStraight(eA, A, rowA, col, 1); buildContAt(eB, B, L, rowB, col); return;
        }
    }
    if (pathOK(eB, B)) {
        int L = pathLen(eB, B);
        if (pathOK(eA, A) && pathLen(eA, A) == L) {
            buildStraight(eA, A, rowA, col, 1); buildStraight(eB, B, rowB, col, 1); return;
        }
        if (ContAt(eA, A, L)) {
            buildStraight(eB, B, rowB, col, 1); buildContAt(eA, A, L, rowA, col); return;
        }
    }
}

static void buildRightFromCap(int x, int y, int eXY, int exX, int exY, int rowX, int col) {
    int rowY = 1 - rowX;
    put(x, rowX, col);
    put(y, rowY, col);
    if (!isCycE[eXY]) {
        int A = -1, eA = -1, B = -1, eB = -1;
        for (size_t i = 0; i < adj[x].size(); ++i)
            if (adj[x][i].second != eXY && adj[x][i].first != exX)
                { A = adj[x][i].first; eA = adj[x][i].second; }
        for (size_t i = 0; i < adj[y].size(); ++i)
            if (adj[y][i].second != eXY && adj[y][i].first != exY)
                { B = adj[y][i].first; eB = adj[y][i].second; }
        buildPairArms(eA, A, eB, B, rowX, col + 1);
        return;
    }
    int cid = cycIdOf[x];
    int len = (int)cycArr[cid].size(), k = len / 2;
    int ix = cycPosOf[x], iy = cycPosOf[y];
    int dir = (iy == (ix - 1 + len) % len) ? 1 : -1;
    for (int t = 1; t < k; ++t) {
        int a = ((ix + t * dir) % len + len) % len;
        int b = ((ix - (t + 1) * dir) % len + len) % len;
        put(cycArr[cid][a], rowX, col + t);
        put(cycArr[cid][b], rowY, col + t);
    }
    int P0 = ((ix + (k - 1) * dir) % len + len) % len;
    int P1 = ((ix - k * dir) % len + len) % len;
    int v0 = cycArr[cid][P0], v1 = cycArr[cid][P1];
    int A = -1, eA = -1, B = -1, eB = -1;
    if (ncNbr[v0].size() == 1) { A = ncNbr[v0][0]; eA = findE(v0, A); }
    if (ncNbr[v1].size() == 1) { B = ncNbr[v1][0]; eB = findE(v1, B); }
    buildPairArms(eA, A, eB, B, rowX, col + k);
}

static void buildCaseC(int x0, int eid0, int row, int col) {
    int z = -1, ez = -1;
    for (size_t i = 0; i < adj[x0].size(); ++i)
        if (adj[x0][i].second != eid0) { z = adj[x0][i].first; ez = adj[x0][i].second; }
    int L, xl, armPrev;
    if (!isChain(z)) { L = 1; xl = z; armPrev = x0; }
    else { Run r = chainRun(ez, z); L = r.cnt + 1; xl = r.nxt; armPrev = r.last; }
    // row `row`, columns col .. col+L-1 : the arm x0 .. armPrev
    {
        int pe = eid0, cur = x0, c = col;
        for (int t = 0; t < L; ++t) {
            put(cur, row, c);
            int nx = -1, ne = -1;
            for (size_t i = 0; i < adj[cur].size(); ++i)
                if (adj[cur][i].second != pe) { nx = adj[cur][i].first; ne = adj[cur][i].second; }
            pe = ne; cur = nx; ++c;
        }
    }
    for (size_t i = 0; i < adj[xl].size(); ++i) {
        if (adj[xl][i].first == armPrev) continue;
        int y = adj[xl][i].first, eXY = adj[xl][i].second;
        for (size_t j = 0; j < adj[y].size(); ++j) {
            if (adj[y][j].second == eXY) continue;
            int w = adj[y][j].first, ew = adj[y][j].second;
            if (pathOK(ew, w) && pathLen(ew, w) == L
                && RightFromCap(xl, y, eXY, armPrev, w)) {
                buildStraight(ew, w, 1 - row, col + L - 1, -1);
                buildRightFromCap(xl, y, eXY, armPrev, w, row, col + L);
                return;
            }
        }
    }
}

// ------------------------------------------------------------------ driver --
static void solveOne() {
    scanf("%d %d", &n, &m);
    EU.assign(m, 0); EV.assign(m, 0);
    adj.assign(n + 1, vector<pair<int,int> >());
    degv.assign(n + 1, 0);
    for (int i = 0; i < m; ++i) {
        int a, b; scanf("%d %d", &a, &b);
        EU[i] = a; EV[i] = b;
        adj[a].push_back(make_pair(b, i));
        adj[b].push_back(make_pair(a, i));
        ++degv[a]; ++degv[b];
    }
    isCycE.assign(m, 0);
    cycIdOf.assign(n + 1, -1); cycPosOf.assign(n + 1, -1);
    cycArr.clear(); cycPend.clear();
    ncNbr.assign(n + 1, vector<int>());
    chIdOf.assign(n + 1, -1); chIdxOf.assign(n + 1, -1); chArr.clear();
    Fm.assign(2 * m + 2, -1); Pm.assign(2 * m + 2, -1); Pl.assign(2 * m + 2, 0);
    RX.assign(n + 1, -1); RY.assign(n + 1, 0);

    bool ok = true;
    for (int v = 1; v <= n; ++v) if (degv[v] > 3) ok = false;

    // cycle detection (cactus: every edge is on at most one cycle)
    if (ok) {
        vector<int> pv(n + 1, 0), pe(n + 1, -1), dsc(n + 1, 0);
        int tm = 0;
        vector<pair<int, size_t> > st;
        for (int s = 1; s <= n; ++s) {
            if (dsc[s]) continue;
            dsc[s] = ++tm; st.clear(); st.push_back(make_pair(s, (size_t)0));
            while (!st.empty()) {
                int u = st.back().first;
                if (st.back().second < adj[u].size()) {
                    size_t idx = st.back().second++;
                    int v = adj[u][idx].first, e = adj[u][idx].second;
                    if (e == pe[u]) continue;
                    if (!dsc[v]) {
                        pv[v] = u; pe[v] = e; dsc[v] = ++tm;
                        st.push_back(make_pair(v, (size_t)0));
                    } else if (dsc[v] < dsc[u]) {
                        vector<int> cyc;
                        int cur = u;
                        while (cur != v) { cyc.push_back(cur); isCycE[pe[cur]] = 1; cur = pv[cur]; }
                        cyc.push_back(v);
                        isCycE[e] = 1;
                        reverse(cyc.begin(), cyc.end());
                        int cid = (int)cycArr.size();
                        for (size_t t = 0; t < cyc.size(); ++t) {
                            if (cycIdOf[cyc[t]] >= 0) ok = false;  // not a cactus
                            cycIdOf[cyc[t]] = cid; cycPosOf[cyc[t]] = (int)t;
                        }
                        cycArr.push_back(cyc);
                    }
                } else st.pop_back();
            }
        }
        for (size_t c = 0; c < cycArr.size(); ++c)
            if (cycArr[c].size() & 1) ok = false;
    }

    if (ok) {
        for (int e = 0; e < m; ++e) if (!isCycE[e])
            { ncNbr[EU[e]].push_back(EV[e]); ncNbr[EV[e]].push_back(EU[e]); }
        cycPend.assign(cycArr.size(), vector<int>());
        for (size_t c = 0; c < cycArr.size(); ++c)
            for (size_t t = 0; t < cycArr[c].size(); ++t)
                if (!ncNbr[cycArr[c][t]].empty()) cycPend[c].push_back((int)t);
        // maximal runs of degree-2 non-cycle vertices
        for (int v = 1; v <= n; ++v) {
            if (!isChain(v) || chIdOf[v] >= 0) continue;
            int cn = 0;
            for (size_t i = 0; i < adj[v].size(); ++i) if (isChain(adj[v][i].first)) ++cn;
            if (cn >= 2) continue;
            int cid = (int)chArr.size();
            vector<int> arr;
            int prev = -1, cur = v;
            for (;;) {
                arr.push_back(cur); chIdOf[cur] = cid; chIdxOf[cur] = (int)arr.size() - 1;
                int nx = -1;
                for (size_t i = 0; i < adj[cur].size(); ++i) {
                    int w = adj[cur][i].first;
                    if (w != prev && isChain(w) && chIdOf[w] < 0) nx = w;
                }
                if (nx < 0) break;
                prev = cur; cur = nx;
            }
            chArr.push_back(arr);
        }
    }

    if (!ok) { printf("No\n"); return; }
    if (n == 1) { printf("Yes\n0 0\n"); return; }

    int mode = -1, ra = -1, rb = -1, re = -1;
    for (int v = 1; v <= n && mode < 0; ++v) {          // (a) single-cell leftmost column
        if (degv[v] != 1) continue;
        int z = adj[v][0].first, e = adj[v][0].second;
        if (F(e, z)) { mode = 0; ra = v; rb = z; re = e; }
    }
    for (int e = 0; e < m && mode < 0; ++e) {           // (b) vertical in leftmost column
        if (RightFromCap(EU[e], EV[e], e, -1, -1)) { mode = 1; ra = EU[e]; rb = EV[e]; re = e; }
    }
    for (int v = 1; v <= n && mode < 0; ++v) {          // (c) two converging left arms
        if (degv[v] != 1) continue;
        if (CaseC(v, -1)) { mode = 2; ra = v; }
    }

    if (mode < 0) { printf("No\n"); return; }
    if (mode == 0) { put(ra, 0, 0); buildF(re, rb, 0, 1); }
    else if (mode == 1) buildRightFromCap(ra, rb, re, -1, -1, 0, 0);
    else buildCaseC(ra, -1, 0, 0);

    printf("Yes\n");
    for (int v = 1; v <= n; ++v) printf("%d %d\n", RX[v], RY[v]);
}

static void *run(void *) {
    int t;
    if (scanf("%d", &t) != 1) return NULL;
    while (t--) solveOne();
    return NULL;
}

int main() {
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 512ULL * 1024 * 1024);
    pthread_t th;
    pthread_create(&th, &attr, run, NULL);
    pthread_join(th, NULL);
    pthread_attr_destroy(&attr);
    return 0;
}
