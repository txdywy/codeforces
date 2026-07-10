#define NDEBUG
#include <algorithm>
#include <cassert>
#include <cstdio>
#include <vector>
using namespace std;

using i64 = long long;

struct FastInput {
    static constexpr int BUFFER_SIZE = 1 << 20;
    char buffer[BUFFER_SIZE];
    int at = 0, end = 0;

    inline char getChar() {
        if (at == end) {
            end = (int)fread(buffer, 1, BUFFER_SIZE, stdin);
            at = 0;
        }
        return at == end ? 0 : buffer[at++];
    }

    template<class T>
    inline void read(T& value) {
        char c;
        do c = getChar(); while (c <= ' ');
        value = 0;
        do {
            value = value * 10 + (c - '0');
            c = getChar();
        } while (c > ' ');
    }
};

struct FastOutput {
    static constexpr int BUFFER_SIZE = 1 << 20;
    char buffer[BUFFER_SIZE];
    int at = 0;
    ~FastOutput() { flush(); }

    inline void flush() {
        fwrite(buffer, 1, at, stdout);
        at = 0;
    }

    inline void write(i64 value) {
        if (at + 32 > BUFFER_SIZE) flush();
        char digits[24];
        int count = 0;
        do {
            digits[count++] = char('0' + value % 10);
            value /= 10;
        } while (value);
        while (count) buffer[at++] = digits[--count];
        buffer[at++] = '\n';
    }
};

struct SparseTable {
    const vector<int>* lg = nullptr;
    vector<vector<int>> st;

    SparseTable() = default;
    SparseTable(const vector<int>& a, const vector<int>& logs) : lg(&logs) {
        int n = (int)a.size() - 1;
        int k = logs[n] + 1;
        st.assign(k, vector<int>(n + 1));
        st[0] = a;
        for (int j = 1; j < k; ++j) {
            int len = 1 << j, half = len >> 1;
            for (int i = 1; i + len - 1 <= n; ++i) {
                int x = st[j - 1][i], y = st[j - 1][i + half];
                st[j][i] = max(x, y);
            }
        }
    }

    int query(int l, int r) const {
        assert(l <= r);
        int j = (*lg)[r - l + 1];
        int x = st[j][l], y = st[j][r - (1 << j) + 1];
        return max(x, y);
    }
};

struct Agg {
    static constexpr i64 BAD = -(1LL << 60);
    i64 whole = 0;
    i64 pref = 0;
    i64 suff = 0;
    i64 best = 0;
};

static inline Agg mergeAgg(const Agg& a, const Agg& b) {
    Agg c;
    c.whole = (a.whole >= 0 && b.whole >= 0) ? a.whole + b.whole : Agg::BAD;
    c.pref = (a.whole >= 0) ? a.whole + b.pref : a.pref;
    c.suff = (b.whole >= 0) ? b.whole + a.suff : b.suff;
    c.best = max({a.best, b.best, a.suff + b.pref});
    return c;
}

static inline Agg oneValue(i64 x) {
    if (x == 0) return {Agg::BAD, 0, 0, 0};
    return {x, x, x, x};
}

struct ChainValueForest {
    struct Meta {
        int start = 0;
        int size = 0;
        int offset = 0;
    };
    vector<Meta> chains;
    vector<Agg> tree;
    const vector<int>* chainId = nullptr;
    const vector<int>* coordinates = nullptr;
    const vector<i64>* values = nullptr;

    void build(const vector<int>& coords, vector<int>& ends, const vector<i64>& p) {
        chainId = &ends;
        coordinates = &coords;
        values = &p;
        int n = (int)coords.size();
        size_t total = 0;
        for (int start = 0; start < n; ) {
            int end = ends[start];
            int length = end - start;
            if (length == 1) {
                ends[start] = -1;
                start = end;
                continue;
            }
            int size = 1;
            while (size < length) size <<= 1;
            int id = (int)chains.size();
            chains.push_back({start, size, (int)total});
            for (int pos = start; pos < end; ++pos) ends[pos] = id;
            total += 2u * (unsigned)size;
            start = end;
        }
        tree.assign(total, Agg{});
        for (int id = 0; id < (int)chains.size(); ++id) {
            const Meta& meta = chains[id];
            int end = meta.start;
            while (end < n && ends[end] == id) ++end;
            for (int pos = meta.start; pos < end; ++pos)
                tree[meta.offset + meta.size + pos - meta.start] = oneValue(p[coords[pos]]);
            for (int v = meta.size - 1; v; --v)
                tree[meta.offset + v] = mergeAgg(tree[meta.offset + (v << 1)], tree[meta.offset + (v << 1 | 1)]);
        }
    }

    void setPoint(int pos, i64 value) {
        int id = (*chainId)[pos];
        if (id < 0) return;
        const Meta& meta = chains[id];
        int v = meta.size + pos - meta.start;
        tree[meta.offset + v] = oneValue(value);
        for (v >>= 1; v; v >>= 1) {
            tree[meta.offset + v] = mergeAgg(tree[meta.offset + (v << 1)], tree[meta.offset + (v << 1 | 1)]);
        }
    }

    Agg query(int pos, int count) const {
        int id = (*chainId)[pos];
        if (id < 0) {
            assert(count == 1);
            return oneValue((*values)[(*coordinates)[pos]]);
        }
        const Meta& meta = chains[id];
        int l = meta.size + pos - meta.start;
        if (count == 1) return tree[meta.offset + l];
        int r = l + count;
        Agg left, right;
        bool hasLeft = false, hasRight = false;
        while (l < r) {
            if (l & 1) {
                const Agg& part = tree[meta.offset + l++];
                left = hasLeft ? mergeAgg(left, part) : part;
                hasLeft = true;
            }
            if (r & 1) {
                const Agg& part = tree[meta.offset + --r];
                right = hasRight ? mergeAgg(part, right) : part;
                hasRight = true;
            }
            l >>= 1;
            r >>= 1;
        }
        if (!hasLeft) return right;
        if (!hasRight) return left;
        return mergeAgg(left, right);
    }
};

struct CompatibilitySegTree {
    static constexpr int INF = 1'000'000'000;
    struct Node {
        int maxLow = -INF;
        int minHigh = INF;
    };
    int n = 0, size = 1;
    vector<Node> tree;

    void build(const vector<int>& low, const vector<int>& high) {
        n = (int)low.size();
        while (size < n) size <<= 1;
        tree.assign(2 * size, Node{});
        for (int i = 0; i < n; ++i) tree[size + i] = {low[i], high[i]};
        for (int i = size - 1; i; --i) tree[i] = merge(tree[i << 1], tree[i << 1 | 1]);
    }

    static Node merge(const Node& a, const Node& b) {
        return {max(a.maxLow, b.maxLow), min(a.minHigh, b.minHigh)};
    }

    int firstBad(int ql, int qr, int diagonal) const {
        if (ql >= qr) return -1;
        if (qr - ql <= 4) {
            for (int i = ql; i < qr; ++i) {
                const Node& x = tree[size + i];
                if (x.maxLow > diagonal || x.minHigh < diagonal) return i;
            }
            return -1;
        }
        int leftNodes[32], rightNodes[32];
        int leftCount = 0, rightCount = 0;
        int l = ql + size, r = qr + size;
        while (l < r) {
            if (l & 1) leftNodes[leftCount++] = l++;
            if (r & 1) rightNodes[rightCount++] = --r;
            l >>= 1;
            r >>= 1;
        }
        auto bad = [&](int x) {
            return tree[x].maxLow > diagonal || tree[x].minHigh < diagonal;
        };
        auto consume = [&](int x) -> int {
            if (!bad(x)) return -1;
            while (x < size) {
                x <<= 1;
                if (!bad(x)) ++x;
            }
            return x - size;
        };
        for (int i = 0; i < leftCount; ++i) {
            int answer = consume(leftNodes[i]);
            if (answer != -1) return answer;
        }
        for (int i = rightCount - 1; i >= 0; --i) {
            int answer = consume(rightNodes[i]);
            if (answer != -1) return answer;
        }
        return -1;
    }
};

struct Ref {
    int pos = -1;
    int end = -1;
};

struct DivideNode {
    int l = 0, r = 0, mid = 0;
    int leftChild = -1, rightChild = -1;
    int leftRefOffset = -1, rightRefOffset = -1;
};

struct Solver {
    int n;
    vector<int> a, b, invA, invB;
    vector<i64> p;
    vector<int> logs;
    vector<int> ngrA, ngrB, pglA, pglB;
    SparseTable maxA, maxB;

    vector<DivideNode> dnodes;
    vector<Ref> leftRefs, rightRefs;
    vector<int> leftCoords, rightCoords;
    vector<int> leftChainEnd;
    vector<int> partnerChain, partnerRunEnd;
    vector<int> lowDiagonal, highDiagonal;
    vector<int> occurrenceOffset, occurrencePosition;

    vector<int> tmpParent, tmpIndegree, tmpLo, tmpHi, component;
    ChainValueForest valueTree;
    CompatibilitySegTree compatibilityTree;
    int root = -1;

    explicit Solver(int n_) : n(n_), a(n + 1), b(n + 1), invA(n + 1), invB(n + 1),
        p(n), logs(n + 2), ngrA(n + 1), ngrB(n + 1), pglA(n + 1), pglB(n + 1),
        occurrenceOffset(n + 1), tmpParent(n + 1), tmpIndegree(n + 1),
        tmpLo(n + 1), tmpHi(n + 1) {}

    static void nearestGreater(const vector<int>& v, vector<int>& ngr, vector<int>& pgl) {
        int n = (int)v.size() - 1;
        vector<int> st;
        st.reserve(n);
        for (int i = 1; i <= n; ++i) {
            while (!st.empty() && v[st.back()] < v[i]) st.pop_back();
            pgl[i] = st.empty() ? 0 : st.back();
            st.push_back(i);
        }
        st.clear();
        for (int i = n; i >= 1; --i) {
            while (!st.empty() && v[st.back()] < v[i]) st.pop_back();
            ngr[i] = st.empty() ? n + 1 : st.back();
            st.push_back(i);
        }
    }

    int argmaxA(int l, int r) const { return invA[maxA.query(l, r)]; }
    int argmaxB(int l, int r) const { return invB[maxB.query(l, r)]; }


    void appendLeftChains(int L, int M, int refOffset) {
        for (int x = L; x <= M; ++x) tmpIndegree[x] = 0;
        for (int x = L; x <= M; ++x) {
            if (tmpParent[x] != -1) {
                assert(x < tmpParent[x] && tmpParent[x] <= M);
                ++tmpIndegree[tmpParent[x]];
            }
        }
        for (int start = L; start <= M; ++start) if (tmpIndegree[start] == 0) {
            component.clear();
            int x = start;
            while (x != -1) {
                component.push_back(x);
                x = tmpParent[x];
            }
            int base = (int)leftCoords.size();
            int end = base + (int)component.size();
            for (int i = 0; i < (int)component.size(); ++i) {
                int v = component[i];
                leftCoords.push_back(v);
                leftChainEnd.push_back(end);
                partnerChain.push_back(-1);
                partnerRunEnd.push_back(base + i + 1);
                lowDiagonal.push_back(CompatibilitySegTree::INF);
                highDiagonal.push_back(-CompatibilitySegTree::INF);
                leftRefs[refOffset + v - L] = {base + i, end};
                assert(v < n);
            }
        }
#ifndef NDEBUG
        for (int x = L; x <= M; ++x) assert(leftRefs[refOffset + x - L].pos != -1);
#endif
    }

    void appendRightChains(int M, int R, int refOffset) {
        for (int y = M + 1; y <= R; ++y) tmpIndegree[y] = 0;
        for (int y = M + 1; y <= R; ++y) {
            if (tmpParent[y] != -1) {
                assert(M < tmpParent[y] && tmpParent[y] < y);
                ++tmpIndegree[tmpParent[y]];
            }
        }
        for (int start = M + 1; start <= R; ++start) if (tmpIndegree[start] == 0) {
            component.clear();
            int y = start;
            while (y != -1) {
                component.push_back(y);
                y = tmpParent[y];
            }
            int base = (int)rightCoords.size();
            int end = base + (int)component.size();
            for (int i = 0; i < (int)component.size(); ++i) {
                int v = component[i];
                rightCoords.push_back(v);
                rightRefs[refOffset + v - (M + 1)] = {base + i, end};
            }
        }
#ifndef NDEBUG
        for (int y = M + 1; y <= R; ++y) assert(rightRefs[refOffset + y - (M + 1)].pos != -1);
#endif
    }

    int buildDivide(int L, int R) {
        int id = (int)dnodes.size();
        dnodes.push_back({L, R, (L + R) >> 1, -1, -1, -1, -1});
        if (L == R) return id;
        int M = (L + R) >> 1;
        int leftOffset = (int)leftRefs.size();
        int rightOffset = (int)rightRefs.size();
        leftRefs.resize(leftOffset + M - L + 1);
        rightRefs.resize(rightOffset + R - M);
        dnodes[id].leftRefOffset = leftOffset;
        dnodes[id].rightRefOffset = rightOffset;

        for (int x = L; x <= M; ++x) {
            tmpParent[x] = -1;
            tmpLo[x] = R + 1;
            tmpHi[x] = R;
        }
        int bestAPos = -1, bestBPos = -1, bestAVal = -1, bestBVal = -1;
        for (int x = M - 1; x >= L; --x) {
            int z = x + 1;
            if (a[z] > bestAVal) bestAVal = a[z], bestAPos = z;
            if (b[z] > bestBVal) bestBVal = b[z], bestBPos = z;
            int ta = ngrA[bestAPos] <= R ? ngrA[bestAPos] : R + 1;
            int tb = ngrB[bestBPos] <= R ? ngrB[bestBPos] : R + 1;
            if (ta == tb) continue;
            int lo = min(ta, tb) + 1;
            int hi = min(max(ta, tb), R);
            if (lo > hi) continue;

            int first = R + 1, last = L - 1;
            if (ngrA[x] < ngrB[x]) {
                hi = min(hi, ngrB[x] - 1);
                if (lo <= hi) {
                    int z0 = argmaxA(x, lo - 1);
                    first = ngrA[z0];
                    if (first <= hi) last = argmaxA(x, hi);
                }
            } else if (ngrB[x] < ngrA[x]) {
                hi = min(hi, ngrA[x] - 1);
                if (lo <= hi) {
                    int z0 = argmaxB(x, lo - 1);
                    first = ngrB[z0];
                    if (first <= hi) last = argmaxB(x, hi);
                }
            }
            if (first > last) continue;
            tmpLo[x] = first;
            tmpHi[x] = last;
            if (ta < tb) {
                tmpParent[x] = bestBPos;
            } else {
                tmpParent[x] = bestAPos;
            }
        }
        int nodeLeftBegin = (int)leftCoords.size();
        appendLeftChains(L, M, leftOffset);

        for (int y = M + 1; y <= R; ++y) {
            tmpParent[y] = -1;
        }
        bestAPos = bestBPos = -1;
        bestAVal = bestBVal = -1;
        for (int y = M + 2; y <= R; ++y) {
            int z = y - 1;
            if (a[z] > bestAVal) bestAVal = a[z], bestAPos = z;
            if (b[z] > bestBVal) bestBVal = b[z], bestBPos = z;
            int sa = pglA[bestAPos] >= L ? pglA[bestAPos] : L - 1;
            int sb = pglB[bestBPos] >= L ? pglB[bestBPos] : L - 1;
            if (sa == sb) continue;
            int lo = max(min(sa, sb), L);
            int hi = max(sa, sb) - 1;
            if (lo > hi) continue;

            int first = R + 1, last = L - 1;
            if (pglA[y] > pglB[y]) {
                lo = max(lo, pglB[y] + 1);
                if (lo <= hi) {
                    int z0 = argmaxA(hi + 1, y);
                    last = pglA[z0];
                    if (last >= lo) first = argmaxA(lo, y);
                }
            } else if (pglB[y] > pglA[y]) {
                lo = max(lo, pglA[y] + 1);
                if (lo <= hi) {
                    int z0 = argmaxB(hi + 1, y);
                    last = pglB[z0];
                    if (last >= lo) first = argmaxB(lo, y);
                }
            }
            if (first > last) continue;
            if (sa > sb) {
                tmpParent[y] = bestBPos;
            } else {
                tmpParent[y] = bestAPos;
            }
        }
        appendRightChains(M, R, rightOffset);

        // For a fixed left-chain vertex x, all legal right endpoints whose
        // next state still crosses M form one contiguous interval on one
        // right chain. Store that interval in diagonal coordinates.
        for (int x = L; x < M; ++x) if (tmpParent[x] != -1) {
            int first = tmpLo[x], last = tmpHi[x];

            Ref leftRef = leftRefs[leftOffset + x - L];
            Ref firstRef = rightRefs[rightOffset + first - (M + 1)];
            Ref lastRef = rightRefs[rightOffset + last - (M + 1)];
            assert(firstRef.end == lastRef.end);
            int lowPos = min(firstRef.pos, lastRef.pos);
            int highPos = max(firstRef.pos, lastRef.pos);
            partnerChain[leftRef.pos] = firstRef.end;
            lowDiagonal[leftRef.pos] = lowPos - leftRef.pos;
            highDiagonal[leftRef.pos] = highPos - leftRef.pos;
        }
        for (int pos = (int)leftCoords.size() - 1; pos >= nodeLeftBegin; --pos) {
            if (pos + 1 < leftChainEnd[pos] && partnerChain[pos] == partnerChain[pos + 1])
                partnerRunEnd[pos] = partnerRunEnd[pos + 1];
            else
                partnerRunEnd[pos] = pos + 1;
        }

        int lc = buildDivide(L, M);
        int rc = buildDivide(M + 1, R);
        dnodes[id].leftChild = lc;
        dnodes[id].rightChild = rc;
        return id;
    }

    void prepare() {
        for (int i = 2; i <= n + 1; ++i) logs[i] = logs[i >> 1] + 1;
        for (int i = 1; i <= n; ++i) invA[a[i]] = i, invB[b[i]] = i;
        nearestGreater(a, ngrA, pglA);
        nearestGreater(b, ngrB, pglB);
        maxA = SparseTable(a, logs);
        maxB = SparseTable(b, logs);

        int levels = logs[n] + 2;
        size_t reserveCount = (size_t)n * levels;
        dnodes.reserve(2 * n);
        leftRefs.reserve(reserveCount / 2 + n);
        rightRefs.reserve(reserveCount / 2 + n);
        leftCoords.reserve(reserveCount / 2 + n);
        rightCoords.reserve(reserveCount / 2 + n);
        leftChainEnd.reserve(reserveCount / 2 + n);
        partnerChain.reserve(reserveCount / 2 + n);
        partnerRunEnd.reserve(reserveCount / 2 + n);
        lowDiagonal.reserve(reserveCount / 2 + n);
        highDiagonal.reserve(reserveCount / 2 + n);
        component.reserve(n);
        root = buildDivide(1, n);
        for (int start = 0; start < (int)leftCoords.size(); ) {
            int end = leftChainEnd[start];
            if (end - start > 1) {
                for (int pos = start; pos < end; ++pos)
                    ++occurrenceOffset[leftCoords[pos] + 1];
            }
            start = end;
        }
        for (int x = 0; x < n; ++x) occurrenceOffset[x + 1] += occurrenceOffset[x];
        occurrencePosition.resize(occurrenceOffset[n]);
        vector<int> cursor = occurrenceOffset;
        for (int start = 0; start < (int)leftCoords.size(); ) {
            int end = leftChainEnd[start];
            if (end - start > 1) {
                for (int pos = start; pos < end; ++pos)
                    occurrencePosition[cursor[leftCoords[pos]]++] = pos;
            }
            start = end;
        }
        compatibilityTree.build(lowDiagonal, highDiagonal);
        valueTree.build(leftCoords, leftChainEnd, p);
    }

    int descendToSeparator(int node, int x, int y) const {
        while (dnodes[node].l != dnodes[node].r) {
            const auto& d = dnodes[node];
            if (x <= d.mid && d.mid < y) return node;
            if (y <= d.mid) node = d.leftChild;
            else node = d.rightChild;
        }
        assert(false);
        return -1;
    }

    i64 queryAnswer(int l, int r, int k) const {
        if (k == 0 || l + 1 >= r) return 0;
        Agg answer = oneValue(p[l]);
        --k;
        if (k == 0) return answer.best;
        int ia = argmaxA(l + 1, r - 1);
        int ib = argmaxB(l + 1, r - 1);
        if (ia == ib) return answer.best;
        int x = min(ia, ib), y = max(ia, ib);
        if (x + 1 >= y) return answer.best;

        int node = descendToSeparator(root, x, y);
        while (k > 0) {
            const auto& d = dnodes[node];
            Ref lr = leftRefs[d.leftRefOffset + x - d.l];
            Ref rr = rightRefs[d.rightRefOffset + y - (d.mid + 1)];
            int common = 0;
            if (partnerChain[lr.pos] == rr.end) {
                int maximumEdges = min(lr.end - lr.pos - 1, rr.end - rr.pos - 1);
                int limit = min(lr.pos + maximumEdges, partnerRunEnd[lr.pos]);
                int diagonal = rr.pos - lr.pos;
                int bad = compatibilityTree.firstBad(lr.pos, limit, diagonal);
                common = (bad == -1 ? limit : bad) - lr.pos;
            }
            int lastX = leftCoords[lr.pos + common];
            int lastY = rightCoords[rr.pos + common];
            bool adjacent = lastX + 1 >= lastY;
            int phaseLength = adjacent ? common : common + 1;
            assert(phaseLength > 0);
            int take = min(k, phaseLength);
            answer = mergeAgg(answer, valueTree.query(lr.pos, take));
            k -= take;
            if (k == 0 || adjacent) break;

            ia = argmaxA(lastX + 1, lastY - 1);
            ib = argmaxB(lastX + 1, lastY - 1);
            if (ia == ib) break;
            x = min(ia, ib);
            y = max(ia, ib);
            if (x + 1 >= y) break;
            if (y <= d.mid) node = d.leftChild;
            else if (x > d.mid) node = d.rightChild;
            else {
                // A valid active transition would have extended the LCP.
                assert(false);
            }
            node = descendToSeparator(node, x, y);
        }
        return answer.best;
    }

    void update(int x, i64 y) {
        p[x] = y;
        for (int i = occurrenceOffset[x]; i < occurrenceOffset[x + 1]; ++i)
            valueTree.setPoint(occurrencePosition[i], y);
    }
};

int main() {
    FastInput input;
    FastOutput output;
    int T;
    input.read(T);
    while (T--) {
        int n, m;
        input.read(n);
        input.read(m);
        Solver solver(n);
        for (int i = 1; i <= n; ++i) input.read(solver.a[i]);
        for (int i = 1; i <= n; ++i) input.read(solver.b[i]);
        for (int i = 0; i < n; ++i) input.read(solver.p[i]);
        solver.prepare();
        while (m--) {
            int type;
            input.read(type);
            if (type == 1) {
                int l, r, k;
                input.read(l);
                input.read(r);
                input.read(k);
                output.write(solver.queryAnswer(l, r, k));
            } else {
                int x;
                i64 y;
                input.read(x);
                input.read(y);
                solver.update(x, y);
            }
        }
    }
    return 0;
}
