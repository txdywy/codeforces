#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <queue>
#include <set>
#include <unordered_set>
#include <utility>
#include <vector>
using namespace std;

struct DSU {
    vector<int> p, sz;
    explicit DSU(int n = 0) : p(n), sz(n, 1) { iota(p.begin(), p.end(), 0); }
    int find(int x) { return p[x] == x ? x : p[x] = find(p[x]); }
    void unite(int a, int b) {
        a = find(a), b = find(b);
        if (a == b) return;
        if (sz[a] < sz[b]) swap(a, b);
        p[b] = a;
        sz[a] += sz[b];
    }
};

struct Solver {
    struct Edge { int u, v; };
    struct HAdj { int to, id, port; };
    struct HEdge { int a, b, pa, pb; };
    struct Inc {
        int atom, port;
        int kind; // 0 = Q edge, 1 = arm
        int ref;
    };
    struct QEdge {
        int a, b, ia, ib;
        vector<int> path; // actual original vertices, including both ports
        int len() const { return int(path.size()) - 1; }
    };
    struct Arm {
        int atom, inc;
        vector<int> path; // root port, then all vertices of the arm
        int len() const { return int(path.size()) - 1; }
    };
    struct RAdj { int to, qid; };
    struct SmallOpt { int l, r, param; };
    struct State {
        int s, e, prev, param, l, r;
    };
    struct ChosenToken {
        int s, e, param;
        int left_col, right_col;
    };

    int n, m;
    vector<Edge> edges;
    vector<vector<pair<int,int>>> g;

    vector<vector<int>> cycles;
    vector<int> cycle_of, pos_in_cycle;

    vector<vector<HAdj>> h;
    vector<HEdge> hedges;
    vector<int> h_orig, h_cycle;

    vector<int> atom_h, atom_of_h, atom_type; // 0 = V, 1 = C
    vector<vector<int>> atom_incs;
    vector<Inc> incs;
    vector<QEdge> qedges;
    vector<Arm> arms;
    vector<int> qdeg;

    vector<vector<int>> r_members;
    vector<int> r_internal_q;
    vector<int> r_order, r_edge_q;

    vector<pair<int,int>> answer;
    bool bad = false;

    explicit Solver(int n_, int m_) : n(n_), m(m_), edges(m_), g(n_) {}

    static int mod(int x, int m) {
        x %= m;
        if (x < 0) x += m;
        return x;
    }

    bool contains_atom(const vector<int>& v, int a) const {
        for (int x : v) if (x == a) return true;
        return false;
    }

    int other_q(int qid, int a) const {
        return qedges[qid].a ^ qedges[qid].b ^ a;
    }

    int inc_for_q(int qid, const vector<int>& members) const {
        const auto &q = qedges[qid];
        if (contains_atom(members, q.a)) return q.ia;
        if (contains_atom(members, q.b)) return q.ib;
        return -1;
    }

    int port_at_h_edge(int eid, int node) const {
        const auto &e = hedges[eid];
        return e.a == node ? e.pa : e.pb;
    }

    int other_h(int eid, int node) const {
        const auto &e = hedges[eid];
        return e.a ^ e.b ^ node;
    }

    bool extract_cycles() {
        vector<int> tin(n, -1), par(n, -1), pe(n, -1), it(n, 0);
        int timer = 0;
        for (int root = 0; root < n; ++root) if (tin[root] == -1) {
            vector<int> st(1, root);
            tin[root] = timer++;
            while (!st.empty()) {
                int v = st.back();
                if (it[v] == (int)g[v].size()) {
                    st.pop_back();
                    continue;
                }
                auto [u, eid] = g[v][it[v]++];
                if (eid == pe[v]) continue;
                if (tin[u] == -1) {
                    tin[u] = timer++;
                    par[u] = v;
                    pe[u] = eid;
                    st.push_back(u);
                } else if (tin[u] < tin[v]) {
                    vector<int> cyc;
                    int x = v;
                    cyc.push_back(x);
                    while (x != u) {
                        x = par[x];
                        if (x < 0) return false;
                        cyc.push_back(x);
                    }
                    reverse(cyc.begin(), cyc.end());
                    cycles.push_back(std::move(cyc));
                }
            }
        }

        cycle_of.assign(n, -1);
        pos_in_cycle.assign(n, -1);
        for (int c = 0; c < (int)cycles.size(); ++c) {
            if (cycles[c].size() & 1) return false;
            for (int i = 0; i < (int)cycles[c].size(); ++i) {
                int v = cycles[c][i];
                if (cycle_of[v] != -1) return false;
                cycle_of[v] = c;
                pos_in_cycle[v] = i;
            }
        }
        return true;
    }

    bool build_bridge_tree() {
        int C = cycles.size();
        vector<int> hv(n, -1);
        h_orig.assign(C, -1);
        h_cycle.resize(C);
        iota(h_cycle.begin(), h_cycle.end(), 0);
        int hn = C;
        for (int v = 0; v < n; ++v) if (cycle_of[v] == -1) {
            hv[v] = hn++;
            h_orig.push_back(v);
            h_cycle.push_back(-1);
        }
        h.assign(hn, {});
        for (auto [u, v] : edges) {
            if (cycle_of[u] != -1 && cycle_of[u] == cycle_of[v]) continue;
            int a = cycle_of[u] == -1 ? hv[u] : cycle_of[u];
            int b = cycle_of[v] == -1 ? hv[v] : cycle_of[v];
            int id = hedges.size();
            hedges.push_back({a, b, u, v});
            h[a].push_back({b, id, u});
            h[b].push_back({a, id, v});
        }
        if (hn > 0 && (int)hedges.size() != hn - 1) return false;
        return true;
    }

    int add_inc(int atom, int port, int kind, int ref) {
        int id = incs.size();
        incs.push_back({atom, port, kind, ref});
        atom_incs[atom].push_back(id);
        return id;
    }

    bool build_atoms_and_q() {
        int hn = h.size();
        atom_of_h.assign(hn, -1);
        for (int x = 0; x < hn; ++x) {
            bool cyc = h_cycle[x] != -1;
            if (cyc || (int)h[x].size() == 3) {
                int a = atom_h.size();
                atom_of_h[x] = a;
                atom_h.push_back(x);
                atom_type.push_back(cyc ? 1 : 0);
            }
        }
        atom_incs.assign(atom_h.size(), {});
        if (atom_h.empty()) return true;

        vector<char> used(hedges.size(), false);
        for (int a = 0; a < (int)atom_h.size(); ++a) {
            int start_h = atom_h[a];
            for (auto first : h[start_h]) {
                if (used[first.id]) continue;
                vector<int> path;
                path.push_back(first.port);
                int last_e = first.id;
                used[last_e] = true;
                int cur = first.to;
                bool is_arm = false;
                while (atom_of_h[cur] == -1) {
                    if (h_orig[cur] < 0) return false;
                    path.push_back(h_orig[cur]);
                    int nxt_e = -1, nxt = -1;
                    for (auto z : h[cur]) if (z.id != last_e) {
                        nxt_e = z.id;
                        nxt = z.to;
                        break;
                    }
                    if (nxt_e == -1) {
                        is_arm = true;
                        break;
                    }
                    if (used[nxt_e]) return false;
                    used[nxt_e] = true;
                    last_e = nxt_e;
                    cur = nxt;
                }
                if (is_arm) {
                    int aid = arms.size();
                    int iid = add_inc(a, path.front(), 1, aid);
                    arms.push_back({a, iid, std::move(path)});
                } else {
                    int b = atom_of_h[cur];
                    path.push_back(port_at_h_edge(last_e, cur));
                    int qid = qedges.size();
                    int ia = add_inc(a, path.front(), 0, qid);
                    int ib = add_inc(b, path.back(), 0, qid);
                    qedges.push_back({a, b, ia, ib, std::move(path)});
                }
            }
        }
        for (char x : used) if (!x) return false;
        qdeg.assign(atom_h.size(), 0);
        for (auto &q : qedges) ++qdeg[q.a], ++qdeg[q.b];
        return (int)qedges.size() + 1 == (int)atom_h.size() || atom_h.size() == 1;
    }

    vector<int> token_members(int s, int e) const {
        vector<int> z;
        for (int i = s; i <= e; ++i) {
            int rid = r_order[i];
            z.insert(z.end(), r_members[rid].begin(), r_members[rid].end());
        }
        return z;
    }

    int token_internal_q(int s, int e) const {
        if (s < e) return r_edge_q[s];
        return r_internal_q[r_order[s]];
    }

    vector<int> token_external_incs(int s, int e) const {
        auto mem = token_members(s, e);
        int iq = token_internal_q(s, e);
        vector<int> ext;
        for (int a : mem) for (int iid : atom_incs[a]) {
            if (incs[iid].kind == 0 && incs[iid].ref == iq) continue;
            ext.push_back(iid);
        }
        return ext;
    }

    pair<int,int> token_core_incs(int s, int e) const {
        auto mem = token_members(s, e);
        int li = -1, ri = -1;
        if (s > 0) li = inc_for_q(r_edge_q[s - 1], mem);
        if (e + 1 < (int)r_order.size()) ri = inc_for_q(r_edge_q[e], mem);
        return {li, ri};
    }

    vector<SmallOpt> gen_options(int s, int e) const {
        auto mem = token_members(s, e);
        auto ext = token_external_incs(s, e);
        auto [li, ri] = token_core_incs(s, e);
        vector<SmallOpt> ret;
        if (mem.size() == 1 && atom_type[mem[0]] == 0) {
            vector<int> aa;
            for (int iid : ext) if (incs[iid].kind == 1) aa.push_back(iid);
            if (li != -1 && ri != -1) {
                if (aa.size() != 1) return ret;
                int reach = arms[incs[aa[0]].ref].len() - 1;
                ret.push_back({reach, 0, 0});
                ret.push_back({0, reach, 1});
            } else {
                ret.push_back({0, 0, -1});
            }
            return ret;
        }
        if (mem.size() == 1 && atom_type[mem[0]] == 1) {
            int cid = h_cycle[atom_h[mem[0]]];
            int L = cycles[cid].size(), k = L / 2;
            vector<int> cand;
            if (ext.empty()) cand.push_back(0);
            else {
                int p = pos_in_cycle[incs[ext[0]].port];
                cand = {p, p - 1, p - k, p - k - 1};
                for (int &x : cand) x = mod(x, L);
                sort(cand.begin(), cand.end());
                cand.erase(unique(cand.begin(), cand.end()), cand.end());
            }
            for (int ss : cand) {
                bool ok = true;
                int lr[2] = {0, 0};
                for (int iid : ext) {
                    int p = pos_in_cycle[incs[iid].port];
                    int side = -1;
                    if (p == ss || p == mod(ss + 1, L)) side = 0;
                    if (p == mod(ss + k, L) || p == mod(ss + k + 1, L)) side = 1;
                    if (side == -1) { ok = false; break; }
                    if (iid == li && side != 0) ok = false;
                    if (iid == ri && side != 1) ok = false;
                    if (incs[iid].kind == 1 && ((side == 0 && li != -1) || (side == 1 && ri != -1))) {
                        if (lr[side] != 0) ok = false;
                        lr[side] = arms[incs[iid].ref].len();
                    }
                }
                if (ok) ret.push_back({lr[0], lr[1], ss});
            }
            return ret;
        }

        if (mem.size() != 2 || ext.size() != 4) return ret;
        for (int mask = 0; mask < (1 << 4); ++mask) {
            bool ok = true;
            for (int a : mem) {
                int cnt[2] = {0, 0};
                for (int i = 0; i < 4; ++i) if (incs[ext[i]].atom == a) ++cnt[(mask >> i) & 1];
                if (cnt[0] != 1 || cnt[1] != 1) ok = false;
            }
            for (int i = 0; i < 4; ++i) {
                int side = (mask >> i) & 1;
                if (ext[i] == li && side != 0) ok = false;
                if (ext[i] == ri && side != 1) ok = false;
            }
            int lr[2] = {0, 0};
            if (ok) for (int i = 0; i < 4; ++i) if (incs[ext[i]].kind == 1) {
                int side = (mask >> i) & 1;
                if ((side == 0 && li != -1) || (side == 1 && ri != -1)) {
                    if (lr[side] != 0) ok = false;
                    lr[side] = arms[incs[ext[i]].ref].len();
                }
            }
            if (ok) ret.push_back({lr[0], lr[1], mask});
        }
        return ret;
    }

    bool make_r_path(const vector<int>& forced) {
        int A = atom_h.size();
        DSU dsu(A);
        for (int qid : forced) dsu.unite(qedges[qid].a, qedges[qid].b);
        vector<int> rid_root(A, -1), atom_r(A, -1);
        r_members.clear();
        for (int a = 0; a < A; ++a) {
            int rt = dsu.find(a);
            if (rid_root[rt] == -1) {
                rid_root[rt] = r_members.size();
                r_members.push_back({});
            }
            atom_r[a] = rid_root[rt];
            r_members[atom_r[a]].push_back(a);
        }
        int R = r_members.size();
        r_internal_q.assign(R, -1);
        vector<vector<RAdj>> rg(R);
        for (int qid = 0; qid < (int)qedges.size(); ++qid) {
            int x = atom_r[qedges[qid].a], y = atom_r[qedges[qid].b];
            if (x == y) {
                if (r_internal_q[x] != -1) return false;
                r_internal_q[x] = qid;
            } else {
                rg[x].push_back({y, qid});
                rg[y].push_back({x, qid});
            }
        }
        for (int i = 0; i < R; ++i) {
            if (r_members[i].size() > 2 || rg[i].size() > 2) return false;
            if (r_members[i].size() == 2 && r_internal_q[i] == -1) return false;
        }
        int start = 0;
        if (R > 1) {
            start = -1;
            for (int i = 0; i < R; ++i) if (rg[i].size() == 1) { start = i; break; }
            if (start == -1) return false;
        }
        r_order.clear();
        r_edge_q.clear();
        int prev = -1, cur = start;
        while (cur != -1) {
            r_order.push_back(cur);
            int nxt = -1, qid = -1;
            for (auto z : rg[cur]) if (z.to != prev) { nxt = z.to; qid = z.qid; break; }
            if (nxt != -1) r_edge_q.push_back(qid);
            prev = cur;
            cur = nxt;
        }
        return (int)r_order.size() == R;
    }

    bool optional_dimer_ok(int i) const {
        if (i + 1 >= (int)r_order.size()) return false;
        int x = r_order[i], y = r_order[i + 1];
        if (r_members[x].size() != 1 || r_members[y].size() != 1) return false;
        int a = r_members[x][0], b = r_members[y][0];
        return atom_type[a] == 0 && atom_type[b] == 0 && qedges[r_edge_q[i]].len() == 1;
    }

    bool path_dp(vector<ChosenToken>& chosen) const {
        int R = r_order.size();
        vector<vector<int>> end_at(R);
        vector<State> states;
        for (int s = 0; s < R; ++s) {
            for (int take = 1; take <= 2; ++take) {
                int e = s + take - 1;
                if (e >= R) continue;
                if (take == 2 && !optional_dimer_ok(s)) continue;
                auto opts = gen_options(s, e);
                for (auto op : opts) {
                    int prv = -2;
                    if (s == 0) prv = -1;
                    else {
                        int D = qedges[r_edge_q[s - 1]].len();
                        for (int sid : end_at[s - 1]) if (states[sid].r + op.l < D) {
                            prv = sid;
                            break;
                        }
                    }
                    if (prv == -2) continue;
                    int id = states.size();
                    states.push_back({s, e, prv, op.param, op.l, op.r});
                    end_at[e].push_back(id);
                }
            }
        }
        if (end_at[R - 1].empty()) return false;
        int cur = end_at[R - 1][0];
        vector<State> seq;
        while (cur != -1) {
            seq.push_back(states[cur]);
            cur = states[cur].prev;
        }
        reverse(seq.begin(), seq.end());
        chosen.clear();
        int col = 0;
        for (int i = 0; i < (int)seq.size(); ++i) {
            auto mem = token_members(seq[i].s, seq[i].e);
            int width = 0;
            if (mem.size() == 1 && atom_type[mem[0]] == 1) {
                int cid = h_cycle[atom_h[mem[0]]];
                width = (int)cycles[cid].size() / 2 - 1;
            }
            chosen.push_back({seq[i].s, seq[i].e, seq[i].param, col, col + width});
            if (i + 1 < (int)seq.size()) {
                int qid = r_edge_q[seq[i].e];
                col += width + qedges[qid].len();
            }
        }
        return true;
    }

    int cycle_side(int iid, int ss, int cid) const {
        int L = cycles[cid].size(), k = L / 2;
        int p = pos_in_cycle[incs[iid].port];
        if (p == ss || p == mod(ss + 1, L)) return 0;
        if (p == mod(ss + k, L) || p == mod(ss + k + 1, L)) return 1;
        return -1;
    }

    void put_vertex(int v, int row, int col) {
        if (answer[v].first != -1 && answer[v] != make_pair(row, col)) bad = true;
        answer[v] = {row, col};
    }

    int map_token(const ChosenToken& t, int incoming_row) {
        auto mem = token_members(t.s, t.e);
        auto [li, ri] = token_core_incs(t.s, t.e);
        int desired = li != -1 ? incoming_row : 0;
        int target = li != -1 ? li : ri;

        if (mem.size() == 1 && atom_type[mem[0]] == 0) {
            int v = h_orig[atom_h[mem[0]]];
            put_vertex(v, desired, t.left_col);
        } else if (mem.size() == 2) {
            int target_atom = target == -1 ? mem[0] : incs[target].atom;
            int canon = (mem[1] == target_atom);
            int flip = canon ^ desired;
            for (int i = 0; i < 2; ++i) {
                int v = h_orig[atom_h[mem[i]]];
                put_vertex(v, i ^ flip, t.left_col);
            }
        } else {
            int a = mem[0];
            int cid = h_cycle[atom_h[a]];
            int L = cycles[cid].size(), k = L / 2, ss = t.param;
            int canon_target = 0;
            if (target != -1) {
                int p = pos_in_cycle[incs[target].port];
                int d = mod(p - (ss + 1), L);
                canon_target = (d < k) ? 1 : 0;
            }
            int flip = canon_target ^ desired;
            for (int j = 0; j < k; ++j) {
                int u = cycles[cid][mod(ss - j, L)];
                int v = cycles[cid][mod(ss + 1 + j, L)];
                put_vertex(u, 0 ^ flip, t.left_col + j);
                put_vertex(v, 1 ^ flip, t.left_col + j);
            }
        }
        return ri == -1 ? -1 : answer[incs[ri].port].first;
    }

    void map_horizontal_arm(int iid, int side) {
        const auto &ar = arms[incs[iid].ref];
        auto [row, col] = answer[ar.path[0]];
        int dir = side ? 1 : -1;
        for (int j = 1; j < (int)ar.path.size(); ++j)
            put_vertex(ar.path[j], row, col + dir * j);
    }

    void map_vertical_arm(int iid, int side) {
        const auto &ar = arms[incs[iid].ref];
        auto [row, col] = answer[ar.path[0]];
        int dir = side ? 1 : -1;
        for (int j = 1; j < (int)ar.path.size(); ++j)
            put_vertex(ar.path[j], 1 - row, col + dir * (j - 1));
    }

    bool reconstruct(const vector<ChosenToken>& chosen) {
        answer.assign(n, {-1, 0});
        bad = false;
        int incoming = 0;
        for (int i = 0; i < (int)chosen.size(); ++i) {
            int outgoing = map_token(chosen[i], incoming);
            if (i + 1 < (int)chosen.size()) {
                int qid = r_edge_q[chosen[i].e];
                const auto &q = qedges[qid];
                auto mem = token_members(chosen[i].s, chosen[i].e);
                bool fw = contains_atom(mem, q.a);
                int D = q.len();
                for (int j = 1; j < D; ++j) {
                    int v = fw ? q.path[j] : q.path[D - j];
                    put_vertex(v, outgoing, chosen[i].right_col + j);
                }
                incoming = outgoing;
            }
        }

        for (auto &t : chosen) {
            auto mem = token_members(t.s, t.e);
            auto ext = token_external_incs(t.s, t.e);
            auto [li, ri] = token_core_incs(t.s, t.e);
            vector<int> aa;
            for (int iid : ext) if (incs[iid].kind == 1) aa.push_back(iid);
            if (mem.size() == 1 && atom_type[mem[0]] == 0) {
                if (li != -1 && ri != -1) {
                    if (aa.size() != 1) return false;
                    map_vertical_arm(aa[0], t.param);
                } else if (li == -1 && ri == -1) {
                    if (aa.size() != 3) return false;
                    map_horizontal_arm(aa[0], 0);
                    map_horizontal_arm(aa[1], 1);
                    map_vertical_arm(aa[2], 0);
                } else {
                    if (aa.size() != 2) return false;
                    int outside = (li == -1 ? 0 : 1);
                    map_horizontal_arm(aa[0], outside);
                    map_vertical_arm(aa[1], outside);
                }
            } else if (mem.size() == 1) {
                int cid = h_cycle[atom_h[mem[0]]];
                for (int iid : aa) {
                    int side = cycle_side(iid, t.param, cid);
                    if (side == -1) return false;
                    map_horizontal_arm(iid, side);
                }
            } else {
                if (ext.size() != 4) return false;
                for (int i = 0; i < 4; ++i) if (incs[ext[i]].kind == 1)
                    map_horizontal_arm(ext[i], (t.param >> i) & 1);
            }
        }

        if (bad) return false;
        for (auto p : answer) if (p.first == -1) return false;
        int mn = answer[0].second, mx = answer[0].second;
        for (auto p : answer) mn = min(mn, p.second), mx = max(mx, p.second);
        for (auto &p : answer) p.second -= mn;
        mx -= mn;
        if (mx > 200000) return false;
        unordered_set<long long> seen;
        seen.reserve(n * 2 + 1);
        for (auto [r, c] : answer) {
            if (r < 0 || r > 1 || c < 0 || c > 200000) return false;
            long long key = (static_cast<long long>(r) << 32) ^ static_cast<unsigned>(c);
            if (!seen.insert(key).second) return false;
        }
        for (auto [u, v] : edges) {
            int d = abs(answer[u].first - answer[v].first) + abs(answer[u].second - answer[v].second);
            if (d != 1) return false;
        }
        return true;
    }

    bool solve_no_atoms() {
        int start = 0;
        for (int v = 0; v < n; ++v) if (g[v].size() <= 1) { start = v; break; }
        answer.assign(n, {-1, 0});
        int prev = -1, cur = start, col = 0;
        while (cur != -1) {
            answer[cur] = {0, col++};
            int nxt = -1;
            for (auto [u, id] : g[cur]) if (u != prev) { nxt = u; break; }
            prev = cur;
            cur = nxt;
        }
        for (auto p : answer) if (p.first == -1) return false;
        return true;
    }

    bool solve() {
        for (int v = 0; v < n; ++v) if (g[v].size() > 3) return false;
        if (!extract_cycles()) return false;
        if (!build_bridge_tree()) return false;
        if (!build_atoms_and_q()) return false;
        if (atom_h.empty()) return solve_no_atoms();

        vector<int> mandatory;
        vector<vector<int>> ambiguous;
        for (int a = 0; a < (int)atom_h.size(); ++a) {
            if (atom_type[a] == 1 && qdeg[a] > 2) return false;
            if (atom_type[a] == 0 && qdeg[a] == 3) {
                vector<int> cand;
                for (int iid : atom_incs[a]) if (incs[iid].kind == 0) {
                    int qid = incs[iid].ref;
                    int b = other_q(qid, a);
                    if (atom_type[b] == 0 && qdeg[b] == 1 && qedges[qid].len() == 1)
                        cand.push_back(qid);
                }
                if (cand.empty()) return false;
                if (cand.size() == 1) mandatory.push_back(cand[0]);
                else ambiguous.push_back(std::move(cand));
            }
        }

        // In a tree, after deleting its leaves the branching atoms form a path.
        // Hence only its two ends can have more than one candidate (or one
        // isolated branching atom can have three): at most four variants.
        vector<vector<int>> variants(1, mandatory);
        for (auto &cand : ambiguous) {
            vector<vector<int>> nv;
            for (auto &base : variants) for (int qid : cand) {
                auto z = base;
                z.push_back(qid);
                nv.push_back(std::move(z));
            }
            variants.swap(nv);
        }
        for (auto &forced : variants) {
            if (!make_r_path(forced)) continue;
            vector<ChosenToken> chosen;
            if (!path_dp(chosen)) continue;
            if (reconstruct(chosen)) return true;
        }
        return false;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int T;
    cin >> T;
    while (T--) {
        int n, m;
        cin >> n >> m;
        Solver sol(n, m);
        for (int i = 0; i < m; ++i) {
            int u, v;
            cin >> u >> v;
            --u, --v;
            sol.edges[i] = {u, v};
            sol.g[u].push_back({v, i});
            sol.g[v].push_back({u, i});
        }
        if (!sol.solve()) {
            cout << "No\n";
        } else {
            cout << "Yes\n";
            for (auto [x, y] : sol.answer) cout << x << ' ' << y << '\n';
        }
    }
    return 0;
}
