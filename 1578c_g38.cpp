#include <iostream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <queue>
#include <cmath>
#include <set>
#include <map>
#if (defined(__unix__) || defined(__APPLE__)) && !defined(_WIN32)
#include <sys/resource.h>
#define HAS_SYS_RESOURCE 1
#endif
using namespace std;
struct TreeEmbedder {
  int n;
  const vector<vector<int>>& adj;
  const vector<pair<int, int>>& edges;
  static const int OFFSET = 250000;
  static const int MAX_COORD = 500000;
  static int grid[2][MAX_COORD];
  static int grid_token[2][MAX_COORD];
  static int cur_token;
  TreeEmbedder(int n, const vector<vector<int>>& adj, const vector<pair<int, int>>& edges)
    : n(n), adj(adj), edges(edges) {}
  static void reset_grid() {
    cur_token++;
  }
  bool is_occupied(int r, int c) {
    int idx = c + OFFSET;
    if (idx < 0 || idx >= MAX_COORD) return true;
    return grid_token[r][idx] == cur_token;
  }
  void set_occupied(int r, int c, int u) {
    int idx = c + OFFSET;
    grid[r][idx] = u;
    grid_token[r][idx] = cur_token;
  }
  void clear_occupied(int r, int c) {
    int idx = c + OFFSET;
    grid_token[r][idx] = 0;
  }
  pair<int, int> bfs_farthest(int start, const vector<bool>& blocked = {}) {
    vector<int> dist(n, -1);
    queue<int> q;
    q.push(start);
    dist[start] = 0;
    int farthest = start;
    while (!q.empty()) {
      int u = q.front(); q.pop();
      if (dist[u] > dist[farthest]) farthest = u;
      for (int v : adj[u]) {
        if (!blocked.empty() && blocked[v]) continue;
        if (dist[v] == -1) {
          dist[v] = dist[u] + 1;
          q.push(v);
        }
      }
    }
    return {farthest, dist[farthest]};
  }
  vector<int> get_path(int start, int target) {
    vector<int> parent(n, -1);
    vector<bool> vis(n, false);
    queue<int> q;
    q.push(start);
    vis[start] = true;
    while (!q.empty()) {
      int u = q.front(); q.pop();
      if (u == target) break;
      for (int v : adj[u]) {
        if (!vis[v]) {
          vis[v] = true;
          parent[v] = u;
          q.push(v);
        }
      }
    }
    vector<int> path;
    int curr = target;
    while (curr != -1) {
      path.push_back(curr);
      curr = parent[curr];
    }
    return path; 
  }
  vector<int> trace_chain(int start, int p) {
    vector<int> chain;
    int curr = start, prev = p;
    while (curr != -1) {
      chain.push_back(curr);
      int nxt = -1, cnt = 0;
      for (int v : adj[curr]) {
        if (v != prev) {
          cnt++;
          nxt = v;
        }
      }
      if (cnt > 1) return {}; 
      prev = curr;
      curr = nxt;
    }
    return chain;
  }
  bool solve(vector<pair<int, int>>& result) {
    if (n <= 1) {
      result = {{0, 0}};
      return true;
    }
    if (n == 2) {
      result.assign(2, {0, 0});
      result[0] = {0, 0};
      result[1] = {0, 1};
      return true;
    }
    for (int i = 0; i < n; ++i) {
      if (adj[i].size() > 3) return false;
    }
    vector<int> cand_leaves;
    auto add_leaf = [&](int l) {
      if (l >= 0 && l < n && adj[l].size() <= 1) {
        if (find(cand_leaves.begin(), cand_leaves.end(), l) == cand_leaves.end()) {
          cand_leaves.push_back(l);
        }
      }
    };
    int p1 = bfs_farthest(0).first;
    int p2 = bfs_farthest(p1).first;
    int p3 = bfs_farthest(p2).first;
    add_leaf(p1);
    add_leaf(p2);
    add_leaf(p3);
    vector<int> deg3;
    for (int i = 0; i < n; ++i) {
      if (adj[i].size() == 3) deg3.push_back(i);
    }
    if (!deg3.empty()) {
      auto bfs_deg3 = [&](int start) {
        vector<int> dist(n, -1);
        vector<int> parent(n, -1);
        queue<int> q;
        q.push(start);
        dist[start] = 0;
        int farthest = start;
        while (!q.empty()) {
          int u = q.front(); q.pop();
          if (adj[u].size() == 3 && dist[u] > dist[farthest]) farthest = u;
          for (int v : adj[u]) {
            if (dist[v] == -1) {
              dist[v] = dist[u] + 1;
              parent[v] = u;
              q.push(v);
            }
          }
        }
        return make_pair(farthest, parent);
      };
      int d1 = bfs_deg3(deg3[0]).first;
      auto res2 = bfs_deg3(d1);
      int d2 = res2.first;
      auto& parent2 = res2.second;
      vector<int> core_path;
      int curr = d2;
      while (curr != -1) {
        core_path.push_back(curr);
        curr = parent2[curr];
      }
      vector<bool> in_core(n, false);
      for (int u : core_path) in_core[u] = true;
      for (int d : {d1, d2}) {
        for (int v : adj[d]) {
          if (!in_core[v]) {
            vector<bool> vis(n, false);
            vis[d] = true; vis[v] = true;
            queue<int> q; q.push(v);
            while (!q.empty()) {
              int u = q.front(); q.pop();
              if (adj[u].size() <= 1) add_leaf(u);
              for (int w : adj[u]) {
                if (!vis[w]) {
                  vis[w] = true;
                  q.push(w);
                }
              }
            }
          }
        }
      }
      int k_core = (int)core_path.size();
      vector<int> check_nodes;
      for (int i = 0; i < min(k_core, 3); ++i) {
        check_nodes.push_back(core_path[i]);
        check_nodes.push_back(core_path[k_core - 1 - i]);
      }
      for (int u : check_nodes) {
        for (int v : adj[u]) {
          if (!in_core[v]) {
            vector<bool> blk(n, false);
            blk[u] = true;
            int lf = bfs_farthest(v, blk).first;
            add_leaf(lf);
          }
        }
      }
    }
    set<pair<int, int>> seen_pairs;
    vector<vector<int>> unique_cands;
    for (size_t i = 0; i < cand_leaves.size(); ++i) {
      for (size_t j = 0; j < cand_leaves.size(); ++j) {
        if (i == j) continue;
        int l1 = cand_leaves[i], l2 = cand_leaves[j];
        if (!seen_pairs.count({l1, l2})) {
          seen_pairs.insert({l1, l2});
          auto p = get_path(l1, l2);
          if (p.size() >= 2) unique_cands.push_back(p);
        }
      }
    }
    for (const auto& path : unique_cands) {
      int m = path.size();
      vector<bool> p_set(n, false);
      for (int u : path) p_set[u] = true;
      vector<int> hang(m, -1);
      bool ok_hang = true;
      for (int i = 0; i < m; ++i) {
        int u = path[i];
        int cnt = 0;
        for (int v : adj[u]) {
          if (!p_set[v]) {
            cnt++;
            hang[i] = v;
          }
        }
        if (cnt > 1) { ok_hang = false; break; }
      }
      if (!ok_hang) continue;
      struct HangConfig {
        vector<int> arm1, arm2;
      };
      vector<vector<HangConfig>> hang_configs(m);
      for (int i = 0; i < m; ++i) {
        int h = hang[i];
        if (h == -1) {
          hang_configs[i].push_back({{}, {}});
          continue;
        }
        vector<int> ch;
        for (int v : adj[h]) {
          if (v != path[i]) ch.push_back(v);
        }
        if (ch.size() > 2) { ok_hang = false; break; }
        if (ch.empty()) {
          hang_configs[i].push_back({{}, {}});
        } else if (ch.size() == 1) {
          auto a1 = trace_chain(ch[0], h);
          if (a1.empty() && adj[ch[0]].size() > 1) { ok_hang = false; break; }
          hang_configs[i].push_back({a1, {}});
          hang_configs[i].push_back({{}, a1});
        } else if (ch.size() == 2) {
          auto a1 = trace_chain(ch[0], h);
          auto a2 = trace_chain(ch[1], h);
          if ((a1.empty() && adj[ch[0]].size() > 1) || (a2.empty() && adj[ch[1]].size() > 1)) {
            ok_hang = false; break;
          }
          if (a1.size() < a2.size()) swap(a1, a2);
          hang_configs[i].push_back({a1, a2});
          hang_configs[i].push_back({a2, a1});
        }
      }
      if (!ok_hang) continue;
      reset_grid();
      vector<pair<int, int>> pos(n, {-1, -1});
      int max_calls = m + 30000;
      auto dfs = [&](auto& self, int idx, int r, int c) -> bool {
        max_calls--;
        if (max_calls <= 0) return false;
        int u = path[idx];
        if (is_occupied(r, c)) return false;
        set_occupied(r, c, u);
        pos[u] = {r, c};
        int h = hang[idx];
        const auto& configs = hang_configs[idx];
        auto try_hang = [&](const HangConfig& cfg, int next_r, int next_c) -> bool {
          vector<pair<int, int>> placed_nodes;
          if (h != -1) {
            int hr = -1, hc = -1;
            pair<int, int> prev_pos = (idx == 0 ? make_pair(-1, -1) : pos[path[idx - 1]]);
            pair<int, int> cands[3] = {{1 - r, c}, {r, c + 1}, {r, c - 1}};
            for (int k = 0; k < 3; ++k) {
              int nr = cands[k].first, nc = cands[k].second;
              if (make_pair(nr, nc) != make_pair(next_r, next_c) &&
                make_pair(nr, nc) != prev_pos) {
                if (!is_occupied(nr, nc)) {
                  hr = nr; hc = nc;
                  break;
                }
              }
            }
            if (hr == -1) return false;
            const auto& arm1 = cfg.arm1;
            const auto& arm2 = cfg.arm2;
            if (hr == 1 - r && hc == c) {
              for (int step = 0; step < (int)arm1.size(); ++step) {
                if (is_occupied(hr, c - 1 - step)) return false;
              }
              for (int step = 0; step < (int)arm2.size(); ++step) {
                if (is_occupied(hr, c + 1 + step)) return false;
              }
              set_occupied(hr, hc, h);
              pos[h] = {hr, hc};
              placed_nodes.push_back({h, hr * 1000000 + (hc + OFFSET)});
              for (int step = 0; step < (int)arm1.size(); ++step) {
                int v = arm1[step], nc1 = c - 1 - step;
                set_occupied(hr, nc1, v);
                pos[v] = {hr, nc1};
                placed_nodes.push_back({v, hr * 1000000 + (nc1 + OFFSET)});
              }
              for (int step = 0; step < (int)arm2.size(); ++step) {
                int v = arm2[step], nc2 = c + 1 + step;
                set_occupied(hr, nc2, v);
                pos[v] = {hr, nc2};
                placed_nodes.push_back({v, hr * 1000000 + (nc2 + OFFSET)});
              }
            } else {
              if (!arm1.empty() && !arm2.empty()) return false;
              const auto& single_arm = (!arm1.empty() ? arm1 : arm2);
              int step_dir = hc - c;
              for (int step = 0; step < (int)single_arm.size(); ++step) {
                int nc = hc + (step + 1) * step_dir;
                if (is_occupied(hr, nc)) return false;
              }
              set_occupied(hr, hc, h);
              pos[h] = {hr, hc};
              placed_nodes.push_back({h, hr * 1000000 + (hc + OFFSET)});
              for (int step = 0; step < (int)single_arm.size(); ++step) {
                int v = single_arm[step], nc = hc + (step + 1) * step_dir;
                set_occupied(hr, nc, v);
                pos[v] = {hr, nc};
                placed_nodes.push_back({v, hr * 1000000 + (nc + OFFSET)});
              }
            }
          }
          if (idx + 1 == m) return true;
          if (self(self, idx + 1, next_r, next_c)) return true;
          for (auto& pn : placed_nodes) {
            int v = pn.first;
            clear_occupied(pos[v].first, pos[v].second);
            pos[v] = {-1, -1};
          }
          return false;
        };
        if (idx + 1 == m) {
          for (const auto& cfg : configs) {
            if (try_hang(cfg, -1, -1)) return true;
          }
        } else {
          pair<int, int> next_steps[2] = {{r, c + 1}, {1 - r, c}};
          for (int k = 0; k < 2; ++k) {
            int next_r = next_steps[k].first, next_c = next_steps[k].second;
            if (next_c == c && idx > 0 && pos[path[idx - 1]].second == c) {
              continue; 
            }
            for (const auto& cfg : configs) {
              if (try_hang(cfg, next_r, next_c)) return true;
            }
          }
        }
        clear_occupied(r, c);
        pos[u] = {-1, -1};
        return false;
      };
      if (dfs(dfs, 0, 0, 0)) {
        bool valid = true;
        set<pair<int, int>> seen;
        for (int i = 0; i < n; ++i) {
          if (pos[i].first < 0 || pos[i].first > 1) { valid = false; break; }
          if (seen.count(pos[i])) { valid = false; break; }
          seen.insert(pos[i]);
        }
        if (!valid) continue;
        for (const auto& e : edges) {
          int d = abs(pos[e.first].first - pos[e.second].first) +
              abs(pos[e.first].second - pos[e.second].second);
          if (d != 1) { valid = false; break; }
        }
        if (!valid) continue;
        result = pos;
        return true;
      }
    }
    return false;
  }
};
struct CactusSolver {
  int n, m;
  const vector<vector<int>>& adj;
  const vector<pair<int, int>>& edges;
  vector<vector<int>> cycle_bccs;
  vector<pair<int, int>> bridge_edges;
  int k;
  vector<vector<int>> cycle_rings;
  vector<int> cycle_of_node;
  vector<int> cycle_order;
  vector<int> u_prev_cycle, u_next_cycle;
  vector<int> bct_path;
  vector<int> pos_in_bct;
  vector<vector<int>> cand_rungs;
  CactusSolver(int n, const vector<vector<int>>& adj, const vector<pair<int, int>>& edges)
    : n(n), m(edges.size()), adj(adj), edges(edges), cycle_of_node(n, -1) {}
  bool find_bccs() {
    vector<int> dfn(n, 0), low(n, 0);
    int timer = 0;
    vector<pair<int, int>> st;
    bool bcc_valid = true;
    auto dfs_bcc = [&](auto& self, int u, int p) -> void {
      dfn[u] = low[u] = ++timer;
      for (int v : adj[u]) {
        if (v == p) continue;
        if (dfn[v]) {
          low[u] = min(low[u], dfn[v]);
          if (dfn[v] < dfn[u]) {
            st.push_back({u, v});
          }
        } else {
          st.push_back({u, v});
          self(self, v, u);
          low[u] = min(low[u], low[v]);
          if (low[v] >= dfn[u]) {
            vector<pair<int, int>> cur_edges;
            while (true) {
              auto e = st.back();
              st.pop_back();
              cur_edges.push_back(e);
              if (e.first == u && e.second == v) break;
            }
            vector<int> cur_nodes;
            for (auto& e : cur_edges) {
              cur_nodes.push_back(e.first);
              cur_nodes.push_back(e.second);
            }
            sort(cur_nodes.begin(), cur_nodes.end());
            cur_nodes.erase(unique(cur_nodes.begin(), cur_nodes.end()), cur_nodes.end());
            if (cur_edges.size() == 1) {
              bridge_edges.push_back(cur_edges[0]);
            } else if (cur_edges.size() == cur_nodes.size() && cur_nodes.size() >= 3) {
              if (cur_nodes.size() % 2 != 0 || cur_nodes.size() < 4) {
                bcc_valid = false;
              }
              cycle_bccs.push_back(cur_nodes);
            } else {
              bcc_valid = false;
            }
          }
        }
      }
    };
    for (int i = 0; i < n; ++i) {
      if (!dfn[i]) dfs_bcc(dfs_bcc, i, -1);
    }
    if (!bcc_valid) return false;
    k = cycle_bccs.size();
    vector<int> v_cnt(n, 0);
    for (int i = 0; i < k; ++i) {
      for (int u : cycle_bccs[i]) {
        v_cnt[u]++;
        if (v_cnt[u] > 1) return false;
        cycle_of_node[u] = i;
      }
    }
    return true;
  }
  bool build_bct() {
    if (k == 1) {
      cycle_order = {0};
      bct_path = {n + 0};
      pos_in_bct.assign(k, 0);
      u_prev_cycle.assign(k, -1);
      u_next_cycle.assign(k, -1);
      return true;
    }
    int bct_size = n + k;
    vector<vector<int>> bct_adj(bct_size);
    for (int i = 0; i < k; ++i) {
      int c_node = n + i;
      for (int u : cycle_bccs[i]) {
        bct_adj[u].push_back(c_node);
        bct_adj[c_node].push_back(u);
      }
    }
    for (auto& e : bridge_edges) {
      bct_adj[e.first].push_back(e.second);
      bct_adj[e.second].push_back(e.first);
    }
    auto bct_bfs = [&](int start) -> vector<int> {
      vector<int> dist(bct_size, -1);
      queue<int> q;
      q.push(start);
      dist[start] = 0;
      while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : bct_adj[u]) {
          if (dist[v] == -1) {
            dist[v] = dist[u] + 1;
            q.push(v);
          }
        }
      }
      return dist;
    };
    auto d0 = bct_bfs(n + 0);
    int c_start = 0;
    for (int i = 0; i < k; ++i) {
      if (d0[n + i] > d0[n + c_start]) c_start = i;
    }
    auto d1 = bct_bfs(n + c_start);
    int c_end = 0;
    for (int i = 0; i < k; ++i) {
      if (d1[n + i] > d1[n + c_end]) c_end = i;
    }
    vector<int> parent(bct_size, -1);
    vector<bool> vis(bct_size, false);
    queue<int> q;
    q.push(n + c_start);
    vis[n + c_start] = true;
    while (!q.empty()) {
      int u = q.front(); q.pop();
      for (int v : bct_adj[u]) {
        if (!vis[v]) {
          vis[v] = true;
          parent[v] = u;
          q.push(v);
        }
      }
    }
    bct_path.clear();
    int curr = n + c_end;
    while (curr != -1) {
      bct_path.push_back(curr);
      curr = parent[curr];
    }
    reverse(bct_path.begin(), bct_path.end());
    return update_bct_order();
  }
  bool update_bct_order() {
    cycle_order.clear();
    for (int x : bct_path) {
      if (x >= n) cycle_order.push_back(x - n);
    }
    if ((int)cycle_order.size() != k) return false;
    pos_in_bct.assign(k, -1);
    u_prev_cycle.assign(k, -1);
    u_next_cycle.assign(k, -1);
    for (int idx = 0; idx < (int)bct_path.size(); ++idx) {
      int x = bct_path[idx];
      if (x >= n) {
        int c_id = x - n;
        pos_in_bct[c_id] = idx;
        if (idx > 0) u_prev_cycle[c_id] = bct_path[idx - 1];
        if (idx + 1 < (int)bct_path.size()) u_next_cycle[c_id] = bct_path[idx + 1];
      }
    }
    return true;
  }
  bool compute_rings_and_cand_rungs() {
    cycle_rings.assign(k, {});
    for (int c_idx = 0; c_idx < k; ++c_idx) {
      const auto& cnodes = cycle_bccs[c_idx];
      int c_len = cnodes.size();
      if (c_len % 2 != 0 || c_len < 4) return false;
      vector<bool> in_c(n, false);
      for (int u : cnodes) in_c[u] = true;
      int start = cnodes[0];
      vector<int> ring = {start};
      int prev = -1, cur = start;
      while ((int)ring.size() < c_len) {
        int nxt = -1;
        for (int v : adj[cur]) {
          if (in_c[v] && v != prev) {
            nxt = v;
            break;
          }
        }
        if (nxt == -1) return false;
        ring.push_back(nxt);
        prev = cur;
        cur = nxt;
      }
      bool closed = false;
      for (int v : adj[ring.back()]) {
        if (v == start) { closed = true; break; }
      }
      if (!closed) return false;
      cycle_rings[c_idx] = ring;
    }
    cand_rungs.assign(k, {});
    for (int c_id : cycle_order) {
      const auto& ring = cycle_rings[c_id];
      int c_len = ring.size();
      int L = c_len / 2;
      vector<int> outside_nodes;
      for (int u : ring) {
        bool has_out = false;
        for (int v : adj[u]) {
          if (cycle_of_node[v] != c_id) {
            has_out = true;
            break;
          }
        }
        if (has_out) outside_nodes.push_back(u);
      }
      int u_prev = u_prev_cycle[c_id];
      int u_next = u_next_cycle[c_id];
      for (int i = 0; i < c_len; ++i) {
        int p1 = i, p2 = (i + 1) % c_len;
        int p3 = (i + L) % c_len, p4 = (i + L + 1) % c_len;
        int r1_a = ring[p1], r1_b = ring[p2];
        int r2_a = ring[p3], r2_b = ring[p4];
        bool all_in = true;
        for (int u : outside_nodes) {
          if (u != r1_a && u != r1_b && u != r2_a && u != r2_b) {
            all_in = false;
            break;
          }
        }
        if (!all_in) continue;
        if (u_prev != -1 && u_prev != r1_a && u_prev != r1_b) continue;
        if (u_next != -1 && u_next != r2_a && u_next != r2_b) continue;
        cand_rungs[c_id].push_back(i);
      }
      if (cand_rungs[c_id].empty()) return false;
    }
    return true;
  }
  pair<bool, vector<int>> trace_simple_chain(int start_node, int p, const vector<bool>* in_vis = nullptr) {
    vector<int> nodes;
    int curr = start_node, prev = p;
    while (curr != -1) {
      nodes.push_back(curr);
      vector<int> nxt;
      for (int v : adj[curr]) {
        if (v == prev) continue;
        if (in_vis && !(*in_vis)[v]) continue;
        nxt.push_back(v);
      }
      if (nxt.size() > 1) return {false, {}};
      prev = curr;
      curr = nxt.empty() ? -1 : nxt[0];
    }
    return {true, nodes};
  }
  bool solve_end_tree_dfs(int root_node, int parent_node, const vector<int>& chain_v,
                          vector<pair<int, pair<int, int>>>& placed_nodes) {
    placed_nodes.clear();
    int len_v = chain_v.size();
    vector<bool> vis(n, false);
    vis[root_node] = true;
    vis[parent_node] = true;
    queue<int> q;
    q.push(root_node);
    vector<int> tree_nodes;
    vector<int> parent(n, -1);
    parent[root_node] = parent_node;
    while (!q.empty()) {
      int u = q.front(); q.pop();
      tree_nodes.push_back(u);
      for (int v : adj[u]) {
        if (!vis[v]) {
          vis[v] = true;
          parent[v] = u;
          q.push(v);
        }
      }
    }
    vector<bool> in_t(n, false);
    for (int u : tree_nodes) in_t[u] = true;
    if (tree_nodes.size() == 1) {
      for (int k = 0; k < len_v; ++k) {
        placed_nodes.push_back({chain_v[k], {1, 1 + k}});
      }
      placed_nodes.push_back({root_node, {0, 1}});
      return true;
    }
    vector<int> dist(n, -1);
    queue<int> bq;
    bq.push(root_node);
    dist[root_node] = 0;
    int farthest = root_node;
    while (!bq.empty()) {
      int u = bq.front(); bq.pop();
      if (dist[u] > dist[farthest]) farthest = u;
      for (int v : adj[u]) {
        if (in_t[v] && dist[v] == -1) {
          dist[v] = dist[u] + 1;
          parent[v] = u;
          bq.push(v);
        }
      }
    }
    vector<int> cand_leaves = {farthest};
    int p_far = parent[farthest];
    if (p_far != -1 && p_far != parent_node) {
      for (int v : adj[p_far]) {
        if (in_t[v] && v != parent[p_far] && v != farthest) {
          cand_leaves.push_back(v);
        }
      }
    }
    int far_d3 = -1;
    for (int u : tree_nodes) {
      int deg = 0;
      for (int v : adj[u]) if (in_t[v]) deg++;
      if (deg == 3) {
        if (far_d3 == -1 || dist[u] > dist[far_d3]) {
          far_d3 = u;
        }
      }
    }
    if (far_d3 != -1) {
      int blk = parent[far_d3];
      queue<int> dq;
      vector<bool> dvis(n, false);
      dvis[far_d3] = true;
      if (blk != -1 && blk != parent_node) dvis[blk] = true;
      dq.push(far_d3);
      while (!dq.empty()) {
        int u = dq.front(); dq.pop();
        int ch_cnt = 0;
        for (int v : adj[u]) {
          if (in_t[v] && !dvis[v]) {
            dvis[v] = true;
            dq.push(v);
            ch_cnt++;
          }
        }
        if (ch_cnt == 0) cand_leaves.push_back(u);
      }
    }
    sort(cand_leaves.begin(), cand_leaves.end());
    cand_leaves.erase(unique(cand_leaves.begin(), cand_leaves.end()), cand_leaves.end());
    for (int leaf : cand_leaves) {
      vector<int> spine;
      int curr = leaf;
      while (curr != parent_node) {
        spine.push_back(curr);
        curr = parent[curr];
      }
      reverse(spine.begin(), spine.end());
      if (spine.empty() || spine[0] != root_node) continue;
      int m = spine.size();
      vector<bool> in_sp(n, false);
      for (int u : spine) in_sp[u] = true;
      vector<bool> has_branch(m, false);
      vector<int> branch_h(m, -1);
      vector<vector<int>> branch_arm1(m);
      vector<vector<int>> branch_arm2(m);
      bool spine_valid = true;
      for (int j = 0; j < m; ++j) {
        int u = spine[j];
        vector<int> outs;
        for (int v : adj[u]) {
          if (in_t[v] && !in_sp[v]) outs.push_back(v);
        }
        if (outs.size() > 1) { spine_valid = false; break; }
        if (outs.size() == 1) {
          int h = outs[0];
          vector<int> h_nbrs;
          for (int v : adj[h]) {
            if (in_t[v] && v != u) h_nbrs.push_back(v);
          }
          if (h_nbrs.size() > 2) { spine_valid = false; break; }
          vector<vector<int>> arms;
          for (int hc : h_nbrs) {
            auto [ok_c, chain] = trace_simple_chain(hc, h, &in_t);
            if (!ok_c) { spine_valid = false; break; }
            arms.push_back(chain);
          }
          if (!spine_valid) break;
          has_branch[j] = true;
          branch_h[j] = h;
          if (arms.size() > 0) branch_arm1[j] = arms[0];
          if (arms.size() > 1) branch_arm2[j] = arms[1];
          if (branch_arm1[j].size() < branch_arm2[j].size()) swap(branch_arm1[j], branch_arm2[j]);
        }
      }
      if (!spine_valid) continue;
      int accounted = m;
      for (int j = 0; j < m; ++j) {
        if (has_branch[j]) {
          accounted += 1 + branch_arm1[j].size() + branch_arm2[j].size();
        }
      }
      if (accounted != (int)tree_nodes.size()) continue;
      int max_col = (int)tree_nodes.size() + len_v + 100;
      vector<vector<bool>> occ(2, vector<bool>(max_col, false));
      occ[0][0] = true;
      occ[1][0] = true;
      for (int k = 0; k < len_v; ++k) occ[1][1 + k] = true;
      occ[0][1] = true;
      struct Item { int u, r, c; };
      vector<Item> history = {{root_node, 0, 1}};
      int dfs_calls = 0;
      int max_calls = m + 30000;
      auto dfs = [&](auto& self, int idx, int r, int c, bool arrived_vert) -> bool {
        if (++dfs_calls > max_calls) return false;
        if (idx == m - 1) return true;
        int nxt_u = spine[idx + 1];
        bool u_has_b = has_branch[idx];
        bool nxt_has_b = has_branch[idx + 1];
        int nxt_c = c + 1;
        if (nxt_c < max_col && !occ[r][nxt_c]) {
          if (!u_has_b) {
            occ[r][nxt_c] = true; history.push_back({nxt_u, r, nxt_c});
            if (self(self, idx + 1, r, nxt_c, false)) return true;
            history.pop_back();
            occ[r][nxt_c] = false;
          } else {
            int h = branch_h[idx];
            const auto& arm1 = branch_arm1[idx];
            const auto& arm2 = branch_arm2[idx];
            if (arrived_vert) {
              if (arm2.empty()) {
                int hc = c - 1;
                if (hc > 0 && hc < max_col && !occ[r][hc]) {
                  bool ok_arm = true;
                  for (int k = 0; k < (int)arm1.size(); ++k) {
                    int ac = hc - 1 - k;
                    if (ac <= 0 || ac >= max_col || occ[r][ac]) { ok_arm = false; break; }
                  }
                  if (ok_arm) {
                    int hist_start = history.size();
                    occ[r][nxt_c] = true; history.push_back({nxt_u, r, nxt_c});
                    occ[r][hc] = true; history.push_back({h, r, hc});
                    for (int k = 0; k < (int)arm1.size(); ++k) {
                      occ[r][hc - 1 - k] = true; history.push_back({arm1[k], r, hc - 1 - k});
                    }
                    if (self(self, idx + 1, r, nxt_c, false)) return true;
                    while ((int)history.size() > hist_start) {
                      auto it = history.back(); history.pop_back();
                      occ[it.r][it.c] = false;
                    }
                  }
                }
              }
            } else {
              if (!occ[1 - r][c]) {
                for (int pass = 0; pass < 2; ++pass) {
                  const auto& aL = (pass == 0 ? arm1 : arm2);
                  const auto& aR = (pass == 0 ? arm2 : arm1);
                  if (pass == 1 && arm1 == arm2) break;
                  bool ok_L = true;
                  for (int k = 0; k < (int)aL.size(); ++k) {
                    int col_k = c - 1 - k;
                    if (col_k <= 0 || col_k >= max_col || occ[1 - r][col_k]) { ok_L = false; break; }
                  }
                  bool ok_R = true;
                  for (int k = 0; k < (int)aR.size(); ++k) {
                    int col_k = c + 1 + k;
                    if (col_k >= max_col || occ[1 - r][col_k]) { ok_R = false; break; }
                  }
                  if (ok_L && ok_R) {
                    int hist_start = history.size();
                    occ[r][nxt_c] = true; history.push_back({nxt_u, r, nxt_c});
                    occ[1 - r][c] = true; history.push_back({h, 1 - r, c});
                    for (int k = 0; k < (int)aL.size(); ++k) {
                      occ[1 - r][c - 1 - k] = true; history.push_back({aL[k], 1 - r, c - 1 - k});
                    }
                    for (int k = 0; k < (int)aR.size(); ++k) {
                      occ[1 - r][c + 1 + k] = true; history.push_back({aR[k], 1 - r, c + 1 + k});
                    }
                    if (self(self, idx + 1, r, nxt_c, false)) return true;
                    while ((int)history.size() > hist_start) {
                      auto it = history.back(); history.pop_back();
                      occ[it.r][it.c] = false;
                    }
                  }
                }
              }
            }
          }
        }
        if (!arrived_vert && (u_has_b || nxt_has_b) && idx > 0 && !occ[1 - r][c]) {
          bool u_ok = true;
          int h_u = -1;
          if (u_has_b) {
            if (!branch_arm2[idx].empty()) {
              u_ok = false;
            } else {
              h_u = branch_h[idx];
              const auto& arm = branch_arm1[idx];
              int hc = c + 1;
              if (hc >= max_col || occ[r][hc]) u_ok = false;
              for (int k = 0; k < (int)arm.size(); ++k) {
                int ac = hc + 1 + k;
                if (ac >= max_col || occ[r][ac]) { u_ok = false; break; }
              }
            }
          }
          if (u_ok) {
            int hist_start = history.size();
            occ[1 - r][c] = true; history.push_back({nxt_u, 1 - r, c});
            if (u_has_b) {
              int hc = c + 1;
              occ[r][hc] = true; history.push_back({h_u, r, hc});
              const auto& arm = branch_arm1[idx];
              for (int k = 0; k < (int)arm.size(); ++k) {
                occ[r][hc + 1 + k] = true; history.push_back({arm[k], r, hc + 1 + k});
              }
            }
            if (self(self, idx + 1, 1 - r, c, true)) return true;
            while ((int)history.size() > hist_start) {
              auto it = history.back(); history.pop_back();
              occ[it.r][it.c] = false;
            }
          }
        }
        return false;
      };
      if (dfs(dfs, 0, 0, 1, false)) {
        for (int k = 0; k < len_v; ++k) {
          placed_nodes.push_back({chain_v[k], {1, 1 + k}});
        }
        for (const auto& item : history) {
          placed_nodes.push_back({item.u, {item.r, item.c}});
        }
        return true;
      }
    }
    return false;
  }
  bool check_left_end(int p0) {
    int c0_id = cycle_order[0];
    const auto& ring0 = cycle_rings[c0_id];
    u_L_0_cand = ring0[(p0 + 1) % ring0.size()];
    v_L_0_cand = ring0[p0];
    for (bool swap_left : {false, true}) {
      int u_sp = (swap_left ? v_L_0_cand : u_L_0_cand);
      int v_ch = (swap_left ? u_L_0_cand : v_L_0_cand);
      int len_v = 0;
      vector<int> chain_v;
      for (int v : adj[v_ch]) {
        if (cycle_of_node[v] != c0_id) {
          auto [ok, c] = trace_simple_chain(v, v_ch);
          if (!ok) { len_v = -1; break; }
          chain_v = c;
          len_v = c.size();
          break;
        }
      }
      if (len_v == -1) continue;
      int u_sp_out = -1;
      for (int v : adj[u_sp]) {
        if (cycle_of_node[v] != c0_id) {
          u_sp_out = v;
          break;
        }
      }
      if (u_sp_out == -1) return true;
      vector<pair<int, pair<int, int>>> dummy;
      if (solve_end_tree_dfs(u_sp_out, u_sp, chain_v, dummy)) return true;
    }
    return false;
  }
  int u_L_0_cand, v_L_0_cand;
  struct SegmentPlacement {
    bool ok = false;
    int r_enter = 0;
    int c_enter = 0;
    vector<pair<int, pair<int, int>>> node_pos;
  };
  vector<map<pair<int, int>, SegmentPlacement>> seg_cache;
  bool solve_segment(int ci, int p_curr, int p_next, SegmentPlacement& res) {
    res.ok = false;
    res.node_pos.clear();
    int c_curr = cycle_order[ci];
    int c_next = cycle_order[ci + 1];
    int u_exit = u_next_cycle[c_curr];
    int u_enter = u_prev_cycle[c_next];
    const auto& ring_curr = cycle_rings[c_curr];
    int L_curr = ring_curr.size() / 2;
    int r2_a = ring_curr[(p_curr + L_curr) % ring_curr.size()];
    int r2_b = ring_curr[(p_curr + L_curr + 1) % ring_curr.size()];
    int v_exit_other = (u_exit == r2_a ? r2_b : r2_a);
    vector<int> v_R_chain;
    for (int v : adj[v_exit_other]) {
      if (cycle_of_node[v] != c_curr) {
        auto [ok, c] = trace_simple_chain(v, v_exit_other);
        if (!ok) return false;
        v_R_chain = c;
        break;
      }
    }
    int R_len = v_R_chain.size();
    int t1 = pos_in_bct[c_curr] + 1;
    int t2 = pos_in_bct[c_next] - 1;
    int m_len = t2 - t1;
    if (m_len < 1) return false;
    vector<int> p_mid;
    for (int t = t1; t <= t2; ++t) p_mid.push_back(bct_path[t]);
    const auto& ring_next = cycle_rings[c_next];
    int r1_a = ring_next[(p_next + 1) % ring_next.size()];
    int r1_b = ring_next[p_next];
    int v_enter_other = (u_enter == r1_a ? r1_b : r1_a);
    vector<int> v_L_chain;
    for (int v : adj[v_enter_other]) {
      if (cycle_of_node[v] != c_next) {
        auto [ok, c] = trace_simple_chain(v, v_enter_other);
        if (!ok) return false;
        v_L_chain = c;
        break;
      }
    }
    int L_len = v_L_chain.size();
    vector<bool> has_branch(m_len + 1, false);
    vector<int> branch_h(m_len + 1, -1);
    vector<vector<int>> branch_arm1(m_len + 1);
    vector<vector<int>> branch_arm2(m_len + 1);
    for (int j = 1; j < m_len; ++j) {
      int w = p_mid[j];
      int h = -1;
      for (int v : adj[w]) {
        if (v != p_mid[j - 1] && v != p_mid[j + 1]) {
          h = v;
          break;
        }
      }
      if (h != -1) {
        vector<int> h_ch;
        for (int v : adj[h]) {
          if (v != w) h_ch.push_back(v);
        }
        if (h_ch.size() > 2) return false;
        vector<vector<int>> arms;
        for (int hc : h_ch) {
          auto [ok, arm] = trace_simple_chain(hc, h);
          if (!ok) return false;
          arms.push_back(arm);
        }
        has_branch[j] = true;
        branch_h[j] = h;
        if (arms.size() > 0) branch_arm1[j] = arms[0];
        if (arms.size() > 1) branch_arm2[j] = arms[1];
        if (branch_arm1[j].size() < branch_arm2[j].size()) swap(branch_arm1[j], branch_arm2[j]);
      }
    }
    int total_arm_len = 0;
    for (int j = 1; j < m_len; ++j) {
      total_arm_len += (int)branch_arm1[j].size() + (int)branch_arm2[j].size();
    }
    int max_col = m_len + R_len + L_len + total_arm_len + 100;
    vector<vector<bool>> occ(2, vector<bool>(max_col, false));
    occ[0][0] = true;
    occ[1][0] = true;
    for (int k = 0; k < R_len; ++k) {
      if (1 + k >= max_col) return false;
      occ[1][1 + k] = true;
    }
    struct PlacedItem {
      int u;
      int r, c;
    };
    vector<PlacedItem> history;
    int dfs_calls = 0;
    int max_calls = m_len + 30000;
    auto dfs = [&](auto& self, int idx, int r, int c, bool arrived_vert) -> bool {
      if (++dfs_calls > max_calls) return false;
      if (idx == m_len - 1) {
        int nxt_c = c + 1;
        if (nxt_c >= max_col) return false;
        if (occ[r][nxt_c] || occ[1 - r][nxt_c]) return false;
        for (int k = 0; k < L_len; ++k) {
          int col_k = nxt_c - 1 - k;
          if (col_k <= 0 || col_k >= max_col || occ[1 - r][col_k]) return false;
        }
        if (!has_branch[idx]) {
          res.ok = true;
          res.r_enter = r;
          res.c_enter = nxt_c;
          for (auto& item : history) {
            res.node_pos.push_back({item.u, {item.r, item.c}});
          }
          for (int k = 0; k < R_len; ++k) {
            res.node_pos.push_back({v_R_chain[k], {1, 1 + k}});
          }
          for (int k = 0; k < L_len; ++k) {
            res.node_pos.push_back({v_L_chain[k], {1 - r, nxt_c - 1 - k}});
          }
          return true;
        } else {
          int h = branch_h[idx];
          const auto& arm1 = branch_arm1[idx];
          const auto& arm2 = branch_arm2[idx];
          if (arrived_vert) {
            if (!arm2.empty()) return false;
            int hc = c - 1;
            if (hc <= 0 || hc >= max_col || occ[r][hc]) return false;
            for (int k = 0; k < (int)arm1.size(); ++k) {
              int ac = hc - 1 - k;
              if (ac <= 0 || ac >= max_col || occ[r][ac]) return false;
            }
            res.ok = true;
            res.r_enter = r;
            res.c_enter = nxt_c;
            for (auto& item : history) {
              res.node_pos.push_back({item.u, {item.r, item.c}});
            }
            res.node_pos.push_back({h, {r, hc}});
            for (int k = 0; k < (int)arm1.size(); ++k) {
              res.node_pos.push_back({arm1[k], {r, hc - 1 - k}});
            }
            for (int k = 0; k < R_len; ++k) {
              res.node_pos.push_back({v_R_chain[k], {1, 1 + k}});
            }
            for (int k = 0; k < L_len; ++k) {
              res.node_pos.push_back({v_L_chain[k], {1 - r, nxt_c - 1 - k}});
            }
            return true;
          } else {
            if (L_len > 0) return false;
            if (occ[1 - r][c]) return false;
            for (int pass = 0; pass < 2; ++pass) {
              const auto& aL = (pass == 0 ? arm1 : arm2);
              const auto& aR = (pass == 0 ? arm2 : arm1);
              if (pass == 1 && arm1 == arm2) break;
              if (!aR.empty()) continue;
              bool ok_L = true;
              for (int k = 0; k < (int)aL.size(); ++k) {
                int col_k = c - 1 - k;
                if (col_k <= 0 || col_k >= max_col || occ[1 - r][col_k]) {
                  ok_L = false;
                  break;
                }
              }
              if (ok_L) {
                res.ok = true;
                res.r_enter = r;
                res.c_enter = nxt_c;
                for (auto& item : history) {
                  res.node_pos.push_back({item.u, {item.r, item.c}});
                }
                res.node_pos.push_back({h, {1 - r, c}});
                for (int k = 0; k < (int)aL.size(); ++k) {
                  res.node_pos.push_back({aL[k], {1 - r, c - 1 - k}});
                }
                for (int k = 0; k < R_len; ++k) {
                  res.node_pos.push_back({v_R_chain[k], {1, 1 + k}});
                }
                for (int k = 0; k < L_len; ++k) {
                  res.node_pos.push_back({v_L_chain[k], {1 - r, nxt_c - 1 - k}});
                }
                return true;
              }
            }
            return false;
          }
        }
      }
      int nxt_u = p_mid[idx + 1];
      bool u_has_b = has_branch[idx];
      bool nxt_has_b = has_branch[idx + 1];
      int nxt_c = c + 1;
      if (nxt_c < max_col && !occ[r][nxt_c]) {
        if (!u_has_b) {
          occ[r][nxt_c] = true;
          history.push_back({nxt_u, r, nxt_c});
          if (self(self, idx + 1, r, nxt_c, false)) return true;
          history.pop_back();
          occ[r][nxt_c] = false;
        } else {
          int h = branch_h[idx];
          const auto& arm1 = branch_arm1[idx];
          const auto& arm2 = branch_arm2[idx];
          if (arrived_vert) {
            if (arm2.empty()) {
              int hc = c - 1;
              if (hc > 0 && hc < max_col && !occ[r][hc]) {
                bool ok_arm = true;
                for (int k = 0; k < (int)arm1.size(); ++k) {
                  int ac = hc - 1 - k;
                  if (ac <= 0 || ac >= max_col || occ[r][ac]) {
                    ok_arm = false;
                    break;
                  }
                }
                if (ok_arm) {
                  int hist_start = history.size();
                  occ[r][nxt_c] = true; history.push_back({nxt_u, r, nxt_c});
                  occ[r][hc] = true; history.push_back({h, r, hc});
                  for (int k = 0; k < (int)arm1.size(); ++k) {
                    occ[r][hc - 1 - k] = true;
                    history.push_back({arm1[k], r, hc - 1 - k});
                  }
                  if (self(self, idx + 1, r, nxt_c, false)) return true;
                  while ((int)history.size() > hist_start) {
                    auto item = history.back();
                    history.pop_back();
                    occ[item.r][item.c] = false;
                  }
                }
              }
            }
          } else {
            if (!occ[1 - r][c]) {
              for (int pass = 0; pass < 2; ++pass) {
                const auto& aL = (pass == 0 ? arm1 : arm2);
                const auto& aR = (pass == 0 ? arm2 : arm1);
                if (pass == 1 && arm1 == arm2) break;
                bool ok_L = true;
                for (int k = 0; k < (int)aL.size(); ++k) {
                  int col_k = c - 1 - k;
                  if (col_k <= 0 || col_k >= max_col || occ[1 - r][col_k]) {
                    ok_L = false; break;
                  }
                }
                bool ok_R = true;
                for (int k = 0; k < (int)aR.size(); ++k) {
                  int col_k = c + 1 + k;
                  if (col_k >= max_col || occ[1 - r][col_k]) {
                    ok_R = false; break;
                  }
                }
                if (ok_L && ok_R) {
                  int hist_start = history.size();
                  occ[r][nxt_c] = true; history.push_back({nxt_u, r, nxt_c});
                  occ[1 - r][c] = true; history.push_back({h, 1 - r, c});
                  for (int k = 0; k < (int)aL.size(); ++k) {
                    occ[1 - r][c - 1 - k] = true;
                    history.push_back({aL[k], 1 - r, c - 1 - k});
                  }
                  for (int k = 0; k < (int)aR.size(); ++k) {
                    occ[1 - r][c + 1 + k] = true;
                    history.push_back({aR[k], 1 - r, c + 1 + k});
                  }
                  if (self(self, idx + 1, r, nxt_c, false)) return true;
                  while ((int)history.size() > hist_start) {
                    auto item = history.back();
                    history.pop_back();
                    occ[item.r][item.c] = false;
                  }
                }
              }
            }
          }
        }
      }
      if (!arrived_vert && (u_has_b || nxt_has_b) && idx > 0 && idx + 1 < m_len) {
        if (!occ[1 - r][c]) {
          bool u_ok = true;
          int h_u = -1;
          if (u_has_b) {
            if (!branch_arm2[idx].empty()) {
              u_ok = false;
            } else {
              h_u = branch_h[idx];
              const auto& arm = branch_arm1[idx];
              int hc = c + 1;
              if (hc >= max_col || occ[r][hc]) u_ok = false;
              for (int k = 0; k < (int)arm.size(); ++k) {
                int ac = hc + 1 + k;
                if (ac >= max_col || occ[r][ac]) { u_ok = false; break; }
              }
            }
          }
          if (u_ok) {
            int hist_start = history.size();
            occ[1 - r][c] = true; history.push_back({nxt_u, 1 - r, c});
            if (u_has_b) {
              int hc = c + 1;
              occ[r][hc] = true; history.push_back({h_u, r, hc});
              const auto& arm = branch_arm1[idx];
              for (int k = 0; k < (int)arm.size(); ++k) {
                occ[r][hc + 1 + k] = true;
                history.push_back({arm[k], r, hc + 1 + k});
              }
            }
            if (self(self, idx + 1, 1 - r, c, true)) return true;
            while ((int)history.size() > hist_start) {
              auto item = history.back();
              history.pop_back();
              occ[item.r][item.c] = false;
            }
          }
        }
      }
      return false;
    };
    return dfs(dfs, 0, 0, 0, false);
  }
  bool check_segment(int ci, int p_curr, int p_next) {
    auto it = seg_cache[ci].find({p_curr, p_next});
    if (it != seg_cache[ci].end()) return it->second.ok;
    SegmentPlacement sp;
    bool ok = solve_segment(ci, p_curr, p_next, sp);
    sp.ok = ok;
    seg_cache[ci][{p_curr, p_next}] = sp;
    return ok;
  }
  bool check_right_end(int p_last) {
    int c_last = cycle_order.back();
    const auto& ring_last = cycle_rings[c_last];
    int L_last = ring_last.size() / 2;
    int u_R_last = ring_last[(p_last + L_last) % ring_last.size()];
    int v_R_last = ring_last[(p_last + L_last + 1) % ring_last.size()];
    for (bool swap_right : {false, true}) {
      int u_sp = (swap_right ? v_R_last : u_R_last);
      int v_ch = (swap_right ? u_R_last : v_R_last);
      int len_v = 0;
      vector<int> chain_v;
      for (int v : adj[v_ch]) {
        if (cycle_of_node[v] != c_last) {
          auto [ok, c] = trace_simple_chain(v, v_ch);
          if (!ok) { len_v = -1; break; }
          chain_v = c;
          len_v = c.size();
          break;
        }
      }
      if (len_v == -1) continue;
      int u_sp_out = -1;
      for (int v : adj[u_sp]) {
        if (cycle_of_node[v] != c_last) {
          u_sp_out = v;
          break;
        }
      }
      if (u_sp_out == -1) return true;
      vector<pair<int, pair<int, int>>> dummy;
      if (solve_end_tree_dfs(u_sp_out, u_sp, chain_v, dummy)) return true;
    }
    return false;
  }
  bool solve_with_current_order(vector<pair<int, int>>& result) {
    if (!compute_rings_and_cand_rungs()) return false;
    seg_cache.assign(k, {});
    vector<vector<bool>> dp(k);
    vector<vector<int>> parent_dp(k);
    for (int i = 0; i < k; ++i) {
      dp[i].assign(cand_rungs[cycle_order[i]].size(), false);
      parent_dp[i].assign(cand_rungs[cycle_order[i]].size(), -1);
    }
    for (int p_idx = 0; p_idx < (int)cand_rungs[cycle_order[0]].size(); ++p_idx) {
      int p0 = cand_rungs[cycle_order[0]][p_idx];
      if (check_left_end(p0)) dp[0][p_idx] = true;
    }
    for (int ci = 0; ci < k - 1; ++ci) {
      int c_curr_id = cycle_order[ci];
      int c_next_id = cycle_order[ci + 1];
      for (int p_curr_idx = 0; p_curr_idx < (int)cand_rungs[c_curr_id].size(); ++p_curr_idx) {
        if (!dp[ci][p_curr_idx]) continue;
        int p_curr = cand_rungs[c_curr_id][p_curr_idx];
        for (int p_next_idx = 0; p_next_idx < (int)cand_rungs[c_next_id].size(); ++p_next_idx) {
          int p_next = cand_rungs[c_next_id][p_next_idx];
          if (check_segment(ci, p_curr, p_next)) {
            dp[ci + 1][p_next_idx] = true;
            parent_dp[ci + 1][p_next_idx] = p_curr_idx;
          }
        }
      }
    }
    int best_last_p_idx = -1;
    int c_last_id = cycle_order.back();
    for (int p_last_idx = 0; p_last_idx < (int)cand_rungs[c_last_id].size(); ++p_last_idx) {
      if (!dp[k - 1][p_last_idx]) continue;
      int p_last = cand_rungs[c_last_id][p_last_idx];
      if (check_right_end(p_last)) {
        best_last_p_idx = p_last_idx;
        break;
      }
    }
    if (best_last_p_idx == -1) return false;
    vector<int> chosen_p(k);
    int cur_idx = best_last_p_idx;
    for (int ci = k - 1; ci >= 0; --ci) {
      chosen_p[ci] = cand_rungs[cycle_order[ci]][cur_idx];
      if (ci > 0) cur_idx = parent_dp[ci][cur_idx];
    }
    vector<pair<int, int>> pos(n, {-1, -1});
    int c0_id = cycle_order[0];
    const auto& ring0 = cycle_rings[c0_id];
    int L0 = ring0.size() / 2;
    int p0 = chosen_p[0];
    int u_L_0 = ring0[(p0 + 1) % ring0.size()];
    int v_L_0 = ring0[p0];
    bool left_placed = false;
    for (bool swap_left : {false, true}) {
      int u_sp = (swap_left ? v_L_0 : u_L_0);
      int v_ch = (swap_left ? u_L_0 : v_L_0);
      int r_sp = (swap_left ? 1 : 0);
      int r_ch = (swap_left ? 0 : 1);
      int len_v = 0;
      vector<int> chain_v;
      for (int v : adj[v_ch]) {
        if (cycle_of_node[v] != c0_id) {
          auto [ok, c] = trace_simple_chain(v, v_ch);
          if (!ok) { len_v = -1; break; }
          chain_v = c;
          len_v = c.size();
          break;
        }
      }
      if (len_v == -1) continue;
      int u_sp_out = -1;
      for (int v : adj[u_sp]) {
        if (cycle_of_node[v] != c0_id) {
          u_sp_out = v;
          break;
        }
      }
      if (u_sp_out == -1) {
        for (int idx = 0; idx < len_v; ++idx) {
          pos[chain_v[idx]] = {r_ch, -(idx + 1)};
        }
        left_placed = true;
        break;
      } else {
        vector<pair<int, pair<int, int>>> placed;
        if (!solve_end_tree_dfs(u_sp_out, u_sp, chain_v, placed)) continue;
        for (const auto& item : placed) {
          int u = item.first;
          auto [r_rel, c_rel] = item.second;
          int r_glob = (r_rel == 0 ? r_sp : r_ch);
          pos[u] = {r_glob, -c_rel};
        }
        left_placed = true;
        break;
      }
    }
    if (!left_placed) return false;
    vector<int> last_top, last_bot;
    for (int step = 0; step < L0; ++step) {
      int top_node = ring0[(p0 + 1 + step) % ring0.size()];
      int bot_node = ring0[(p0 - step + ring0.size()) % ring0.size()];
      last_top.push_back(top_node);
      last_bot.push_back(bot_node);
      pos[top_node] = {0, step};
      pos[bot_node] = {1, step};
    }
    for (int ci = 0; ci < k - 1; ++ci) {
      int p_curr = chosen_p[ci];
      int p_next = chosen_p[ci + 1];
      const auto& sp = seg_cache[ci][{p_curr, p_next}];
      int c_curr = cycle_order[ci];
      int u_exit = u_next_cycle[c_curr];
      auto [r_exit, col_exit] = pos[u_exit];
      for (auto& item : sp.node_pos) {
        int node = item.first;
        auto [r_rel, c_rel] = item.second;
        int r_glob = (r_exit == 0 ? r_rel : 1 - r_rel);
        int c_glob = col_exit + c_rel;
        pos[node] = {r_glob, c_glob};
      }
      int next_start_col = col_exit + sp.c_enter;
      int u_enter_glob_row = (r_exit == 0 ? sp.r_enter : 1 - sp.r_enter);
      int c_next = cycle_order[ci + 1];
      int u_enter = u_prev_cycle[c_next];
      const auto& ring_next = cycle_rings[c_next];
      int L_next = ring_next.size() / 2;
      int r1_a = ring_next[(p_next + 1) % ring_next.size()];
      int r1_a_row = (u_enter == r1_a ? u_enter_glob_row : 1 - u_enter_glob_row);
      int r1_b_row = 1 - r1_a_row;
      vector<int> top_next, bot_next;
      for (int step = 0; step < L_next; ++step) {
        int top_node = ring_next[(p_next + 1 + step) % ring_next.size()];
        int bot_node = ring_next[(p_next - step + ring_next.size()) % ring_next.size()];
        pos[top_node] = {r1_a_row, next_start_col + step};
        pos[bot_node] = {r1_b_row, next_start_col + step};
        if (r1_a_row == 0) {
          top_next.push_back(top_node);
          bot_next.push_back(bot_node);
        } else {
          top_next.push_back(bot_node);
          bot_next.push_back(top_node);
        }
      }
      last_top = top_next;
      last_bot = bot_next;
    }
    int c_last = cycle_order.back();
    int u_R_last = last_top.back();
    int v_R_last = last_bot.back();
    auto [r_uR, col_R] = pos[u_R_last];
    auto [r_vR, _col_vR] = pos[v_R_last];
    bool right_placed = false;
    for (bool swap_right : {false, true}) {
      int u_sp = (swap_right ? v_R_last : u_R_last);
      int v_ch = (swap_right ? u_R_last : v_R_last);
      int r_sp = (swap_right ? r_vR : r_uR);
      int r_ch = (swap_right ? r_uR : r_vR);
      int len_v = 0;
      vector<int> chain_v;
      for (int v : adj[v_ch]) {
        if (cycle_of_node[v] != c_last) {
          auto [ok, c] = trace_simple_chain(v, v_ch);
          if (!ok) { len_v = -1; break; }
          chain_v = c;
          len_v = c.size();
          break;
        }
      }
      if (len_v == -1) continue;
      int u_sp_out = -1;
      for (int v : adj[u_sp]) {
        if (cycle_of_node[v] != c_last) {
          u_sp_out = v;
          break;
        }
      }
      if (u_sp_out == -1) {
        for (int idx = 0; idx < len_v; ++idx) {
          pos[chain_v[idx]] = {r_ch, col_R + 1 + idx};
        }
        right_placed = true;
        break;
      } else {
        vector<pair<int, pair<int, int>>> placed;
        if (!solve_end_tree_dfs(u_sp_out, u_sp, chain_v, placed)) continue;
        for (const auto& item : placed) {
          int u = item.first;
          auto [r_rel, c_rel] = item.second;
          int r_glob = (r_rel == 0 ? r_sp : r_ch);
          pos[u] = {r_glob, col_R + c_rel};
        }
        right_placed = true;
        break;
      }
    }
    if (!right_placed) return false;
    for (int i = 0; i < n; ++i) {
      if (pos[i].first == -1) return false;
    }
    for (auto& e : edges) {
      int d = abs(pos[e.first].first - pos[e.second].first) + abs(pos[e.first].second - pos[e.second].second);
      if (d != 1) return false;
    }
    result = pos;
    return true;
  }
  bool solve(vector<pair<int, int>>& result) {
    if (!find_bccs()) return false;
    if (k == 0) return false;
    if (!build_bct()) return false;
    if (solve_with_current_order(result)) return true;
    if (k > 1) {
      reverse(bct_path.begin(), bct_path.end());
      if (!update_bct_order()) return false;
      if (solve_with_current_order(result)) return true;
    }
    return false;
  }
};
bool solve_global(int n, const vector<pair<int, int>>& edges, vector<pair<int, int>>& final_result) {
  if (n == 0) return true;
  vector<vector<int>> adj(n);
  for (const auto& e : edges) {
    if (e.first < 0 || e.first >= n || e.second < 0 || e.second >= n) return false;
    adj[e.first].push_back(e.second);
    adj[e.second].push_back(e.first);
  }
  for (int i = 0; i < n; ++i) {
    if (adj[i].size() > 3) return false;
  }
  vector<int> color(n, -1);
  for (int i = 0; i < n; ++i) {
    if (color[i] != -1) continue;
    queue<int> q;
    q.push(i);
    color[i] = 0;
    while (!q.empty()) {
      int u = q.front(); q.pop();
      for (int v : adj[u]) {
        if (color[v] == -1) {
          color[v] = 1 - color[u];
          q.push(v);
        } else if (color[v] == color[u]) {
          return false;
        }
      }
    }
  }
  vector<bool> vis(n, false);
  vector<vector<int>> components;
  for (int i = 0; i < n; ++i) {
    if (!vis[i]) {
      vector<int> comp;
      queue<int> q;
      q.push(i);
      vis[i] = true;
      while (!q.empty()) {
        int u = q.front(); q.pop();
        comp.push_back(u);
        for (int v : adj[u]) {
          if (!vis[v]) {
            vis[v] = true;
            q.push(v);
          }
        }
      }
      components.push_back(comp);
    }
  }
  final_result.assign(n, {-1, -1});
  int cur_col = 0;
  vector<int> g2l(n, -1);
  for (const auto& comp : components) {
    int c_size = comp.size();
    if (c_size == 1) {
      final_result[comp[0]] = {0, cur_col};
      cur_col += 2;
      continue;
    }
    for (int i = 0; i < c_size; ++i) g2l[comp[i]] = i;
    vector<vector<int>> c_adj(c_size);
    vector<pair<int, int>> c_edges;
    for (int u : comp) {
      for (int v : adj[u]) {
        if (u < v) {
          c_adj[g2l[u]].push_back(g2l[v]);
          c_adj[g2l[v]].push_back(g2l[u]);
          c_edges.push_back({g2l[u], g2l[v]});
        }
      }
    }
    vector<pair<int, int>> comp_res;
    bool solved = false;
    if ((int)c_edges.size() == c_size - 1) {
      TreeEmbedder tree_solver(c_size, c_adj, c_edges);
      if (tree_solver.solve(comp_res)) {
        solved = true;
      }
    } else {
      CactusSolver cactus_solver(c_size, c_adj, c_edges);
      if (cactus_solver.solve(comp_res)) {
        solved = true;
      }
    }
    for (int i = 0; i < c_size; ++i) g2l[comp[i]] = -1;
    if (!solved) return false;
    int min_c = 1e9, max_c = -1e9;
    for (int i = 0; i < c_size; ++i) {
      min_c = min(min_c, comp_res[i].second);
      max_c = max(max_c, comp_res[i].second);
    }
    for (int i = 0; i < c_size; ++i) {
      final_result[comp[i]] = {comp_res[i].first, cur_col + (comp_res[i].second - min_c)};
    }
    cur_col += (max_c - min_c) + 2;
  }
  int min_c = 1e9, max_c = -1e9;
  for (int i = 0; i < n; ++i) {
    min_c = min(min_c, final_result[i].second);
    max_c = max(max_c, final_result[i].second);
  }
  int shift = min_c + (max_c - min_c) / 2;
  for (int i = 0; i < n; ++i) {
    final_result[i].second -= shift;
  }
  vector<pair<int, int>> sorted_coords = final_result;
  sort(sorted_coords.begin(), sorted_coords.end());
  for (int i = 0; i < n; ++i) {
    if (sorted_coords[i].first < 0 || sorted_coords[i].first > 1) return false;
    if (sorted_coords[i].second < -200000 || sorted_coords[i].second > 200000) return false;
    if (i > 0 && sorted_coords[i] == sorted_coords[i - 1]) return false;
  }
  for (const auto& e : edges) {
    int d = abs(final_result[e.first].first - final_result[e.second].first) +
        abs(final_result[e.first].second - final_result[e.second].second);
    if (d != 1) return false;
  }
  return true;
}
int TreeEmbedder::grid[2][MAX_COORD];
int TreeEmbedder::grid_token[2][MAX_COORD];
int TreeEmbedder::cur_token = 0;
int main() {
#if defined(HAS_SYS_RESOURCE) && defined(RLIMIT_STACK)
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0) {
    rl.rlim_cur = min((rlim_t)(256 * 1024 * 1024), rl.rlim_max);
    setrlimit(RLIMIT_STACK, &rl);
  }
#endif
  ios::sync_with_stdio(false);
  cin.tie(nullptr);
  int t;
  if (!(cin >> t)) return 0;
  while (t--) {
    int n, m;
    cin >> n >> m;
    vector<pair<int, int>> edges;
    edges.reserve(m);
    for (int i = 0; i < m; ++i) {
      int u, v;
      cin >> u >> v;
      --u; --v;
      edges.push_back({u, v});
    }
    vector<pair<int, int>> result;
    if (solve_global(n, edges, result)) {
      cout << "Yes\n";
      for (int i = 0; i < n; ++i) {
        cout << result[i].first << " " << result[i].second << "\n";
      }
    } else {
      cout << "No\n";
    }
  }
  return 0;
}
