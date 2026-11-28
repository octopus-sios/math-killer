// Exact verifier for full Ramsey chains in small two-coloured complete graphs.
// Build, run the mutation test, and compare independent orbit counts via verify.py.
#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <thread>
#include <unordered_set>
#include <vector>

using Mask = std::uint64_t;
using Row = std::array<int, 10>;
using std::popcount;
int n, ne;
Mask full, edge[10][10];
int from[45], to[45];
Mask bit(int i) { return Mask(1) << i; }
int low(Mask s) { return std::countr_zero(s); }

Row adjacency(Mask s) {
    Row a{};
    for (; s; s &= s-1) {
        int j = low(s), x = from[j], y = to[j];
        a[x] |= 1 << y;
        a[y] |= 1 << x;
    }
    return a;
}

void set_order(int k) {
    n = k;
    ne = 0;
    for (int v = 0; v < n; ++v) for (int u = 0; u < v; ++u) {
        edge[u][v] = edge[v][u] = bit(ne);
        from[ne] = u; to[ne++] = v;
    }
    full = bit(ne)-1;
}

// Relabel the vertices, refining by neighbour counts in each colour cell.
// Coverage needs ONLY that the result is a relabelling. Missing a canonical
// tie would cost time/repeat isomorphic inputs, not omit a colouring.
Mask normal(const Row &a, Row col, int cells) {
    Row order{};
    std::iota(order.begin(), order.begin()+n, 0);
    for (;;) {
        std::array<Mask,10> sig{};
        for (int v = 0; v < n; ++v) {
            sig[v] = Mask(col[v]) << 40;
            for (int s = a[v]; s; s &= s-1) sig[v] += bit(4*col[low(s)]);
        }
        std::sort(order.begin(), order.begin()+n,
                  [&](int u, int v) { return sig[u] < sig[v]; });
        int count = 0;
        for (int j = 0; j < n; ++j) {
            if (j && sig[order[j]] != sig[order[j-1]]) ++count;
            col[order[j]] = count;
        }
        if (++count == cells) break;
        cells = count;
    }
    if (cells == n) {
        Mask g = 0;
        for (int v = 0; v < n; ++v) for (int u = 0; u < v; ++u)
            if (a[order[v]] & (1 << order[u])) g |= edge[u][v];
        return g;
    }
    Row sizes{};
    for (int v = 0; v < n; ++v) ++sizes[col[v]];
    int c = -1;
    for (int j = 0; j < cells; ++j)
        if (sizes[j] > 1 && (c < 0 || sizes[j] < sizes[c])) c = j;
    Mask best = ~Mask(0);
    for (int v = 0; v < n; ++v) if (col[v] == c) {
        bool twin = false;
        for (int w = 0; w < v; ++w)
            if (col[w] == c && !((a[w]^a[v]) & ~((1<<v)|(1<<w)))) twin = true;
        if (twin) continue;
        Row next = col;
        next[v] = cells;
        best = std::min(best, normal(a, next, cells+1));
    }
    return best;
}

std::vector<Mask> augment(const std::vector<Mask> &previous) {
    std::unordered_set<Mask> reps;
    int base = ne - (n-1);
    for (Mask g : previous) {
        Row a = adjacency(g);
        int mx = 0, atmax = 0;
        for (int v = 0; v < n-1; ++v) mx = std::max(mx, popcount(unsigned(a[v])));
        for (int v = 0; v < n-1; ++v) if (popcount(unsigned(a[v])) == mx) atmax |= 1<<v;
        for (unsigned s = 0; s < (1u<<(n-1)); ++s) {
            int d = popcount(s);
            if (popcount(g)+d > ne/2 || d < mx || (d == mx && (s & atmax))) continue;
            reps.insert(normal(adjacency(g | (Mask(s)<<base)), Row{}, 1));
        }
    }
    return {reps.begin(), reps.end()};
}

struct Chain {
    std::array<Mask,10> part{};
    std::array<Row,10> into{};  // vertex permutations taking part[i] into part[i+1]
};

// The independent, exhaustive witness check. No isomorphism algorithm,
// search logic, random choices, path/forest restrictions or solver needed.
bool valid(Mask red, const Chain &c) {
    Mask used = 0;
    for (int i = 1; i < n; ++i) {
        Mask s = c.part[i];
        if ((s & ~full) || popcount(s) != i || (used & s)) return false;
        if ((s & red) && (s & ~red)) return false;
        used |= s;
        if (i == n-1) break;
        const Row &p = c.into[i];
        int seen = 0;
        for (int v = 0; v < n; ++v) {
            if (p[v] < 0 || p[v] >= n || (seen & (1<<p[v]))) return false;
            seen |= 1<<p[v];
        }
        for (; s; s &= s-1) {
            int e = low(s);
            if (!(edge[p[from[e]]][p[to[e]]] & c.part[i+1])) return false;
        }
    }
    return used == full;
}

void finish_perm(Row &p) {
    int free = (1<<n)-1;
    for (int v = 0; v < n; ++v) if (p[v] >= 0) free &= ~(1<<p[v]);
    for (int v = 0; v < n; ++v) if (p[v] < 0) { p[v] = low(free); free &= free-1; }
}

// Everything below in Search just proposes a positive certificate. A search
// timeout is never taken as a negative decision or a successful verification.
struct Search {
    Chain chain;
    Mask state;
    int budget;
    unsigned draw() {
        state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
        return unsigned((state*2685821657736338717ULL) >> 32);
    }
    void shuffle(int *p, int len) {
        for (int j = len-1; j > 0; --j) std::swap(p[j], p[draw()%(j+1)]);
    }
    bool path_pack(int i, Mask r, Mask b) {
        if (i == 1) { chain.part[1] = r|b; return true; }
        for (bool red : {true,false}) {
            Mask g = red ? r : b;
            if (popcount(g) < i) continue;
            Row a = adjacency(g);
            for (int v = 0; v < n; ++v) {
                if (walk(i,r,b,a,v,v,1<<v,i,0,red)) return true;
                if (budget <= 0) return false;
            }
        }
        return false;
    }
    bool walk(int i, Mask r, Mask b, const Row &a, int start, int v, int used,
              int left, Mask path, bool red) {
        if (--budget <= 0) return false;
        if (!left) {
            if (v < start) return false;
            chain.part[i] = path;
            return path_pack(i-1, r^(red?path:0), b^(red?0:path));
        }
        for (int ns = a[v] & ~used; ns; ns &= ns-1) {
            int w = low(ns);
            if (walk(i,r,b,a,start,w,used|(1<<w),left-1,path|edge[v][w],red)) return true;
            if (budget <= 0) break;
        }
        return false;
    }
    void path_perms() {
        Row prev{};
        for (int i = 1; i < n; ++i) {
            Row a = adjacency(chain.part[i]), list{};
            int v = 0;
            while (v < n && popcount(unsigned(a[v])) != 1) ++v;
            for (int j = 0; j <= i; ++j) {
                if (v >= n) throw std::logic_error("bad path");
                list[j] = v;
                v = low(a[v] & ~(j ? 1<<list[j-1] : 0));
            }
            if (i > 1) {
                Row &p = chain.into[i-1]; p.fill(-1);
                for (int j = 0; j < i; ++j) p[prev[j]] = list[j];
                finish_perm(p);
            }
            prev = list;
        }
    }
    // From an (i+1)-edge parent in the chain, delete one edge, then find
    // an injective embedding of the remaining graph into a colour class.
    bool pack(int i, Mask r, Mask b, Mask parent) {
        if (i == 1) {
            chain.part[1] = r|b;
            int s = low(r|b), t = low(parent);
            Row &p = chain.into[1]; p.fill(-1);
            p[from[s]] = from[t]; p[to[s]] = to[t]; finish_perm(p);
            return true;
        }
        Row del{};
        int nd = 0;
        for (Mask s = parent; s; s &= s-1) del[nd++] = low(s);
        shuffle(del.data(), nd);
        bool first = popcount(r) < popcount(b);
        if (draw()%5 == 0) first = !first;
        for (bool red : {first,!first}) {
            Mask g = red ? r : b;
            if (popcount(g) < i) continue;
            Row a = adjacency(g);
            for (int j = 0; j < nd; ++j) {
                Row h = adjacency(parent^bit(del[j])), ord{}, allow{}, image{};
                int t = 0, seen = 0;
                for (;;) {
                    int best = -1, score = -1;
                    for (int v = 0; v < n; ++v) if (h[v] && !(seen & (1<<v))) {
                        int s = 20*popcount(unsigned(h[v]&seen)) + popcount(unsigned(h[v]));
                        if (s > score) { score = s; best = v; }
                    }
                    if (best < 0) break;
                    seen |= 1<<best; ord[t++] = best;
                    for (int w = 0; w < n; ++w)
                        if (popcount(unsigned(a[w])) >= popcount(unsigned(h[best]))) allow[best] |= 1<<w;
                }
                auto place = [&](auto &&self, int k, int used, Mask m) -> bool {
                    if (--budget <= 0) return false;
                    if (k == t) {
                        chain.part[i] = m;
                        if (!pack(i-1, r^(red?m:0), b^(red?0:m), m)) return false;
                        Row &p = chain.into[i]; p.fill(-1);
                        for (int z = 0; z < t; ++z) p[image[ord[z]]] = ord[z];
                        finish_perm(p); return true;
                    }
                    int v = ord[k], ns = allow[v] & ~used;
                    for (int z = 0; z < k; ++z)
                        if (h[v] & (1<<ord[z])) ns &= a[image[ord[z]]];
                    for (; ns; ns &= ns-1) {
                        int w = low(ns); image[v] = w; Mask next = m;
                        for (int z = 0; z < k; ++z)
                            if (h[v] & (1<<ord[z])) next |= edge[w][image[ord[z]]];
                        if (self(self, k+1, used|(1<<w), next)) return true;
                        if (budget <= 0) break;
                    }
                    return false;
                };
                if (place(place,0,0,0)) return true;
                if (budget <= 0) return false;
            }
        }
        return false;
    }
    Mask propose(Mask g, int mode) {
        std::array<int,45> list{};
        int m = 0;
        for (Mask s = g; s; s &= s-1) list[m++] = low(s);
        shuffle(list.data(), m);
        Row deg{}, group{};
        std::iota(group.begin(),group.end(),0);
        Mask ans = 0;
        for (int j = 0; j < m; ++j) {
            int e = list[j], u = from[e], v = to[e];
            if (mode && group[u] == group[v]) continue;
            if (mode == 2 && (deg[u] >= 2 || deg[v] >= 2)) continue;
            ++deg[u]; ++deg[v]; ans |= bit(e);
            int gv = group[v];
            for (int w = 0; w < n; ++w) if (group[w] == gv) group[w] = group[u];
            if (popcount(ans) == n-1) return ans;
        }
        return 0;
    }
    bool solve(Mask r) {
        state = 0x9e3779b97f4a7c15ULL ^ r;
        Mask b = full^r;
        for (int scale = 1; scale <= 16; scale *= 2) {
            budget = 2500*scale;
            if (path_pack(n-1,r,b)) { path_perms(); return true; }
            for (int j = 0; j < 160*scale; ++j) {
                bool red = draw() & 1;
                if (popcount(red?r:b) < n-1) red = !red;
                Mask top = propose(red?r:b, j%3);
                if (!top) continue;
                chain.part[n-1] = top;
                budget = 3500*scale;
                if (pack(n-2, r^(red?top:0), b^(red?0:top), top)) return true;
            }
        }
        return false;
    }
};

int main(int argc, char **argv) {
    int upto = argc > 1 ? std::atoi(argv[1]) : 10;
    if (upto < 3 || upto > 10) return 2;
    std::vector<Mask> graphs{0};
    for (int k = 2; k <= upto; ++k) {
        set_order(k);
        graphs = augment(graphs);
        if (k < 3) continue;
        if (k == 3) {
            Search s;
            if (!s.solve(0) || !valid(0,s.chain)) return 3;
            s.chain.into[1].fill(0);
            if (valid(0,s.chain)) return 4;
        }
        std::atomic<unsigned> next{0}, checked{0};
        std::atomic<bool> failed{false};
        auto run = [&] {
            Search s;
            for (;;) {
                unsigned begin = next.fetch_add(256);
                if (begin >= graphs.size() || failed) break;
                unsigned end = std::min<unsigned>(begin+256, graphs.size());
                for (unsigned j = begin; j < end; ++j) {
                    Mask r = graphs[j];
                    if (!s.solve(r) || !valid(r,s.chain)) {
                        failed = true;
                        std::cerr << "FAIL n=" << k << " red mask=" << r << '\n';
                        return;
                    }
                }
                checked += end-begin;
            }
        };
        std::vector<std::thread> workers;
        unsigned threads = std::clamp(std::thread::hardware_concurrency(),1u,8u);
        for (unsigned j = 1; j < threads; ++j) workers.emplace_back(run);
        run();
        for (auto &w : workers) w.join();
        if (failed || checked != graphs.size()) return 1;
        std::cout << k << " " << checked << std::endl;
    }
}
