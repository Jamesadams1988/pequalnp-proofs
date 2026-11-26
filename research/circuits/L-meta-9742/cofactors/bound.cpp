// Lower bounds for monotone binary edge functions on all induced subgraphs.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Mask = std::uint32_t;

struct TwoSmallest {
    int first = 1000, second = 1000;
    void insert(int x) {
        if (x < first) { second = first; first = x; }
        else if (x < second) second = x;
    }
};

std::vector<Mask> neighborhood_unions(const std::vector<Mask>& adjacency, int offset, int width) {
    std::vector<Mask> all(Mask{1} << width);
    for (Mask s = 1; s < all.size(); ++s)
        all[s] = all[s & (s-1)] | adjacency[offset + std::countr_zero(s)];
    return all;
}

int main() {
    int p, q, m;
    if (!(std::cin >> p >> q >> m) || p < 1 || q < 1 || p > 26 || q > 26 || p+q > 26 || m < 0 || m > p*q)
        return 2;
    std::vector<Mask> neighbors(p+q);
    for (int k = 0; k < m; ++k) {
        int u, v;
        if (!(std::cin >> u >> v) || u < 0 || u >= p || v < p || v >= p+q ||
                (neighbors[u] & (Mask{1} << v))) return 2;
        neighbors[u] |= Mask{1} << v;
        neighbors[v] |= Mask{1} << u;
    }
    const auto near_right = neighborhood_unions(neighbors, 0, p);
    const auto near_left = neighborhood_unions(neighbors, p, q);
    const Mask left = (Mask{1} << p) - 1, limit = Mask{1} << (p+q);
    std::vector<std::uint8_t> bound(limit);
    std::uint64_t cores = 0;
    for (Mask s = 1; s < limit; ++s) {
        const Mask core = s & (near_left[s >> p] | near_right[s & left]);
        if (core != s) { bound[s] = bound[core]; continue; }
        ++cores;
        const int n = std::popcount(s);
        if (n == 2) { bound[s] = 1; continue; }
        int baseline = n-1, edges = 0;
        TwoSmallest and_scores, or_scores;
        for (Mask live = s; live; live &= live-1) {
            const int v = std::countr_zero(live);
            const Mask low_mask = s ^ (Mask{1} << v);
            const Mask residual = low_mask & ~neighbors[v];
            const int degree = std::popcount(s & neighbors[v]);
            if (v < p) edges += degree;
            const int low = bound[low_mask];
            const int high = degree + (bound[residual] ? int(bound[residual]) : -1);
            // Any essential input must be read by at least one gate.
            baseline = std::max(baseline, 1+std::max(low,high));
            and_scores.insert(std::max(2+low,1+high));
            or_scores.insert(std::max(1+low,2+high));
        }
        // A first binary gate chooses two distinct essential variables and one operation.
        const int result = std::max(baseline,std::min(and_scores.second,or_scores.second));
        const int star_upper = edges + std::min(std::popcount(s & left),std::popcount(s >> p))-1;
        if (result > star_upper || result > 255) return 3;
        bound[s] = static_cast<std::uint8_t>(result);
        if (s == limit-1)
            std::cout << "root general-pin floor " << baseline << "; first-AND floor "
                      << and_scores.second << "; first-OR floor " << or_scores.second << '\n';
    }
    std::cout << "masks " << limit << "; nonempty isolate-free masks " << cores
              << "; monotone size lower bound " << int(bound.back()) << '\n';
}
