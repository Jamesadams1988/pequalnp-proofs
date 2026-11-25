#include "goal_levels.hpp"
#include <algorithm>

// All nodes in the current layer are processed before moving to their children.
// "limit" is an upper cutoff; any candidate below it is returned exactly.
int minimum(const Levels &levels, int k, Mask jobs, Mask children, int spent,
            int limit, unsigned long &calls) {
    ++calls;
    constexpr int pigeon_cost[] = {0, 2, 6, 12, 20};
    constexpr int hole_cost[] = {0, 2, 5, 9, 14};
    if (k == 1) return spent + 2 * std::popcount(jobs);

    int lower = spent + hole_cost[k] * std::popcount(jobs);
    if (k == 2) lower += 2 * std::max(4, std::popcount(children));
    else lower += 8 + 5 * std::max(6, std::popcount(children));
    if (lower >= limit) return limit;
    if (!jobs) return minimum(levels, k - 1, children, 0, spent, limit, calls);

    const auto &options = levels[k][std::countr_zero(jobs)].options;
    int best = limit;
    for (int option = 0; option < int(options.size()); ++option) {
        const int price = option < k + 1 ? pigeon_cost[k] : hole_cost[k];
        best = std::min(best, minimum(levels, k, jobs & (jobs - 1),
                                      children | options[option], spent + price,
                                      best, calls));
    }
    return best;
}

int main() {
    const Levels levels = make_levels();
    for (int axis = 0; axis < 2; ++axis) {
        // Pigeon/hole permutations preserve all costs within each root orientation.
        const auto &options = levels[4][0].options;
        const int cutoff = axis ? 130 : 113;
        unsigned long calls = 0;
        const int best = minimum(levels, 3, options[axis ? 5 : 0], 0,
                                 axis ? 14 : 20, cutoff, calls);
        if (best >= cutoff) throw std::runtime_error("no feasible proof below cutoff");
        std::cout << (axis ? "hole" : "pigeon") << " root, resolutions " << best
                  << ", total lines " << best + 45 << ", calls " << calls << '\n';
    }
}
