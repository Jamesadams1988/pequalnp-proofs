// Exhaust every available Hall frontier one node below the claimed minimum.
#include "goal_levels.hpp"

bool reaches_root(const Levels &levels, int k, Mask available) {
    while (k < 4) {
        Mask next = 0;
        int index = 0;
        for (const Goal &goal : levels[++k]) {
            for (Mask needed : goal.options) {
                if ((needed & available) == needed) {
                    next |= Mask{1} << index;
                    break;
                }
            }
            ++index;
        }
        if (!next) return false;
        available = next;
    }
    return available != 0;
}

int main() {
    const Levels levels = make_levels();
    const int minimum[] = {0, 4, 6, 4};
    for (int k = 1; k <= 3; ++k) {
        const int count = levels[k].size();
        const Mask limit = Mask{1} << count;
        const int size = minimum[k] - 1;
        std::uint64_t checked = 0;
        for (Mask set = (Mask{1} << size) - 1; set < limit;) {
            if (reaches_root(levels, k, set))
                throw std::runtime_error("smaller frontier reaches the root");
            ++checked;
            // Next fixed-popcount mask in increasing order.
            const Mask low = set & -set;
            const Mask carry = set + low;
            set = carry | (((carry ^ set) >> 2) / low);
        }
        Mask witness = 0;
        for (int i = 0; i < count; ++i) {
            if (levels[k][i].pigeons == (1 << (k + 1)) - 1)
                witness |= Mask{1} << i;
        }
        if (std::popcount(witness) != minimum[k] || !reaches_root(levels, k, witness))
            throw std::runtime_error("missing upper-bound control");
        std::cout << "level " << k << ", candidate nodes " << count
                  << ", excluded frontiers " << checked << ", minimum " << minimum[k] << '\n';
    }
}
