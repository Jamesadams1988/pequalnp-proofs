#pragma once
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;
struct Goal {
    int pigeons, holes;
    std::vector<Mask> options;
};
using Levels = std::array<std::vector<Goal>, 5>;

inline Levels make_levels() {
    Levels levels;
    for (int k = 1; k <= 4; ++k) {
        for (unsigned p = 1; p < 32; ++p) {
            for (unsigned h = 1; h < 16; ++h) {
                if (std::popcount(p) != k + 1 || std::popcount(h) != k) continue;
                Goal goal{int(p), int(h), {}};
                if (k > 1) {
                    // A fixed pigeon demands every child with that pigeon removed.
                    // A fixed hole similarly demands every child with that hole removed.
                    for (int axis = 0; axis <= 1; ++axis) {
                        int present = axis == 0 ? p : h;
                        for (int bit = 1; bit <= present; bit *= 2) {
                            if (!(present & bit)) continue;
                            Mask needed = 0;
                            int index = 0;
                            for (const Goal &child : levels[k - 1]) {
                                bool nested = (child.pigeons & p) == unsigned(child.pigeons)
                                           && (child.holes & h) == unsigned(child.holes);
                                int removed = axis == 0 ? (p ^ child.pigeons) : (h ^ child.holes);
                                if (nested && removed == bit) needed |= Mask{1} << index;
                                ++index;
                            }
                            if (std::popcount(needed) != k + axis)
                                throw std::runtime_error("invalid family cardinality");
                            goal.options.push_back(needed);
                        }
                    }
                }
                levels[k].push_back(goal);
            }
        }
    }
    return levels;
}
