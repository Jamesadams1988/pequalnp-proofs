#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Mask = std::uint32_t;
constexpr int side = 13;
constexpr Mask all = (1u << side) - 1;
constexpr Mask universe = (1u << (2 * side)) - 1;

struct Plane {
    std::array<Mask, 1 << side> meet{};
    Plane() {
        for (int p = 0; p < side; ++p)
            for (int d : {0, 1, 3, 9})
                meet[1 << p] |= 1u << ((d - p + side) % side);
        for (Mask s = 1; s <= all; ++s)
            meet[s] |= meet[s & (s - 1)] | meet[s & -s];
    }

    std::vector<Mask> maximal_independent() const {
        std::vector<Mask> cuts;
        for (Mask p = 0; p <= all; ++p) {
            Mask l = all ^ meet[p];
            if ((all ^ meet[l]) == p) cuts.push_back(p | (l << side));
        }
        return cuts;
    }
};

template<typename F> void subsets(Mask s, F visit) {
    for (Mask t = s;; t = (t - 1) & s) {
        visit(t);
        if (!t) break;
    }
}

// Aggregate over every maximal false assignment and every canonical factor
// that rejects it. One entry for each 26-bit singleton support uses 256 MiB.
struct Capacity {
    std::uint16_t cuts = 0;
    std::uint16_t weight = 0;
};

int cut_weight(Mask i) {
    int size = std::popcount(i);
    if (size == 13) return 5;
    if (size == 10) return 0;
    return 1;
}

bool independent(const Plane& plane, Mask s) {
    return !(plane.meet[s & all] & (s >> side));
}

// Independently evaluate the canonical factor by constructing the components
// of the incidence graph remaining after its accepted singleton inputs vanish.
bool canonical_accepts(const Plane& plane, Mask singleton, Mask assignment) {
    if (singleton & assignment) return true;
    Mask unvisited = universe ^ singleton;
    while (unvisited) {
        Mask component = unvisited & -unvisited;
        Mask frontier = component;
        while (frontier) {
            Mask neighbors = (plane.meet[frontier & all] << side) | plane.meet[frontier >> side];
            frontier = neighbors & unvisited & ~component;
            component |= frontier;
        }
        unvisited &= ~component;
        Mask selected = component & assignment;
        if ((selected & all) && (selected >> side)) return true;
    }
    return false;
}

int main() {
    Plane plane;
    auto cuts = plane.maximal_independent();
    std::vector<Capacity> capacity(universe + 1);
    std::array<int, 27> by_size{};
    std::uint64_t incidences = 0;
    int total_weight = 0;
    for (Mask i : cuts) {
        ++by_size[std::popcount(i)];
        int weight = cut_weight(i);
        total_weight += weight;
        Mask p_available = all ^ (i & all);
        Mask l_available = all ^ (i >> side);
        subsets(p_available, [&](Mask p) {
            Mask allowed = l_available & ~plane.meet[p];
            subsets(allowed, [&](Mask l) {
                Mask singleton = universe ^ (i | p | (l << side));
                ++capacity[singleton].cuts;
                capacity[singleton].weight += weight;
                ++incidences;
            });
        });
    }
    int max_cuts = 0, max_weight = 0;
    Mask best_cuts = 0, best_weight = 0;
    for (Mask s = 0; s <= universe; ++s) {
        if (capacity[s].cuts > max_cuts) {
            max_cuts = capacity[s].cuts;
            best_cuts = s;
        }
        if (capacity[s].weight > max_weight) {
            max_weight = capacity[s].weight;
            best_weight = s;
        }
    }
    // Check both maxima witnesses and two extreme supports from their actual
    // component formulas on all cuts. The enumeration above uses only masks.
    for (Mask s : {Mask(0), universe, best_cuts, best_weight}) {
        int false_cuts = 0, false_weight = 0;
        for (Mask i : cuts) {
            bool rejects = !canonical_accepts(plane, s, i);
            if (rejects != (!(s & i) && independent(plane, universe ^ (s | i)))) return 1;
            if (rejects) {
                ++false_cuts;
                false_weight += cut_weight(i);
            }
        }
        if (false_cuts != capacity[s].cuts || false_weight != capacity[s].weight) return 1;
    }
    std::cout << "maximal negatives by size";
    for (int size = 0; size <= 26; ++size)
        if (by_size[size]) std::cout << ' ' << size << '=' << by_size[size];
    std::cout << "\ntotal maximal negatives " << cuts.size() << "\ntotal weight " << total_weight
              << "\ncut-factor incidences " << incidences
              << "\nmaximum false cuts per factor " << max_cuts << " (singleton masks "
              << (best_cuts & all) << ' ' << (best_cuts >> side) << ')'
              << "\nmaximum false weight per factor " << max_weight << " (singleton masks "
              << (best_weight & all) << ' ' << (best_weight >> side) << ')'
              << "\nunweighted lower bound " << (cuts.size() + max_cuts - 1) / max_cuts
              << "\nweighted lower bound " << (total_weight + max_weight - 1) / max_weight << '\n';
    return !(cuts.size() == 704 && total_weight == 686 && max_cuts == 14 && max_weight == 10);
}
