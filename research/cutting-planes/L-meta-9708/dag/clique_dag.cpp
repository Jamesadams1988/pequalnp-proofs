// Enumerate families of proper clique labels in normalized K6 cutting planes.
// Build: c++ -O2 -std=c++17 clique_dag.cpp -o clique_dag
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>

using Mask = std::uint64_t;
constexpr int vertices = 6;
constexpr int full = 63;
constexpr int impossible = 1000;
constexpr Mask bit(int index) { return Mask(1) << index; }
int count(Mask mask) { return __builtin_popcountll(mask); }
int first(Mask mask) { return __builtin_ctzll(mask); }

struct Bounds {
    int operands = impossible;
    int instructions = impossible;
};
std::array<int, 64> edges;
std::array<Mask, 64> majority;
std::vector<int> labels;
std::map<std::pair<int, Mask>, Bounds> cache;
std::array<Bounds, 7> best;
std::array<unsigned, 7> families;

void initialize() {
    for (int set = 0; set <= full; ++set) {
        int index = 0;
        for (int i = 0; i < vertices; ++i)
            for (int j = 0; j < i; ++j, ++index)
                if ((set & bit(i)) && (set & bit(j)))
                    edges[set] |= 1 << index;
        for (int test = 1; test <= full; ++test)
            if (2 * count(test & set) > count(test))
                majority[set] |= bit(test);
    }
    for (int size = 3; size <= 5; ++size)
        for (int set = 1; set < full; ++set)
            if (count(set) == size)
                labels.push_back(set);
}

// Lower-bound one cut for a fixed selection of its distinct nonedge children.
// The uncovered pairs are mandatory children. Other possible children are edges.
Bounds rule_bound(int target, Mask children) {
    int missing = edges[target];
    Mask protected_sets = 0;
    std::array<int, vertices> degree{};
    int mandatory = count(children);
    for (Mask left = children; left; left &= left - 1) {
        int child = first(left);
        missing &= ~edges[child];
        protected_sets |= majority[child];
        for (int i = 0; i < vertices; ++i)
            degree[i] += (child >> i) & 1;
    }
    for (int test = target; test; test = (test - 1) & target) {
        int n = count(test);
        if ((n == 4 || n == 6) && !(protected_sets & bit(test)))
            return {};
    }
    int index = 0;
    for (int i = 0; i < vertices; ++i) {
        for (int j = 0; j < i; ++j, ++index) {
            if (missing & (1 << index)) {
                ++mandatory;
                ++degree[i];
                ++degree[j];
            }
        }
    }
    int divisor = degree[first(target)];
    bool unweighted_cut = divisor >= 2 && mandatory < 2 * divisor;
    for (int i = 0; i < vertices; ++i)
        if ((target & bit(i)) && degree[i] != divisor)
            unweighted_cut = false;
    return {mandatory, mandatory + (unweighted_cut ? 0 : 1)};
}

Bounds best_cut(int target, Mask available) {
    Mask proper = 0;
    for (Mask left = available; left; left &= left - 1) {
        int child = first(left);
        if (child != target && (child & target) == child)
            proper |= bit(child);
    }
    const auto key = std::make_pair(target, proper);
    auto found = cache.find(key);
    if (found != cache.end())
        return found->second;
    Bounds result;
    for (Mask children = proper;; children = (children - 1) & proper) {
        Bounds current = rule_bound(target, children);
        result.operands = std::min(result.operands, current.operands);
        result.instructions = std::min(result.instructions, current.instructions);
        if (!children)
            break;
    }
    cache.emplace(key, result);
    return result;
}

// The count includes the final full-clique cut. Families containing a label
// impossible by the majority test remain impossible under all later labels,
// since we enumerate in order of nondecreasing size.
void enumerate(unsigned index, int cuts, Mask chosen, Bounds prefix) {
    ++families[cuts];
    Bounds final = best_cut(full, chosen);
    if (final.operands != impossible) {
        best[cuts].operands = std::min(best[cuts].operands, prefix.operands + final.operands);
        best[cuts].instructions = std::min(best[cuts].instructions, prefix.instructions + final.instructions);
    }
    if (cuts == 6)
        return;
    for (unsigned i = index; i < labels.size(); ++i) {
        int label = labels[i];
        Bounds next = best_cut(label, chosen);
        if (next.operands != impossible)
            enumerate(i + 1, cuts + 1, chosen | bit(label),
                      {prefix.operands + next.operands, prefix.instructions + next.instructions});
    }
}

int main() {
    initialize();
    enumerate(0, 1, 0, {0, 0});
    std::cout << "derived labels | surviving prefixes | min operand bound | min local instruction bound\n";
    for (int i = 1; i <= 6; ++i) {
        std::cout << i << " " << families[i] << " ";
        if (best[i].operands == impossible)
            std::cout << "infeasible infeasible\n";
        else
            std::cout << best[i].operands << " " << best[i].instructions << "\n";
    }
    return 0;
}
