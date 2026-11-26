#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>

namespace {
constexpr int vertices = 9;
constexpr int positive_count = 12;
constexpr int negative_count = 13;
constexpr int positive_sets = 1 << positive_count;
constexpr int negative_sets = 1 << negative_count;
constexpr int infinity = 60;
using Byte = std::uint8_t;
using Mask = unsigned;

constexpr std::array<std::pair<int, int>, positive_count> edges{{
    {0,4}, {0,5}, {1,5}, {0,6}, {2,6}, {3,6},
    {1,7}, {2,7}, {4,7}, {1,8}, {3,8}, {5,8}
}};

struct Signature {
    Mask accepted;  // Positive assignments on which this signal is one
    Mask rejected;  // Negative assignments on which this signal is zero

    bool dominates(Signature other) const {
        return (accepted & other.accepted) == other.accepted &&
               (rejected & other.rejected) == other.rejected;
    }
};

enum Gate { Not, And, Or };
Signature evaluate(Gate gate, Signature left, Signature right) {
    if (gate == And)
        return {left.accepted & right.accepted, left.rejected | right.rejected};
    if (gate == Or)
        return {left.accepted | right.accepted, left.rejected & right.rejected};
    return {left.accepted ^ (positive_sets - 1), left.rejected ^ (negative_sets - 1)};
}

std::vector<Signature> input_signatures() {
    std::vector<Mask> positive, negative;
    for (auto [a, b] : edges)
        positive.push_back((1u << a) | (1u << b));
    auto is_independent = [&](Mask assignment) {
        return std::none_of(positive.begin(), positive.end(), [&](Mask edge) {
            return (assignment & edge) == edge;
        });
    };
    for (Mask assignment = 0; assignment < (1u << vertices); ++assignment) {
        if (!is_independent(assignment)) continue;
        bool maximal = true;
        for (int v = 0; v < vertices; ++v) {
            Mask extension = assignment | (1u << v);
            if (extension != assignment && is_independent(extension)) maximal = false;
        }
        if (maximal) negative.push_back(assignment);
    }
    assert(negative.size() == negative_count);
    std::vector<Signature> signals(vertices, {0, 0});
    for (int v = 0; v < vertices; ++v) {
        for (int i = 0; i < positive_count; ++i)
            if ((positive[i] >> v) & 1) signals[v].accepted |= 1u << i;
        for (int j = 0; j < negative_count; ++j)
            if (!((negative[j] >> v) & 1)) signals[v].rejected |= 1u << j;
    }
    return signals;
}

// For each mask keep one representative of each proper two-part partition.
std::vector<std::vector<Mask>> partitions(int mask_count) {
    std::vector<std::vector<Mask>> result(mask_count);
    for (Mask mask = 1; mask < unsigned(mask_count); ++mask) {
        for (Mask part = (mask-1) & mask; part; part = (part-1) & mask)
            if (part < (mask ^ part)) result[mask].push_back(part);
    }
    return result;
}

std::vector<Mask> common_signals(const std::vector<Signature>& signals,
                                 bool positive_side, int count) {
    std::vector<Mask> common(1 << count, (1u << signals.size()) - 1);
    for (int i = 0; i < count; ++i) {
        Mask on_assignment = 0;
        for (unsigned j = 0; j < signals.size(); ++j) {
            Mask bits = positive_side ? signals[j].accepted : signals[j].rejected;
            if ((bits >> i) & 1) on_assignment |= 1u << j;
        }
        for (Mask mask = 1u << i; mask < (2u << i); ++mask)
            common[mask] = common[mask ^ (1u << i)] & on_assignment;
    }
    return common;
}

class FormulaDP {
    std::vector<std::vector<Mask>> positive_parts = partitions(positive_sets);
    std::vector<std::vector<Mask>> negative_parts = partitions(negative_sets);
    std::array<std::vector<Mask>, positive_count + 1> levels;
    std::vector<Byte> costs = std::vector<Byte>(positive_sets * negative_sets);
    std::vector<Byte> columns;

    static void improve(Byte* result, const Byte* left, const Byte* right, int length) {
        for (int i = 0; i < length; ++i)
            result[i] = std::min(result[i], Byte(left[i] + right[i]));
    }

public:
    FormulaDP() {
        for (Mask a = 1; a < positive_sets; ++a)
            levels[std::popcount(a)].push_back(a);
        std::size_t largest = 0;
        for (const auto& level : levels) largest = std::max(largest, level.size());
        columns.resize(((largest + 31) / 32 * 32) * negative_sets);
    }

    int minimum_leaves(const std::vector<Signature>& signals) {
        auto accepts = common_signals(signals, true, positive_count);
        auto rejects = common_signals(signals, false, negative_count);
        // R(A,B) first minimizes over leaves and all disjoint positive splits.
        // Next process all negative splits in increasing mask order. A transpose
        // allows these minima to be computed with contiguous vector operations.
        for (const auto& level : levels) {
            if (level.empty()) continue;
            int width = (level.size() + 31) / 32 * 32;
            for (Mask a : level) {
                Byte* dst = &costs[a * negative_sets];
                for (Mask b = 1; b < negative_sets; ++b)
                    dst[b] = (accepts[a] & rejects[b]) ? 1 : infinity;
                for (Mask part : positive_parts[a])
                    improve(dst, &costs[part * negative_sets],
                            &costs[(a ^ part) * negative_sets], negative_sets);
            }
            for (unsigned i = 0; i < level.size(); ++i)
                for (int b = 1; b < negative_sets; ++b)
                    columns[b * width + i] = costs[level[i] * negative_sets + b];
            for (Mask b = 1; b < negative_sets; ++b) {
                for (Mask part : negative_parts[b])
                    improve(&columns[b * width], &columns[part * width],
                            &columns[(b ^ part) * width], width);
            }
            for (unsigned i = 0; i < level.size(); ++i)
                for (int b = 1; b < negative_sets; ++b)
                    costs[level[i] * negative_sets + b] = columns[b * width + i];
        }
        return costs.back();
    }
};
} // namespace

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "usage: two_prefix FIRST-OP RHS (0=NOT, 1=AND, 2=OR)\n";
        return 1;
    }
    const int first = std::stoi(argv[1]), rhs = std::stoi(argv[2]);
    if (!(first == Not && rhs == 5) &&
        !((first == And || first == Or) && rhs >= 6 && rhs <= 8)) return 1;
    auto signals = input_signatures();
    signals.push_back(evaluate(Gate(first), signals[5], signals[rhs]));
    FormulaDP dp;
    int baseline = dp.minimum_leaves(signals);
    std::cout << "first " << first << " 5 " << rhs << " baseline leaves " << baseline << '\n';
    std::map<std::pair<Mask, Mask>, int> cache;
    for (Gate gate : {Not, And, Or}) {
        for (int a = 0; a < 10; ++a) {
            for (int b = (gate == Not ? a : a+1); b < (gate == Not ? a+1 : 10); ++b) {
                Signature extra = evaluate(gate, signals[a], signals[b]);
                auto key = std::pair{extra.accepted, extra.rejected};
                if (!cache.contains(key)) {
                    bool redundant = !extra.accepted || !extra.rejected ||
                        std::any_of(signals.begin(), signals.end(),
                                    [&](Signature old) { return old.dominates(extra); });
                    int value = baseline;
                    if (!redundant) {
                        signals.push_back(extra);
                        value = dp.minimum_leaves(signals);
                        signals.pop_back();
                    }
                    cache.emplace(key, value);
                }
                std::cout << gate << ' ' << a << ' ' << b << ' ' << cache.at(key) << '\n';
            }
        }
    }
}
