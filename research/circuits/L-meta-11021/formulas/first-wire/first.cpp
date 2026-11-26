#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Mask = std::uint32_t;
constexpr int inputCount = 9;
const std::vector<std::pair<int,int>> edges = {
    {0,4},{0,5},{1,5},{2,6},{3,6},{0,7},{2,7},{4,7},{1,8},{3,8},{4,8},{6,8}
};

int main(int argc, char** argv) {
    if (argc != 4) return 2;
    std::string operation = argv[1];
    int left = std::stoi(argv[2]), right = std::stoi(argv[3]);
    if (left < 0 || right > 8 || left > right ||
        (operation == "not" && left != right) ||
        ((operation == "and" || operation == "or") && left == right) ||
        (operation != "not" && operation != "and" && operation != "or" && operation != "raw"))
        throw std::invalid_argument("use raw 0 0, not i i, and i j, or or i j");
    constexpr int maxLeaves = 17;
    auto output = [](int assignment) {
        for (auto [i,j] : edges)
            if ((assignment >> i) & (assignment >> j) & 1) return true;
        return false;
    };
    std::vector<int> tests;
    for (auto [i,j] : edges) tests.push_back((1 << i) | (1 << j));
    for (int x = 0; x < (1 << inputCount); ++x) {
        if (output(x)) continue;
        bool maximal = true;
        for (int i = 0; i < inputCount; ++i)
            if (!(x >> i & 1) && !output(x | 1 << i)) maximal = false;
        if (maximal) tests.push_back(x);
    }
    if (tests.size() != 25) throw std::logic_error("unexpected boundary size");
    Mask positive = (1u << edges.size()) - 1;
    Mask full = (1u << tests.size()) - 1;
    std::vector<std::vector<Mask>> layer(maxLeaves + 1);
    std::vector<unsigned char> dominated(full + 1), generated(full + 1);
    auto insert = [&](int leaves, Mask errors) {
        layer[leaves].push_back(errors);
        // Once a superseding error set is dominated, all of its supersets already are.
        auto mark = [&](auto&& self, Mask m, Mask free) -> void {
            if (dominated[m]) return;
            dominated[m] = true;
            while (free) {
                Mask bit = free & -free;
                free ^= bit;
                self(self, m | bit, free);
            }
        };
        mark(mark, errors, full ^ errors);
    };
    auto feature = [&](int x, int i) {
        bool a = (x >> left) & 1, b = (x >> right) & 1;
        bool first = operation == "and" ? a && b : operation == "or" ? a || b : !a;
        if (i < 9) return bool((x >> i) & 1);
        return first;
    };
    for (int i = 0; i < (operation == "raw" ? 9 : 10); ++i) {
        Mask errors = 0;
        for (unsigned t = 0; t < tests.size(); ++t)
            if (feature(tests[t], i) != (t < edges.size())) errors |= 1u << t;
        if (!dominated[errors]) insert(1, errors);
    }
    for (int leaves = 2; leaves <= maxLeaves; ++leaves) {
        std::vector<Mask> candidates;
        for (int h = 1; h <= leaves / 2; ++h) {
            for (auto x : layer[h]) for (auto y : layer[leaves-h]) {
                if (h * 2 == leaves && x > y) continue;
                auto common = x & y, different = x ^ y;
                for (Mask z : {common | (different & positive), common | (different & ~positive)}) {
                    if (!z) {
                        std::cout << operation<<" "<<left<<" "<<right<<" "<<leaves<<"\n";
                        return 0;
                    }
                    if (!generated[z] && !dominated[z]) {
                        candidates.push_back(z);
                        generated[z] = true;
                    }
                }
            }
        }
        std::sort(candidates.begin(), candidates.end(), [](Mask x, Mask y) {
            int a = std::popcount(x), b = std::popcount(y);
            return a != b ? a < b : x < y;
        });
        for (Mask z : candidates) if (!dominated[z]) insert(leaves, z);
    }
    std::cout << "excluded " << operation << " " << left << " " <<right;
    std::cout << " through " << maxLeaves << " leaves\n";
}
