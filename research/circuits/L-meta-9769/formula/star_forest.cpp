#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>

using Mask = std::uint32_t;
constexpr int n = 21;
constexpr Mask all = (1u << n) - 1;

// Find a maximum clique of pairwise disjoint heavy neighborhoods.
void extend(Mask candidates, Mask chosen, const std::array<Mask,n>& disjoint,
            Mask& best) {
    if (std::popcount(chosen) > std::popcount(best)) best = chosen;
    while (candidates != 0 && std::popcount(chosen) + std::popcount(candidates) > std::popcount(best)) {
        int line = std::countr_zero(candidates);
        Mask bit = 1u << line;
        candidates ^= bit;
        extend(candidates & disjoint[line], chosen | bit, disjoint, best);
    }
}

int main(int argc, char** argv) {
    if (argc != 2) throw std::runtime_error("expected edges file");
    std::ifstream edges(argv[1]);
    std::array<Mask,n> lines{};
    int p, l, count = 0;
    while (edges >> p >> l) {
        if (p < 0 || p >= n || l < 0 || l >= n || (lines[l] & (1u << p)))
            throw std::runtime_error("invalid edge");
        lines[l] |= 1u << p;
        ++count;
    }
    if (!edges.eof() || count != 104) throw std::runtime_error("expected 104 edges");
    std::array<int,n+1> maximum;
    maximum.fill(-1);
    std::array<Mask,n+1> rows{}, cols{};
    for (Mask selected = 0; selected <= all; ++selected) {
        int size = std::popcount(selected);
        Mask easy = 0, occupied = 0, candidates = 0;
        std::array<Mask,n> inside{}, disjoint{};
        for (int j = 0; j < n; ++j) {
            inside[j] = lines[j] & selected;
            if (std::popcount(inside[j]) <= 1) {
                easy |= 1u << j;
                occupied |= inside[j];
            }
        }
        for (int j = 0; j < n; ++j)
            if (!(easy & (1u << j)) && !(inside[j] & occupied))
                candidates |= 1u << j;
        if (std::popcount(easy) + std::popcount(candidates) <= maximum[size])
            continue;
        for (int j = 0; j < n; ++j)
            for (int k = j + 1; k < n; ++k)
                if (!(inside[j] & inside[k])) {
                    disjoint[j] |= 1u << k;
                    disjoint[k] |= 1u << j;
                }
        Mask extra = 0;
        extend(candidates, 0, disjoint, extra);
        Mask kept = easy | extra;
        if (std::popcount(kept) > maximum[size]) {
            maximum[size] = std::popcount(kept);
            rows[size] = selected;
            cols[size] = kept;
        }
    }
    int optimum = 0;
    for (int i = 0; i <= n; ++i) {
        std::cout << i << ' ' << maximum[i] << ' ' << rows[i] << ' ' << cols[i] << '\n';
        optimum = std::max(optimum, i + maximum[i]);
    }
    std::cout << "maximum vertices " << optimum << '\n';
}
