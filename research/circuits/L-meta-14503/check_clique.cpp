#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>

using Signature = std::uint16_t;
std::array<int, 65536> size;
std::array<Signature, 9> wires;
std::array<std::uint64_t, 6> prefixes;

// Treat both Boolean constants as free. AND/OR with a constant and NOT of a
// constant yield an existing wire or another constant, so constants can be
// omitted from this recursion. Omitting repeated signals loses no output:
// later gates can use the earlier copy.
void visit(int used) {
    ++prefixes[used];
    int count = 4 + used;
    auto accept = [&](Signature value) {
        if (value == 0 || value == 65535) return;
        size[value] = std::min(size[value], used + 1);
        if (used == 5) return;
        if (std::find(wires.begin(), wires.begin()+count, value) != wires.begin()+count) return;
        wires[count] = value;
        visit(used + 1);
    };
    // If the final gate ignores the last intermediate, omit that intermediate
    // and compute the same output earlier. This prune is applied only at
    // depth five, with a single gate left and no descendants to enumerate.
    int first = (used == 5) ? count-1 : 0;
    for (int i = first; i < count; ++i) {
        accept(static_cast<Signature>(~wires[i]));
        for (int j = 0; j < i; ++j) {
            accept(wires[i] & wires[j]);
            accept(wires[i] | wires[j]);
        }
    }
}

int main() {
    size.fill(100);
    size[0] = size[65535] = 0;
    Signature k4 = 0, triangle = 0, parity = 0;
    for (unsigned r = 0; r < 16; ++r) {
        for (unsigned i = 0; i < 4; ++i)
            if (r & (1U << i)) wires[i] |= 1U << r;
        if (std::popcount(r) >= 2) k4 |= 1U << r;
        if (std::popcount(r & 7U) >= 2) triangle |= 1U << r;
        if (std::popcount(r & 3U) == 1) parity |= 1U << r;
    }
    for (int i = 0; i < 4; ++i) size[wires[i]] = 0;
    visit(0);
    std::cout << "K4 signature " << k4 << ", attainable through six gates = " << (size[k4] <= 6) << '\n';
    assert(size[k4] > 6);
    assert(size[triangle] == 4);
    assert(size[parity] == 4);
    assert(size[1U << 15] == 3);
    assert(size[static_cast<Signature>(~wires[0])] == 1);
    std::cout << "Control minimums for triangle, XOR(x0,x1), four-way AND, NOT(x0): "
              << size[triangle] << ", " << size[parity] << ", " << size[1U << 15] << ", "
              << size[static_cast<Signature>(~wires[0])] << '\n';
    std::cout << "Prefixes by depth:";
    for (auto n : prefixes) std::cout << ' ' << n;
    std::cout << "\nMinimum signature counts by size 0..6:";
    for (int i = 0; i <= 6; ++i) std::cout << ' ' << std::count(size.begin(), size.end(), i);
    std::cout << '\n';
    auto [a,b,c,d] = std::array{wires[0],wires[1],wires[2],wires[3]};
    // 7 gates, with the two same-pair conjunctions and a cross-pair product.
    assert(((a & b) | (c & d) | ((a | b) & (c | d))) == k4);
}
