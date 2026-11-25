// g++ -std=c++20 -O2 ConicTriples.cpp -o ./conic-triples && ./conic-triples
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Mask = std::uint32_t;
constexpr Mask universe = (Mask{1} << 31) - 1;
constexpr std::array<Mask, 31> occupied = {
    1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105,
    67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146,
    1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688,
    218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091,
    1109426182, 71368717, 142737434, 285474868, 570949736};

struct Rectangle { Mask points, lines; };

void check(bool condition) { if (!condition) std::abort(); }

void extend(int next, int remaining, Rectangle partial,
            std::vector<Rectangle>& eligible) {
    if (remaining == 0) {
        const int count = std::popcount(partial.lines);
        check(count <= 10);
        if (count == 10) eligible.push_back(partial);
        return;
    }
    for (int i = next; i <= 31 - remaining; ++i) {
        extend(i + 1, remaining - 1, {partial.points | (Mask{1} << i),
                                      partial.lines & ~occupied[i]}, eligible);
    }
}

void verify_plane(const std::array<Mask,31>& rows) {
    for (int p = 0; p < 31; ++p) {
        check(std::popcount(rows[p]) == 6);
        for (int q = 0; q < 31; ++q) if (p != q) {
            check(std::popcount(rows[p] & rows[q]) == 1);
            check((rows[q] & ~rows[p]) != 0);
        }
    }
    for (int j = 0; j < 31; ++j) {
        Mask line = 0;
        for (int p = 0; p < 31; ++p) if ((rows[p] >> j) & 1)
            line |= Mask{1} << p;
        check(std::popcount(line) == 6);
        for (Mask a = line; a; a = (a-1) & line) {
            Mask allowed = universe;
            for (Mask r = a; r; r &= r-1) allowed &= ~rows[std::countr_zero(r)];
            check(std::popcount(a) * std::popcount(allowed) <= 45);
        }
    }
}

int main() {
    std::array<Mask,31> transpose{};
    for (int i = 0; i < 31; ++i)
        for (int j = 0; j < 31; ++j)
            if ((occupied[i] >> j) & 1) transpose[j] |= Mask{1} << i;
    verify_plane(occupied);
    verify_plane(transpose);
    for (int r = 0; r < 31; ++r) {
        const Mask shifted = ((occupied[r] << 1) & universe) | (occupied[r] >> 30);
        check(shifted == occupied[(r + 1) % 31]);
    }
    const Mask target = universe ^ occupied[0];
    std::vector<Rectangle> eligible;
    extend(1, 5, {1, target}, eligible);
    check(eligible.size() == 600);
    std::vector<std::array<int,2>> partners(eligible.size());
    std::array<int,2> triples{};
    for (std::size_t i = 0; i < eligible.size(); ++i) {
        const auto a = eligible[i];
        for (std::size_t j = i + 1; j < eligible.size(); ++j) {
            const auto b = eligible[j];
            for (std::size_t k = j + 1; k < eligible.size(); ++k) {
                const auto c = eligible[k];
                if ((a.lines | b.lines | c.lines) != target) continue;
                check((a.points & b.points) == 1 && (a.points & c.points) == 1 &&
                      (b.points & c.points) == 1);
                std::array<int,3> overlaps = {
                    std::popcount(a.lines & b.lines), std::popcount(a.lines & c.lines),
                    std::popcount(b.lines & c.lines)};
                std::sort(overlaps.begin(), overlaps.end());
                const int type = overlaps == std::array<int,3>{2,2,2} ? 0 : 1;
                check(type == 0 || overlaps == std::array<int,3>{0,0,5});
                ++partners[i][type]; ++partners[j][type]; ++partners[k][type];
                ++triples[type];
            }
        }
    }
    for (const auto& pair : partners) check(pair == std::array<int,2>{20,3});
    check(triples == std::array<int,2>{4000,600});
    std::cout << "600 eligible rectangles; 4000 triples with overlaps (2,2,2), "
                 "600 with (0,0,5); every first rectangle has 20+3 partner pairs.\n";
}
