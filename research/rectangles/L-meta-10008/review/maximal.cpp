#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>

using Mask = std::uint32_t;
using Design = std::array<Mask,31>;
constexpr Mask universe = 0x7fffffff;

void enumerate(const Design& rows, const Design& cols, bool transposed,
               int next, Mask chosen, Mask allowed, int size, std::map<int,int>& histogram) {
    if (size) {
        const int width = std::popcount(allowed);
        if (width < size || (transposed && width == size)) {
            return;
        }
        Mask closure = universe;
        for (Mask scan = allowed; scan; scan &= scan - 1) {
            closure &= ~cols[std::countr_zero(scan)];
        }
        if (closure == chosen) {
            ++histogram[size * width];
        }
    }
    if (size == 7) return;
    for (int row = next; row < 31; ++row) {
        enumerate(rows, cols, transposed, row + 1, chosen | (1u << row),
                  allowed & ~rows[row], size + 1, histogram);
    }
}

int main() {
    Design rows, cols{};
    for (int i = 0; i < 31; ++i) {
        if (!(std::cin >> rows[i])) return 1;
        for (int j = 0; j < 31; ++j) {
            cols[j] |= ((rows[i] >> j) & 1u) << i;
        }
    }
    std::map<int,int> histogram;
    enumerate(rows,cols,false,0,0,universe,0,histogram);
    enumerate(cols,rows,true,0,0,universe,0,histogram);
    int total=0;
    for (const auto& [area,count] : histogram) {
        std::cout << area << ' ' << count << '\n';
        total += count;
    }
    std::cout << "total " << total << '\n';
}
