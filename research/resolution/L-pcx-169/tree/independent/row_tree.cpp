// Exact leaf count for variable-query trees on the unary pigeonhole formula PHP(5,4).
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <vector>

namespace {
constexpr unsigned pigeons = 5;
constexpr unsigned holes = 4;
constexpr unsigned row_types = 81;
constexpr unsigned all_holes = 15;
constexpr std::array<unsigned, holes> power_of_three = {1, 3, 9, 27};

using Rows = std::array<unsigned, pigeons>;
std::uint32_t binomial[row_types + pigeons][pigeons + 1] = {};
unsigned occupied[row_types] = {}, excluded[row_types] = {}, unknown[row_types] = {};

std::uint32_t multiset_rank(const Rows& rows) {
    std::uint32_t rank = 0;
    for (unsigned i = 0; i < pigeons; ++i)
        rank += binomial[rows[i] + i][i + 1];
    return rank;
}

std::uint32_t child_rank(Rows rows, unsigned i, unsigned new_row) {
    while (i + 1 < pigeons && new_row > rows[i + 1]) {
        rows[i] = rows[i + 1];
        ++i;
    }
    rows[i] = new_row;
    return multiset_rank(rows);
}

void initialize() {
    for (unsigned n = 0; n < row_types + pigeons; ++n) {
        binomial[n][0] = 1;
        for (unsigned k = 1; k <= std::min(pigeons, n); ++k)
            binomial[n][k] = binomial[n-1][k-1] + binomial[n-1][k];
    }
    for (unsigned row = 0; row < row_types; ++row) {
        for (unsigned h = 0; h < holes; ++h) {
            unsigned digit = (row / power_of_three[h]) % 3;
            if (digit == 2) occupied[row] |= 1u << h;
            else if (digit == 1) excluded[row] |= 1u << h;
            else unknown[row] |= 1u << h;
        }
    }
}

bool falsifies_axiom(const Rows& rows) {
    unsigned taken = 0;
    for (unsigned row : rows) {
        if (excluded[row] == all_holes || (occupied[row] & taken))
            return true;
        taken |= occupied[row];
    }
    return false;
}
} // namespace

int main() {
    initialize();
    const std::size_t size = binomial[row_types + pigeons - 1][pigeons];
    std::vector<std::uint32_t> leaves(size, 1);
    std::size_t visited = 0, nonterminal = 0, distinct_choices = 0, labelled_choices = 0;
    std::uint32_t largest = 0;
    Rows rows{};

    auto visit = [&]() {
        std::uint32_t rank = multiset_rank(rows);
        if (rank != size - 1 - visited++) {
            std::cerr << "Multisets were not visited in descending rank order.\n";
            std::exit(2);
        }
        if (falsifies_axiom(rows)) return;
        ++nonterminal;
        auto best = std::numeric_limits<std::uint32_t>::max();
        for (unsigned i = 0; i < pigeons; ++i) {
            unsigned row = rows[i];
            labelled_choices += std::bitset<holes>(unknown[row]).count();
            if (i > 0 && rows[i-1] == row) continue;
            for (unsigned h = 0; h < holes; ++h) {
                if ((unknown[row] & (1u << h)) == 0) continue;
                ++distinct_choices;
                auto no = child_rank(rows, i, row + power_of_three[h]);
                auto yes = child_rank(rows, i, row + 2 * power_of_three[h]);
                if (no <= rank || yes <= rank || no >= size || yes >= size) {
                    std::cerr << "Child is outside the completed part of the table.\n";
                    std::exit(3);
                }
                best = std::min(best, leaves[no] + leaves[yes]);
            }
        }
        if (best == std::numeric_limits<std::uint32_t>::max()) {
            std::cerr << "Reached a complete assignment without a falsified axiom.\n";
            std::exit(4);
        }
        largest = std::max(largest, best);
        leaves[rank] = best;
    };

    // Fix the largest row first and enumerate the smaller entries in descending order.
    auto enumerate = [&](auto&& self, int i, int cap) -> void {
        if (i < 0) {
            visit();
            return;
        }
        for (int row = cap; row >= 0; --row) {
            rows[i] = row;
            self(self, i - 1, row);
        }
    };
    enumerate(enumerate, pigeons - 1, row_types - 1);
    if (visited != size) return 5;
    std::cout << "five ternary rows, four labelled columns\n"
              << "ranked multisets " << size << " nonterminal " << nonterminal
              << " terminal " << size - nonterminal << '\n'
              << "inequivalent variable choices over nonterminal row multisets " << distinct_choices << '\n'
              << "all labelled query choices over those states " << labelled_choices << '\n'
              << "maximum optimal value " << largest << " empty-state optimum " << leaves[0] << '\n';
}
