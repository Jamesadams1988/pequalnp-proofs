// Enumerate all useful fan-in-two AND/OR/NOT circuits of a prescribed budget.
// Only targets depending on every listed input are eligible for the live-wire prune.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Table = std::uint32_t;
struct Gate { int left, right; char op; };
struct Goal { Table table; int minimum = -1; std::vector<Gate> witness; };
struct Search {
    int n, budget;
    Table full;
    std::array<Table, 12> wires{};
    std::array<Gate, 7> gates{};
    std::vector<Goal> goals;
    std::uint64_t finals = 0;

    void visit(int depth, unsigned unused) {
        int next = n + depth;
        for (int a = 0; a < next; ++a) {
            for (int b = a; b < next; ++b) {
                unsigned remaining = unused & ~(1U << a) & ~(1U << b);
                // After this gate, the old wires still unused and this new output
                // must fit in the remaining fan-in slots of a connected circuit.
                if (std::popcount(remaining) > budget - depth - 1) continue;
                for (char op : {'&', '|', '~'}) {
                    if ((op == '~') != (a == b)) continue;
                    Gate gate{a, b, op};
                    if (depth > 0 && b < next - 1) {
                        Gate prev = gates[depth - 1];
                        if (std::array<int, 3>{a, b, op} < std::array<int, 3>{prev.left, prev.right, prev.op}) continue;
                    }
                    Table x = wires[a], y = wires[b];
                    Table value = op == '&' ? (x & y) : op == '|' ? (x | y) : (full ^ x);
                    if (value == 0 || value == full) continue;
                    if (std::find(wires.begin(), wires.begin() + next, value) != wires.begin() + next) continue;
                    gates[depth] = gate;
                    if (depth + 1 == budget) {
                        ++finals;
                        for (auto& goal : goals) {
                            if (value == goal.table && goal.minimum < 0) {
                                goal.minimum = budget;
                                goal.witness.assign(gates.begin(), gates.begin() + budget);
                            }
                        }
                    } else {
                        wires[next] = value;
                        visit(depth + 1, remaining | (1U << next));
                    }
                }
            }
        }
    }
};

int main(int argc, char** argv) {
    if (argc < 4) throw std::invalid_argument("usage: search INPUTS MAX_GATES TARGET ...");
    int n = std::stoi(argv[1]), cap = std::stoi(argv[2]);
    if (n < 2 || n > 5 || cap < 0 || cap > 7) throw std::invalid_argument("need 2..5 inputs and 0..7 gates");
    int rows = 1 << n;
    Table mask = rows == 32 ? std::numeric_limits<Table>::max() : (1U << rows) - 1;
    Search s{n, 0, mask};
    for (int i = 0; i < n; ++i)
        for (int r = 0; r < rows; ++r) if ((r >> i) & 1) s.wires[i] |= 1U << r;
    for (int k = 3; k < argc; ++k) {
        auto t = std::stoull(argv[k], nullptr, 0);
        if (t > mask) throw std::invalid_argument("target exceeds row width");
        for (int i = 0; i < n; ++i) {
            bool essential = false;
            for (int r = 0; r < rows; ++r)
                if (((t >> r) ^ (t >> (r ^ (1 << i)))) & 1) essential = true;
            if (!essential) throw std::invalid_argument("compressed targets must use every input");
        }
        s.goals.push_back({static_cast<Table>(t)});
    }
    // Every connected circuit with n essential inputs and g gates uses at
    // least n+g-1 edges and at most 2g, hence at least n-1 gates.
    for (s.budget = n - 1; s.budget <= cap; ++s.budget) {
        s.finals = 0;
        s.visit(0, (1U << n) - 1);
        std::cerr << "inputs=" << n << " gates=" << s.budget << " completed=" << s.finals << '\n';
        if (std::all_of(s.goals.begin(), s.goals.end(), [](const Goal& g){return g.minimum >= 0;})) break;
    }
    for (const auto& g : s.goals) {
        std::cout << g.table << ' ' << g.minimum;
        for (auto gate : g.witness) std::cout << ' ' << gate.op << ',' << gate.left << ',' << gate.right;
        std::cout << '\n';
    }
}
