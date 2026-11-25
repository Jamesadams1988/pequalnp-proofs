// Exhaust every smaller binary gate budget for the six distinct five-input
// restrictions. NOT is free on every operand and on the output.
#include <array>
#include <bit>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

using Table = std::uint32_t;
using Signals = std::vector<Table>;
constexpr std::uint64_t target = 0xfe80fe00fe00e800ULL;

Table restrict_input(unsigned input, unsigned value) {
    Table result = 0;
    unsigned row = 0;
    for (unsigned full = 0; full < 64; ++full) {
        if (((full >> input) & 1) == value) {
            if ((target >> full) & 1) result |= Table{1} << row;
            ++row;
        }
    }
    return result;
}

// The sought output must be constant on every class of rows that the
// current live signals cannot distinguish.
bool separates_output(const Signals& signals, Table goal) {
    for (Table ones = goal; ones; ones &= ones - 1) {
        unsigned row = std::countr_zero(ones);
        Table zeros = ~goal;
        for (Table signal : signals) {
            zeros &= ((signal >> row) & 1) ? signal : ~signal;
            if (!zeros) break;
        }
        if (zeros) return false;
    }
    return true;
}

bool fits(const Signals& signals, Table goal, unsigned remaining) {
    // Every live signal must feed the output. A binary gate can decrease the
    // live count by at most one, even when both of its operands die here.
    if (signals.size() > remaining + 1) return false;
    for (Table signal : signals) {
        if (signal == goal || ~signal == goal) return true;
    }
    if (!remaining || !separates_output(signals, goal)) return false;

    for (unsigned i = 0; i < signals.size(); ++i) {
        for (unsigned j = i + 1; j < signals.size(); ++j) {
            Table a = signals[i], b = signals[j];
            for (Table gate : {a & b, ~a & b, a & ~b, ~a & ~b}) {
                // A gate returning a constant or an existing signal in
                // either polarity can be eliminated from a shortest circuit.
                if (!gate || !~gate) continue;
                bool redundant = false;
                for (Table signal : signals) {
                    if (gate == signal || ~gate == signal) redundant = true;
                }
                if (redundant) continue;
                for (unsigned keep = 0; keep < 4; ++keep) {
                    if (signals.size() - 1 + std::popcount(keep) > remaining) continue;
                    Signals next{gate};
                    for (unsigned k = 0; k < signals.size(); ++k) {
                        if ((k != i || (keep & 1)) && (k != j || (keep & 2))) {
                            next.push_back(signals[k]);
                        }
                    }
                    if (fits(next, goal, remaining - 1)) return true;
                }
            }
        }
    }
    return false;
}

int main() {
    Signals inputs;
    for (unsigned i = 0; i < 5; ++i) {
        Table column = 0;
        for (unsigned row = 0; row < 32; ++row) {
            if ((row >> i) & 1) column |= Table{1} << row;
        }
        inputs.push_back(column);
    }
    // The matching upper bounds are checked by FaceWitnesses.lean.
    constexpr unsigned minimum[6][2] = {{6,8},{6,8},{6,8},{4,8},{8,7},{8,7}};
    for (unsigned i : {0u,3u,4u}) {
        for (unsigned value : {0u,1u}) {
            Table goal = restrict_input(i, value);
            for (unsigned j = 0; j < 5; ++j) {
                bool essential = false;
                for (unsigned row = 0; row < 32; ++row) {
                    essential |= (((goal >> row) ^ (goal >> (row ^ (1u << j)))) & 1) != 0;
                }
                if (!essential) return 1;
            }
            // Inputs 0–2 are exchangeable, as are inputs 4 and 5. Verify the
            // claimed face identity in the surviving inputs' natural order.
            unsigned group_end = (i == 0) ? 3 : (i == 3) ? 4 : 6;
            for (unsigned k = i; k < group_end; ++k) {
                if (restrict_input(k, value) != goal || minimum[k][value] != minimum[i][value]) return 2;
            }
            if (fits(inputs, goal, minimum[i][value] - 1)) return 3;
            std::cout << "x" << i << "=" << value << " 0x" << std::hex << goal
                      << std::dec << " requires at least " << minimum[i][value]
                      << " binary gates with free complementation\n";
        }
    }
    // Positive control: five-way conjunction needs four binary gates.
    return fits(inputs, Table{1} << 31, 4) ? 0 : 4;
}
