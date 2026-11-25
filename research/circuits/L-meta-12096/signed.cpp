// Complete search for a six-input circuit with free complemented wires.
// Compile: g++ -std=c++20 -O3 -o signed signed.cpp
// Run: ./signed BUDGET [MONOTONE=0] [TARGET=0xfe80fe00fe00e800]
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Table = std::uint64_t;
using Block = unsigned __int128;
using Permutation = std::array<int, 64>;
constexpr int inputs = 6;
constexpr int max_budget = 12;
constexpr Table assigned = 0xfe80fe00fe00e800ULL;

struct Wire {
    Table table;
    Block positives;
    Block negatives;
    Block separates;
};

// Nonzero interned wire IDs occupy a sorted prefix. The zero suffix also
// records the count, so equality compares the entire live-wire bank.
struct Bank {
    std::array<std::uint32_t, max_budget + 1> ids{};
    bool operator==(const Bank&) const = default;
};

std::uint64_t hash_bank(const Bank& bank) {
    std::uint64_t hash = 1469598103934665603ULL;
    for (auto id : bank.ids) hash = (hash ^ id) * 1099511628211ULL;
    return hash;
}

struct BankHash {
    std::size_t operator()(const Bank& b) const { return hash_bank(b); }
};

struct Search {
    int budget;
    bool monotone;
    Table target;
    Block all_pairs;
    std::vector<Wire> wires{{}};
    std::unordered_map<Table, std::uint32_t> ids;
    std::vector<Permutation> permutations;
    std::unordered_set<Bank, BankHash> first_moves;
    std::array<std::vector<Bank>, max_budget + 1> memo;
    struct Chosen { Table x, y, out; int operation; };
    std::array<Chosen, max_budget> path{};
    int found_length = 0;
    std::array<std::uint64_t, max_budget + 1> visits{};
    std::array<std::uint64_t, max_budget + 1> distinct{};

    Block separation(Block hi, Block lo) const {
        return monotone ? (hi & ~lo) : (hi ^ lo);
    }

    std::uint32_t intern(Table table, Block hi, Block lo) {
        auto [it, inserted] = ids.try_emplace(table, wires.size());
        if (inserted) wires.push_back({table, hi, lo, separation(hi, lo)});
        return it->second;
    }

    static Table permute(Table wire, const Permutation& map) {
        Table result = 0;
        while (wire) {
            result |= Table(1) << map[std::countr_zero(wire)];
            wire &= wire - 1;
        }
        return result;
    }

    void get_symmetries() {
        std::array<int, 3> triple = {0, 1, 2};
        do {
            for (int swap = 0; swap < 2; ++swap) {
                Permutation map{};
                for (int r = 0; r < 64; ++r) {
                    int image = r & 8;
                    for (int j = 0; j < 3; ++j) image |= ((r >> triple[j]) & 1) << j;
                    image |= ((r >> (4 + swap)) & 1) << 4;
                    image |= ((r >> (5 - swap)) & 1) << 5;
                    map[r] = image;
                }
                if (permute(target, map) == target) permutations.push_back(map);
            }
        } while (std::next_permutation(triple.begin(), triple.end()));
    }

    bool repeated_first_move(const Bank& bank, int count) {
        // Every candidate key is the image of this bank under a verified
        // target symmetry. Missing interned images only lose opportunities
        // to reuse work. They cannot merge inequivalent banks.
        Bank best = bank;
        for (const auto& map : permutations) {
            Bank transformed{};
            bool have_all = true;
            for (int i = 0; i < count; ++i) {
                auto it = ids.find(permute(wires[bank.ids[i]].table, map));
                if (it == ids.end()) { have_all = false; break; }
                transformed.ids[i] = it->second;
            }
            if (have_all) {
                std::sort(transformed.ids.begin(), transformed.ids.begin() + count);
                best.ids = std::min(best.ids, transformed.ids);
            }
        }
        return !first_moves.insert(best).second;
    }

    bool seen_before(const Bank& bank, int depth) {
        // Fixed capacity. A collision evicts the old full key, which can
        // cause recomputation. A hash match alone never discards a state.
        auto& cache = memo[depth];
        if (cache.empty()) cache.resize(1u << (depth < 8 ? 16 : 12));
        Bank& slot = cache[hash_bank(bank) & (cache.size() - 1)];
        if (slot == bank) return true;
        slot = bank;
        return false;
    }

    bool separates_all_rows(const Bank& bank, int count) const {
        // Signed wires must distinguish every target-positive, target-negative
        // row pair. Under monotone gates, some wire must be 1 on the positive
        // and 0 on the negative. Computing all pairs here supplements the
        // inexpensive subset test before admitting a move.
        for (Table todo = target; todo; todo &= todo - 1) {
            int row = std::countr_zero(todo);
            Table indistinguishable = ~target;
            for (int j = 0; j < count && indistinguishable; ++j) {
                Table w = wires[bank.ids[j]].table;
                if ((w >> row) & 1) indistinguishable &= w;
                else if (!monotone) indistinguishable &= ~w;
            }
            if (indistinguishable) return false;
        }
        return true;
    }

    enum Op { both, either, left_only, right_only };

    template <typename Bits>
    static Bits gate(Op op, Bits x, Bits y) {
        switch (op) {
        case both: return x & y;
        case either: return x | y;
        case left_only: return x & ~y;
        case right_only: return ~x & y;
        }
        std::abort();
    }

    bool run(const Bank& bank, int count, int depth) {
        ++visits[depth];
        if (depth == 0 || count < 2 || seen_before(bank, depth)) return false;
        if (!separates_all_rows(bank, count)) return false;
        ++distinct[depth];
        for (int i = 0; i < count; ++i) {
            for (int j = i + 1; j < count; ++j) {
                // Copy because intern() can reallocate the wire vector.
                Wire a = wires[bank.ids[i]], b = wires[bank.ids[j]];
                Bank rest{};
                Block other_coverage = 0;
                int remaining = 0;
                for (int q = 0; q < count; ++q) {
                    if (q == i || q == j) continue;
                    rest.ids[remaining++] = bank.ids[q];
                    other_coverage |= wires[bank.ids[q]].separates;
                }
                int operations = monotone ? 2 : 4;
                for (int choice = 0; choice < operations; ++choice) {
                    Op op = static_cast<Op>(choice);
                    Table result = gate(op, a.table, b.table);
                    path[budget-depth] = {a.table, b.table, result, choice};
                    if (result == target) { found_length=budget-depth+1; return true; }
                    if (result == 0 || result == a.table || result == b.table) continue;
                    Block hi = gate(op, a.positives, b.positives);
                    Block lo = gate(op, a.negatives, b.negatives);
                    Block coverage = other_coverage | separation(hi, lo);
                    for (unsigned keep = 0; keep < 4; ++keep) {
                        int size = remaining + 1 + std::popcount(keep);
                        // After this gate there are depth-1 gates left. Each
                        // can reduce the number of needed wires by at most one.
                        if (size > depth) continue;
                        Block covered = coverage;
                        if (keep & 1) covered |= a.separates;
                        if (keep & 2) covered |= b.separates;
                        if (covered != all_pairs) continue;
                        std::uint32_t id = intern(result, hi, lo);
                        if (std::binary_search(bank.ids.begin(), bank.ids.begin()+count, id)) continue;
                        Bank next = rest;
                        int k = remaining;
                        next.ids[k++] = id;
                        if (keep & 1) next.ids[k++] = bank.ids[i];
                        if (keep & 2) next.ids[k++] = bank.ids[j];
                        std::sort(next.ids.begin(), next.ids.begin() + size);
                        if (depth == budget && repeated_first_move(next, size)) continue;
                        if (run(next, size, depth - 1)) return true;
                    }
                }
            }
        }
        return false;
    }

    bool solve() {
        get_symmetries();
        std::vector<std::pair<int,int>> pairs;
        for (int y = 0; y < 64; ++y) if ((target >> y) & 1) {
            for (int x = 0; x < 64; ++x) if (!((target >> x) & 1)) {
                bool minimal_y = true, maximal_x = true;
                for (int j = 0; j < inputs; ++j) {
                    if (((y >> j) & 1) && ((target >> (y ^ (1 << j))) & 1)) minimal_y = false;
                    if (!((x >> j) & 1) && !((target >> (x | (1 << j))) & 1)) maximal_x = false;
                }
                if ((minimal_y && maximal_x) || std::popcount(unsigned(x^y)) == 1) {
                    if (pairs.size() < 127) pairs.emplace_back(y,x);
                }
            }
        }
        all_pairs = (Block(1) << pairs.size()) - 1;
        Bank bank{};
        for (int j = 0; j < inputs; ++j) {
            Table wire = 0;
            bool essential = false;
            for (int r = 0; r < 64; ++r) {
                if ((r >> j) & 1) wire |= Table(1) << r;
                if (((target >> r) ^ (target >> (r ^ (1<<j)))) & 1) essential = true;
            }
            if (!essential) throw std::runtime_error("target must depend on every input");
            Block hi = 0, lo = 0;
            for (unsigned p = 0; p < pairs.size(); ++p) {
                auto [y,x] = pairs[p];
                hi |= Block((y >> j) & 1) << p;
                lo |= Block((x >> j) & 1) << p;
            }
            bank.ids[j] = intern(wire, hi, lo);
        }
        return run(bank, inputs, budget);
    }
};

int main(int argc, char** argv) {
    if (argc < 2 || argc > 4) { std::fprintf(stderr,"signed BUDGET [MONOTONE=0] [TABLE]\n"); return 2; }
    int budget = std::atoi(argv[1]);
    bool monotone = argc>2 && std::atoi(argv[2]);
    Table target = argc>3 ? std::strtoull(argv[3],nullptr,0) : assigned;
    if (budget < 0 || budget > max_budget || (target & 1)) {
        std::fprintf(stderr,"budget must be 0..12 and the table must vanish at zero\n"); return 2;
    }
    Search search{budget, monotone, target};
    bool fits = search.solve();
    std::printf("budget=%d basis=%s table=0x%016llx fits=%d symmetries=%zu wire_tables=%zu\n",
                budget, monotone?"monotone":"free-NOT", (unsigned long long)target, fits,
                search.permutations.size(), search.wires.size()-1);
    if (fits) {
        std::unordered_map<Table,int> resolved;
        for (int i=0; i<inputs; ++i) resolved[search.wires[i+1].table]=i;
        for (int i=0; i<search.found_length; ++i) {
            auto step=search.path[i];
            std::printf("wire %d = op%d(%d,%d)\n",inputs+i,step.operation,resolved.at(step.x),resolved.at(step.y));
            resolved[step.out]=inputs+i;
        }
    }
    for (int d=budget; d>=0; --d) std::printf("remaining=%d visits=%llu distinct_covering=%llu\n",
            d, (unsigned long long)search.visits[d], (unsigned long long)search.distinct[d]);
}
