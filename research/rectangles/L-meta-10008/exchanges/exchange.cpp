#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = uint32_t;
constexpr int size = 31;
struct Box { Mask rows, cols; };
struct Cell { int row, col; Mask owners; };

// Incompatible cells are adjacent. Each color class extends to its row x column product.
class Coloring {
    const std::vector<std::vector<int>>& neighbors;
    int colorCount, budget;
    std::vector<Mask> domains;
    std::vector<std::vector<int>> neighborColorCounts;

    bool visit(int left, int used) {
        if (left == 0) return true;
        if (++nodes > budget) {
            cutoff = true;
            return false;
        }
        int vertex = -1, minDomain = colorCount + 1, maxDegree = -1;
        for (size_t v = 0; v < colors.size(); ++v) {
            if (colors[v] >= 0) continue;
            int options = std::popcount(domains[v]);
            if (!options) return false;
            int degree = static_cast<int>(neighbors[v].size());
            if (options < minDomain || (options == minDomain && degree > maxDegree)) {
                vertex = static_cast<int>(v);
                minDomain = options;
                maxDegree = degree;
            }
        }
        // All unused color labels are interchangeable. Try only the first unused one.
        auto choices = domains[vertex] & ((Mask{1} << (used + 1)) - 1);
        while (choices) {
            int c = std::countr_zero(choices);
            choices &= choices - 1;
            colors[vertex] = c;
            for (int v : neighbors[vertex]) {
                if (++neighborColorCounts[v][c] == 1) domains[v] &= ~(Mask{1} << c);
            }
            if (visit(left - 1, std::max(used, c + 1))) return true;
            for (int v : neighbors[vertex]) {
                if (--neighborColorCounts[v][c] == 0) domains[v] |= Mask{1} << c;
            }
            colors[vertex] = -1;
            if (cutoff) break;
        }
        return false;
    }

public:
    std::vector<int> colors;
    int nodes = 0;
    bool cutoff = false;
    Coloring(const std::vector<std::vector<int>>& graph, int k, int nodeLimit)
        : neighbors(graph), colorCount(k), budget(nodeLimit),
          domains(graph.size(), (Mask{1} << k) - 1),
          neighborColorCounts(graph.size(), std::vector<int>(k)), colors(graph.size(), -1) {}
    bool run() { return visit(static_cast<int>(colors.size()), 0); }
};

int main(int argc, char** argv) {
    if (argc != 4) {
        std::cerr << "usage: exchange DELETIONS COLORS NODE_LIMIT < instance.txt\n";
        return 2;
    }
    int deletedCount = std::stoi(argv[1]), k = std::stoi(argv[2]), budget = std::stoi(argv[3]);
    std::array<Mask, size> rows{};
    for (auto& row : rows) if (!(std::cin >> row) || row >> size) return 2;
    std::vector<Box> donor;
    Box box{};
    while (std::cin >> box.rows >> box.cols) donor.push_back(box);
    int boxCount = static_cast<int>(donor.size());
    if (boxCount == 0 || boxCount > 30 || k < 0 || k > 30 || deletedCount < 0 ||
        deletedCount > boxCount || budget <= 0 || !std::cin.eof()) return 2;

    std::vector<Cell> zeros;
    for (int i = 0; i < size; ++i) {
        for (int j = 0; j < size; ++j) {
            Mask owners = 0;
            for (int h = 0; h < boxCount; ++h) {
                if ((donor[h].rows >> i) & (donor[h].cols >> j) & 1)
                    owners |= Mask{1} << h;
            }
            bool isOne = (rows[i] >> j) & 1;
            if (isOne && owners) throw std::runtime_error("donor covers a one");
            if (!isOne) zeros.push_back({i, j, owners});
        }
    }
    int tested = 0, unknown = 0, largest = 0;
    long long total = 0;
    for (Mask deleted = 0; deleted < (Mask{1} << boxCount); ++deleted) {
        if (std::popcount(deleted) != deletedCount) continue;
        std::vector<Cell> cells;
        for (auto v : zeros) if (!(v.owners & ~deleted)) cells.push_back(v);
        std::vector<std::vector<int>> adj(cells.size());
        for (size_t x = 0; x < cells.size(); ++x) {
            for (size_t y = 0; y < x; ++y) {
                auto a = cells[x], b = cells[y];
                if (((rows[a.row] >> b.col) | (rows[b.row] >> a.col)) & 1) {
                    adj[x].push_back(static_cast<int>(y));
                    adj[y].push_back(static_cast<int>(x));
                }
            }
        }
        Coloring search(adj, k, budget);
        if (search.run()) {
            std::vector<Box> result;
            for (int h = 0; h < boxCount; ++h)
                if (!(deleted >> h & 1)) result.push_back(donor[h]);
            std::vector<Box> added(k, {0, 0});
            for (size_t x = 0; x < cells.size(); ++x) {
                added[search.colors[x]].rows |= Mask{1} << cells[x].row;
                added[search.colors[x]].cols |= Mask{1} << cells[x].col;
            }
            result.insert(result.end(), added.begin(), added.end());
            std::cout << "[";
            for (size_t h = 0; h < result.size(); ++h) {
                if (h) std::cout << ",";
                std::cout << "[" << result[h].rows << "," << result[h].cols << "]";
            }
            std::cout << "]\n";
            std::cerr << "found witness at deletion mask " << deleted << "\n";
            return 0;
        }
        ++tested;
        unknown += search.cutoff;
        total += search.nodes;
        largest = std::max(largest, search.nodes);
    }
    std::cerr << "tested " << tested << ", unresolved " << unknown << ", nodes "
              << total << ", largest " << largest << "\n";
    return unknown ? 3 : 0;
}
