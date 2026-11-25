// Enumerate minimum AND/OR tree sizes up to nine gates on six inputs.
// Input is a line-separated list of hexadecimal 64-bit truth tables.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using Word = std::uint64_t;
struct Node { Word table; int left, right, gates, depth; char op; };
std::vector<Node> nodes;
std::unordered_map<Word, int> indexOf;
std::array<std::vector<int>, 10> layer;
std::unordered_set<Word> targets;

void record(Word table, int a, int b, int g, char op) {
    if (g == 9 && !targets.contains(table)) return;
    int depth = 1 + std::max(nodes[a].depth, nodes[b].depth);
    auto [hit, fresh] = indexOf.emplace(table, (int)nodes.size());
    if (fresh) {
        layer[g].push_back(hit->second);
        nodes.push_back({table, a, b, g, depth, op});
    } else {
        Node &old = nodes[hit->second];
        if (old.gates == g && depth < old.depth) old = {table, a, b, g, depth, op};
    }
}
std::string render(int i) {
    const Node &node = nodes[i];
    if (node.op == 'x') return "x" + std::to_string(i);
    return "(" + render(node.left) + " " + node.op + " " + render(node.right) + ")";
}
int main() {
    Word t;
    std::vector<Word> order;
    while (std::cin >> std::hex >> t) { targets.insert(t); order.push_back(t); }
    for (int i = 0; i < 6; ++i) {
        Word table = 0;
        for (int r = 0; r < 64; ++r) if (r >> i & 1) table |= Word{1} << r;
        nodes.push_back({table, -1, -1, 0, 0, 'x'});
        layer[0].push_back(i);
        indexOf.emplace(table, i);
    }
    for (int g = 1; g <= 9; ++g) {
        for (int a = 0; a <= (g - 1)/2; ++a) {
            int b = g - 1 - a;
            for (int i : layer[a]) for (int j : layer[b]) {
                if (a == b && i > j) continue;
                Word left = nodes[i].table, right = nodes[j].table;
                record(left & right, i, j, g, '&');
                record(left | right, i, j, g, '|');
            }
        }
        std::cerr << "gates=" << g << (g == 9 ? " final-targets=" : " distinct=" ) << layer[g].size() << '\n';
    }
    for (Word w : order) {
        auto it = indexOf.find(w);
        std::cout << std::hex << w << std::dec << '\t';
        if (it == indexOf.end()) { std::cout << ">9\n"; continue; }
        const Node &hit = nodes[it->second];
        std::cout << hit.gates << '\t' << hit.depth << '\t' << render(it->second) << '\n';
    }
}
