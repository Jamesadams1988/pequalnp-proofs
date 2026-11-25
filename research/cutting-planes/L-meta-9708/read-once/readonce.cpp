// Exhaust the read-once addition/division trees on the 15 edges of K6,
// with or without one premise (x0 + ... + x5 >= 2). All stored inequalities
// use <=. Each edge source and the optional total can be used only once.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <unordered_set>
#include <utility>
#include <vector>

using Packed = std::uint64_t;
using Catalog = std::vector<std::vector<Packed>>;
constexpr int vertices = 6, edgeCount = 15, masks = 1 << edgeCount;

// Seven byte lanes hold the six nonnegative coefficient encodings and RHS.
// Pure lines have no bias. In lines containing the total, add 1 to each
// coefficient and 2 to the RHS. Thus adding a pure line to either kind
// is ordinary word addition. All reachable lanes are less than 256.
Packed lane(int value, int position) {
    assert(value >= 0 && value < 256);
    return Packed(value) << (8 * position);
}
int component(Packed line, int position) {
    return (line >> (8 * position)) & 255;
}
int bias(bool mixed, int position) {
    return mixed ? (position == vertices ? 2 : 1) : 0;
}
int floorDivide(int n, int d) {
    return n < 0 ? -((-n + d - 1) / d) : n / d;
}

void insertDivisions(std::unordered_set<Packed>& lines, bool mixed) {
    // The inputs here end in an addition or are source lines. Consecutive
    // divisions collapse into one because floor(floor(x/a)/b)=floor(x/(ab)).
    std::vector<Packed> original(lines.begin(), lines.end());
    for (Packed line : original) {
        std::array<int,vertices+1> values;
        int divisorGcd = 0;
        for (int i=0; i<=vertices; ++i) {
            values[i] = component(line,i) - bias(mixed,i);
            if (i < vertices) divisorGcd = std::gcd(divisorGcd,values[i]);
        }
        // With zero coefficients every positive divisor is legal. Once its
        // size exceeds |RHS| every larger divisor gives the same floor.
        int limit = divisorGcd ? divisorGcd : std::abs(values.back())+1;
        for (int d=2; d<=limit; ++d) {
            if (divisorGcd % d != 0) continue;
            Packed divided = 0;
            for (int i=0; i<=vertices; ++i)
                divided |= lane(floorDivide(values[i],d)+bias(mixed,i),i);
            lines.insert(divided);
        }
    }
}

Catalog enumerate(const Catalog* pureCatalog) {
    const bool mixed = pureCatalog != nullptr;
    Catalog states(masks);
    std::vector<Packed> edges;
    for (int i=0; i<vertices; ++i) for (int j=i+1; j<vertices; ++j)
        edges.push_back(lane(1,i) + lane(1,j) + lane(1,vertices));
    // With the specified bias the total -sum(x) <= -2 encodes to zero.
    if (mixed) states[0].push_back(0);
    std::uint64_t combinations = 0, distinctStates = 0;
    for (int mask=1; mask<masks; ++mask) {
        std::unordered_set<Packed> lines;
        if (!mixed && !(mask & (mask-1)))
            lines.insert(edges[__builtin_ctz(unsigned(mask))]);
        // Mixed sums have a unique child containing the total. Pure sums
        // are unordered, so the mask ordering avoids counting them twice.
        int first = mixed ? mask : (mask-1)&mask;
        for (int left=first; left; left=(left-1)&mask) {
            int right = mask ^ left;
            if (!mixed && left>right) continue;
            const auto& positive = mixed ? (*pureCatalog)[left] : states[left];
            for (Packed a : positive) for (Packed b : states[right]) {
                lines.insert(a+b);
                ++combinations;
            }
        }
        insertDivisions(lines,mixed);
        states[mask].assign(lines.begin(),lines.end());
        distinctStates += states[mask].size();
    }
    std::cout << (mixed ? "Mixed" : "Pure") << " nonempty-mask states "
              << distinctStates << ", pair additions " << combinations
              << ", full-mask lines " << states.back().size() << '\n';
    return states;
}
std::set<int> uniformRhs(const Catalog& states, bool mixed, int coefficient) {
    std::set<int> answer;
    for (Packed line : states.back()) {
        bool uniform = true;
        for (int i=0; i<vertices; ++i)
            if (component(line,i)-bias(mixed,i) != coefficient) uniform = false;
        if (uniform) answer.insert(component(line,vertices)-bias(mixed,vertices));
    }
    return answer;
}
void printBounds(const char* label, const std::set<int>& values) {
    std::cout << label;
    for (int x : values) std::cout << ' ' << x;
    std::cout << '\n';
}
int main() {
    const Catalog pure = enumerate(nullptr);
    const auto capacity = uniformRhs(pure,false,1);
    printBounds("Uniform-coefficient-one RHS values",capacity);
    const Catalog mixed = enumerate(&pure);
    const auto final = uniformRhs(mixed,true,0);
    printBounds("Uniform-coefficient-zero RHS values",final);
    return capacity == std::set<int>{2,3} && final == std::set<int>{0,1} ? 0 : 1;
}
