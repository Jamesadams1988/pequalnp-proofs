// C++20. Maxima for two mutually compatible families of false-positive pairs.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
#include <utility>
#include <vector>

using Pair = std::pair<int,int>;
using Word = std::uint64_t;

bool incident(int a, int b) {
    if ((a < 13) == (b < 13)) return false;
    const int residue = (a + b) % 13;
    return residue == 0 || residue == 1 || residue == 3 || residue == 9;
}

bool compatible(Pair a, Pair b) {
    return incident(a.first,b.first) || incident(a.first,b.second) ||
           incident(a.second,b.first) || incident(a.second,b.second);
}

bool mixed(Pair x) { return x.first < 13 && x.second >= 13; }

struct Bits {
    std::array<Word,3> data{};
    bool operator==(const Bits&) const = default;
    void insert(int i) { data[i/64] |= Word(1) << (i%64); }
    int count() const {
        return std::popcount(data[0]) + std::popcount(data[1]) + std::popcount(data[2]);
    }
    Bits operator&(const Bits& other) const {
        return {{data[0]&other.data[0], data[1]&other.data[1], data[2]&other.data[2]}};
    }
};

struct Hash {
    std::size_t operator()(const Bits& x) const {
        auto v=x.data[0]*0x9e3779b97f4a7c15ULL ^ std::rotl(x.data[1],21) ^ std::rotl(x.data[2],47);
        return v ^ (v>>29);
    }
};

enum class Universe { all, mixed, point_pairs_vs_line_pairs };

struct Context {
    Bits columns;
    std::vector<Bits> neighborhoods;

    Context(Pair anchor, Universe universe) {
        std::vector<Pair> rows, eligible_columns;
        for (int a=0; a<26; ++a) for (int b=a+1; b<26; ++b) {
            Pair pair{a,b};
            if (incident(a,b)) continue;
            if (universe==Universe::mixed && !mixed(pair)) continue;
            if (universe!=Universe::point_pairs_vs_line_pairs || b<13) rows.push_back(pair);
            if (universe==Universe::point_pairs_vs_line_pairs && a<13) continue;
            if (compatible(anchor,pair)) eligible_columns.push_back(pair);
        }
        if (eligible_columns.size()>192) throw std::runtime_error("column mask too small");
        for (unsigned i=0; i<eligible_columns.size(); ++i) columns.insert(i);
        for (Pair row : rows) {
            Bits neighborhood;
            for (unsigned i=0; i<eligible_columns.size(); ++i)
                if (compatible(row,eligible_columns[i])) neighborhood.insert(i);
            neighborhoods.push_back(neighborhood);
        }
    }
};

struct Bounds {
    int smaller=0, sum=0, product=0;
    void include(int a, int b) {
        smaller=std::max(smaller,std::min(a,b));
        sum=std::max(sum,a+b);
        product=std::max(product,a*b);
    }
    bool operator==(const Bounds&) const = default;
};

// A closed column set is an intersection of row neighborhoods. Adding each
// row to all preceding intersections generates all possibilities. Discarding
// an intersection below threshold is safe because intersections only shrink.
Bounds enumerate(const Context& context, int threshold) {
    std::vector<Bits> closed;
    std::unordered_set<Bits,Hash> seen;
    auto add=[&](Bits b) {
        if (b.count()>=threshold && seen.insert(b).second) closed.push_back(b);
    };
    add(context.columns);
    auto rows=context.neighborhoods;
    std::sort(rows.begin(),rows.end(),[](Bits a,Bits b){return a.count()<b.count();});
    for (Bits row : rows) {
        const auto before=closed.size();
        for (std::size_t i=0; i<before; ++i) add(closed[i]&row);
    }
    Bounds result;
    for (Bits b : closed) {
        int extent=std::count_if(rows.begin(),rows.end(),[&](Bits r){return (r&b)==b;});
        result.include(extent,b.count());
    }
    return result;
}

// Decide whether k rows have k common columns. Every row covering all current
// columns can be taken for free. All other viable rows are tried in a fixed
// order, retaining only the rows after the chosen one at each recursive step.
bool has_square(Bits columns, const std::vector<Bits>& rows, int selected, int k) {
    std::vector<Bits> choices;
    for (Bits row : rows) {
        Bits next=columns&row;
        if (next==columns) ++selected;
        else if (next.count()>=k) choices.push_back(next);
    }
    if (selected>=k) return true;
    std::sort(choices.begin(),choices.end(),[](Bits a,Bits b){return a.count()<b.count();});
    while (selected+int(choices.size())>=k) {
        Bits next=choices.back();
        choices.pop_back();
        if (has_square(next,choices,selected+1,k)) return true;
    }
    return false;
}

void require(bool test) {
    if (!test) throw std::runtime_error("computed extrema differ from the stated result");
}

int main() {
    // Under cyclic translation, multiplication by 3 and point-line exchange,
    // these are all nonedge orbits. The README gives the explicit actions.
    for (int endpoint : {15,17,20}) {
        Pair anchor{0,endpoint};
        auto mixed_only=enumerate(Context(anchor,Universe::mixed),1);
        require(mixed_only==Bounds{12,61,324});
        auto unrestricted=enumerate(Context(anchor,Universe::all),31);
        require(unrestricted==Bounds{30,145,1638});
        std::cout<<"mixed anchor 0,"<<endpoint
                 <<"  mixed-only (smaller,sum,product) = (12,61,324)"
                 <<"  all pairs, columns >= 31 = (30,145,1638)\n";
    }
    for (int endpoint : {1,2}) {
        Pair anchor{0,endpoint};
        auto unrestricted=enumerate(Context(anchor,Universe::all),41);
        require(unrestricted==Bounds{30,127,1638});
        Context pure(anchor,Universe::point_pairs_vs_line_pairs);
        require(!has_square(pure.columns,pure.neighborhoods,0,31));
        std::cout<<"point-pair anchor 0,"<<endpoint
                 <<"  all pairs, columns >= 41 = (30,127,1638)"
                 <<"  point-pairs vs line-pairs has no 31 by 31 rectangle\n";
    }
}
