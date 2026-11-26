#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Mask = std::uint32_t;

enum class Basis { monotone, paidNot, signedLeaves };

class DepthTest {
    std::vector<Mask> positives, negatives;
    std::vector<std::uint8_t> possible, reverse;
    Basis basis;
    Mask allPositive{}, allNegative{}, full{};

    static bool edgePredicate(Mask input) {
        constexpr std::pair<int,int> edges[] = {
            {0,4},{0,5},{1,5},{2,6},{3,6},{0,7},
            {2,7},{4,7},{1,8},{3,8},{4,8},{6,8}
        };
        for (auto [left,right] : edges)
            if ((input & (1u << left)) && (input & (1u << right))) return true;
        return false;
    }

    bool withinTwo(Mask a, Mask b, bool invert) const {
        return (invert ? reverse : possible)[a | (b << positives.size())];
    }

    template<class Check>
    static bool canSplit(Mask mask, Check check) {
        // It suffices to try one ordering of each two-part partition.
        if (!mask) return check(0, 0);
        const Mask movable = mask ^ (mask & -mask);
        Mask part = movable;
        while (true) {
            if (check(part, mask ^ part)) return true;
            if (!part) return false;
            part = (part - 1) & movable;
        }
    }

    bool withinThree(Mask a, Mask b, bool invert=false) const {
        if (withinTwo(a,b,invert)) return true;
        if (basis==Basis::paidNot && withinTwo(a,b,!invert)) return true;
        return canSplit(a, [&](Mask x, Mask y){return withinTwo(x,b,invert) && withinTwo(y,b,invert);})
            || canSplit(b, [&](Mask x, Mask y){return withinTwo(a,x,invert) && withinTwo(a,y,invert);});
    }

    bool withinFour(Mask a, Mask b) const {
        if (basis==Basis::paidNot && withinThree(a,b,true)) return true;
        return canSplit(a, [&](Mask x, Mask y){return withinThree(x,b) && withinThree(y,b);})
            || canSplit(b, [&](Mask x, Mask y){return withinThree(a,x) && withinThree(a,y);});
    }

public:
    explicit DepthTest(Basis selected) : basis(selected) {
        for (Mask input=0; input<512; ++input) {
            if (std::popcount(input)==2 && edgePredicate(input)) positives.push_back(input);
            if (edgePredicate(input)) continue;
            bool maximal = true;
            for (int v=0; v<9; ++v) {
                const Mask enlarged = input | (1u << v);
                if (enlarged!=input && !edgePredicate(enlarged)) maximal=false;
            }
            if (maximal) negatives.push_back(input);
        }
        if (positives.size()!=12 || negatives.size()!=13) throw std::runtime_error("unexpected boundary sizes");
        allPositive=(1u<<positives.size())-1;
        allNegative=(1u<<negatives.size())-1;
        full=(1u<<(positives.size()+negatives.size()))-1;
        std::vector<Mask> samples=positives;
        samples.insert(samples.end(),negatives.begin(),negatives.end());
        std::set<Mask> tables{0,full};
        for (int v=0; v<9; ++v) {
            Mask table=0;
            for (std::size_t r=0; r<samples.size(); ++r)
                if (samples[r] & (1u<<v)) table |= 1u<<r;
            tables.insert(table);
            if (basis==Basis::signedLeaves) tables.insert(full ^ table);
        }
        for (int layer=1; layer<=2; ++layer) {
            const auto previous=tables;
            if (basis==Basis::paidNot)
                for (Mask table : previous) tables.insert(full ^ table);
            for (auto a=previous.begin(); a!=previous.end(); ++a)
                for (auto b=a; b!=previous.end(); ++b) {
                    tables.insert(*a & *b);
                    tables.insert(*a | *b);
                }
        }
        possible.resize(full+1);
        if (basis==Basis::paidNot) reverse.resize(full+1);
        for (Mask table : tables) {
            const Mask correct=table ^ (allNegative<<positives.size());
            possible[correct]=1;
            if (basis==Basis::paidNot) reverse[full ^ correct]=1;
        }
        // Downward closure: relaxing any requirement preserves feasibility.
        auto close=[&](std::vector<std::uint8_t>& rows) {
        for (Mask bit=1; bit<=full; bit<<=1)
            for (Mask base=0; base<=full; base+=2*bit)
                for (Mask i=base; i<base+bit; ++i) rows[i] |= rows[i+bit];
        };
        close(possible);
        if (basis==Basis::paidNot) close(reverse);
        std::cout << (basis==Basis::signedLeaves?"free signed leaves":basis==Basis::paidNot?"paid NOT gates":"monotone gates") << ", depth-two restricted tables " << tables.size() << '\n';
    }

    void run() const {
        const bool pass=withinFour(allPositive,allNegative);
        std::cout << "depth four fits all 12 edges and 13 maximal negatives: " << (pass?"yes":"no") << '\n';
        if (pass) return;
        Mask a=allPositive, b=allNegative;
        // Inclusion-minimal for row deletion in this fixed order.
        for (std::size_t i=0; i<positives.size(); ++i)
            if (!withinFour(a ^ (1u<<i),b)) a ^= 1u<<i;
        for (std::size_t j=0; j<negatives.size(); ++j)
            if (!withinFour(a,b ^ (1u<<j))) b ^= 1u<<j;
        if (withinFour(a,b)) throw std::runtime_error("lost obstruction");
        for (std::size_t i=0; i<positives.size(); ++i) if (a & (1u<<i)) {
            if (!withinFour(a ^ (1u<<i),b)) throw std::runtime_error("redundant positive");
        }
        for (std::size_t i=0; i<negatives.size(); ++i) if (b & (1u<<i)) {
            if (!withinFour(a,b ^ (1u<<i))) throw std::runtime_error("redundant negative");
        }
        std::cout << "positive input masks:";
        for (std::size_t i=0; i<positives.size(); ++i) if (a & 1u<<i) std::cout << ' ' << positives[i];
        std::cout << "\nnegative input masks:";
        for (std::size_t i=0; i<negatives.size(); ++i) if (b & 1u<<i) std::cout << ' ' << negatives[i];
        std::cout << '\n';
    }
};

int main() {
    DepthTest(Basis::monotone).run();
    DepthTest(Basis::paidNot).run();
    DepthTest(Basis::signedLeaves).run();
}
