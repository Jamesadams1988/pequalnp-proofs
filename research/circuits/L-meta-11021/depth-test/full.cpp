// Depth four with arbitrary signed input literals, constants, AND and OR.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Truth = std::array<Word,8>;
using Mask = unsigned;
constexpr Mask edgeFull=(1u<<12)-1;
constexpr Mask cutFull=(1u<<13)-1;

bool predicate(unsigned input) {
    constexpr std::pair<int,int> edges[] = {{0,4},{0,5},{1,5},{2,6},{3,6},{0,7},
        {2,7},{4,7},{1,8},{3,8},{4,8},{6,8}};
    for (auto [a,b] : edges)
        if ((input & (1u<<a)) && (input & (1u<<b))) return true;
    return false;
}
bool bit(const Truth& t, unsigned i) { return t[i/64] >> (i%64) & 1u; }

struct Profile {
    Word falseOnNeg;          // true bits are negative rows rejected
    Truth missedPos;          // indexed by the original 9-bit input
    Mask edges;               // minimal positives accepted
    Mask cuts;                // maximal negatives rejected
};

std::vector<Profile> depthTwo(bool signedInputs, Word& allNeg) {
    std::vector<unsigned> negatives, minima, maxima;
    Truth goal{};
    for (unsigned x=0; x<512; ++x) {
        if (predicate(x)) {
            goal[x/64] |= Word(1)<<(x%64);
            if (std::popcount(x)==2) minima.push_back(x);
        } else {
            negatives.push_back(x);
            bool maximal=true;
            for (unsigned b=1; b<512; b<<=1)
                if (!(x&b) && !predicate(x|b)) maximal=false;
            if (maximal) maxima.push_back(x);
        }
    }
    if (negatives.size()!=57 || minima.size()!=12 || maxima.size()!=13)
        throw std::runtime_error("unexpected graph predicate");
    allNeg=(Word(1)<<negatives.size())-1;
    Truth zero{}, one;
    one.fill(~Word(0));
    std::set<Truth> pool{zero,one};
    for (unsigned v=0; v<9; ++v) {
        Truth t{};
        for (unsigned x=0; x<512; ++x)
            if (x & (1u<<v)) t[x/64] |= Word(1)<<(x%64);
        pool.insert(t);
        if (signedInputs) {
            for (auto& word:t) word=~word;
            pool.insert(t);
        }
    }
    for (unsigned d=1; d<=2; ++d) {
        const auto prev=pool;
        for (auto a=prev.begin(); a!=prev.end(); ++a)
            for (auto b=a; b!=prev.end(); ++b) {
                Truth both{}, either{};
                for (unsigned i=0; i<8; ++i) {
                    both[i]=(*a)[i]&(*b)[i];
                    either[i]=(*a)[i]|(*b)[i];
                }
                pool.insert(both);
                pool.insert(either);
            }
    }
    std::vector<Profile> rows;
    for (const auto& t:pool) {
        Profile p{};
        for (unsigned i=0; i<negatives.size(); ++i)
            if (!bit(t,negatives[i])) p.falseOnNeg |= Word(1)<<i;
        for (unsigned i=0; i<8; ++i) p.missedPos[i]=~t[i]&goal[i];
        for (unsigned i=0; i<minima.size(); ++i)
            if (bit(t,minima[i])) p.edges |= 1u<<i;
        for (unsigned i=0; i<maxima.size(); ++i)
            if (!bit(t,maxima[i])) p.cuts |= 1u<<i;
        rows.push_back(p);
    }
    return rows;
}

template<std::size_t N>
std::vector<Mask> report(const std::array<bool,N>& present, const char* label) {
    std::vector<Mask> maximal;
    for (Mask mask=N-1;;--mask) {
        if (present[mask] && std::none_of(maximal.begin(),maximal.end(),
            [&](Mask other){return (other & mask)==mask;})) maximal.push_back(mask);
        if (!mask) break;
    }
    int best=0;
    for (auto x:maximal) for (auto y:maximal) best=std::max(best,std::popcount(x|y));
    std::cout << label << ": " << maximal.size() << " maximal masks, best two cover " << best <<
        '/' << std::popcount(Mask(N-1)) << '\n';
    return maximal;
}

std::pair<std::vector<Mask>,std::vector<Mask>> run(bool signedInputs) {
    Word allNeg;
    auto rows=depthTwo(signedInputs,allNeg);
    std::array<bool,edgeFull+1> sound{};
    std::array<bool,cutFull+1> complete{};
    const Truth zero{};
    std::cout << (signedInputs?"signed":"positive") << " leaves, depth-two full tables " << rows.size() << std::endl;
    for (std::size_t i=0; i<rows.size(); ++i) {
        const auto& a=rows[i];
        for (std::size_t j=i; j<rows.size(); ++j) {
            const auto& b=rows[j];
            // A top OR can only have children rejecting all 57 false rows.
            if ((a.falseOnNeg | b.falseOnNeg)==allNeg) sound[a.edges & b.edges]=true;
            if (a.falseOnNeg==allNeg && b.falseOnNeg==allNeg) sound[a.edges | b.edges]=true;
            // A top AND can only have children accepting all 455 true rows.
            if (a.missedPos==zero && b.missedPos==zero) complete[a.cuts | b.cuts]=true;
            bool jointMiss=false;
            for (unsigned w=0; w<8; ++w)
                if (a.missedPos[w] & b.missedPos[w]) { jointMiss=true; break; }
            if (!jointMiss) complete[a.cuts & b.cuts]=true;
        }
    }
    auto edges = report(sound,"OR root, edges covered while rejecting all false rows");
    auto cuts = report(complete,"AND root, maximal negatives rejected while accepting all true rows");
    return {edges,cuts};
}
int main() {
    const auto monotone = run(false);
    const auto signedLeaves = run(true);
    if (monotone != signedLeaves) throw std::runtime_error("one-sided maximal masks differ");
    std::cout << "Both families have the same maximal masks in both one-sided tests.\n";
}
