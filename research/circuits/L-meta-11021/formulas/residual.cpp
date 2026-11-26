#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <limits>
#include <vector>

using Mask = std::uint32_t;
constexpr std::array<std::pair<int,int>,12> edges{{
    {0,4},{0,5},{1,5},{2,6},{3,6},{0,7},{2,7},{4,7},{1,8},{3,8},{4,8},{6,8}
}};
constexpr unsigned positive = (1u << edges.size()) - 1;

bool target(int x) {
    for (auto [i,j]:edges) if ((x >> i) & (x >> j) & 1) return true;
    return false;
}

int main() {
    std::vector<int> tests;
    for (auto [i,j]:edges) tests.push_back(1<<i | 1<<j);
    for (int x=0; x<512; ++x) {
        if (target(x)) continue;
        bool maximal=true;
        for (int i=0; i<9; ++i)
            if (!(x >> i & 1) && !target(x | 1<<i)) maximal=false;
        if (maximal) tests.push_back(x);
    }
    if (tests.size()!=25) return 1;
    const Mask full=(1u<<tests.size())-1;
    constexpr int maxLeaves=17;
    std::vector<std::vector<Mask>> layers(maxLeaves+1);
    std::vector<unsigned char> dominated(full+1), seen(full+1);
    std::array<int,positive+1> residual;
    residual.fill(1000);
    residual[0]=0; // Constant false is represented by an empty residual expression.
    auto insert=[&](int leaves, Mask e) {
        layers[leaves].push_back(e);
        if ((e & ~positive)==0) {
            Mask covered=positive ^ e;
            for (Mask s=covered; s; s=(s-1)&covered)
                residual[s]=std::min(residual[s],leaves);
        }
        auto mark=[&](auto&& self, Mask m, Mask free)->void {
            if (dominated[m]) return;
            dominated[m]=true;
            while (free) {
                Mask bit=free & -free; free^=bit;
                self(self,m|bit,free);
            }
        };
        mark(mark,e,full^e);
    };
    for (int v=0; v<9; ++v) {
        Mask value=0;
        for (unsigned t=0; t<tests.size(); ++t) value|=(unsigned(tests[t]>>v)&1)<<t;
        if (!dominated[value^positive]) insert(1,value^positive);
    }
    for (int l=2; l<=maxLeaves; ++l) {
        std::vector<Mask> candidates;
        for (int a=1; a<=l/2; ++a) {
            for (Mask x:layers[a]) for (Mask y:layers[l-a]) {
                if (2*a==l && x>y) continue;
                Mask both=x&y, diff=x^y;
                for (Mask z:{both|(diff&positive),both|(diff&~positive)}) {
                    if (!seen[z] && !dominated[z]) {
                        seen[z]=true;
                        candidates.push_back(z);
                    }
                }
            }
        }
        std::sort(candidates.begin(),candidates.end(),[](Mask a, Mask b){
            return std::pair(std::popcount(a),a)<std::pair(std::popcount(b),b);
        });
        for (Mask e:candidates) if (!dominated[e]) insert(l,e);
    }
    if (residual[positive]!=17) return 2;
    for (Mask s=0;s<=positive;++s) {
        int suffix=1000;
        for (Mask use=s;;use=(use-1)&s) {
            suffix=std::min(suffix,std::popcount(use)+residual[positive^use]);
            if (use==0) break;
        }
        std::cout<<s<<" "<<residual[s]<<" "<<std::popcount(s)+suffix-1<<"\n";
    }
}
