// Exact primal and dual certificates for weighted covers of the maximal negatives.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
using Profile = std::array<int,5>;
using Wide = std::int64_t;
constexpr Mask half = (Mask(1)<<13)-1;
constexpr Mask full = (Mask(1)<<26)-1;
constexpr Profile sizes{13,10,8,7,6};
constexpr Profile dual{5,0,1,1,1};
constexpr std::array<Profile,4> selected{{
    {2,0,0,0,0}, {0,0,4,6,0}, {0,0,0,10,0}, {0,4,6,0,4}
}};
constexpr std::array<Wide,4> mass_tenths{10,195,351,130};

void require(bool value, const char* message) {
    if (!value) throw std::runtime_error(message);
}

std::array<Mask,1<<13> neighborhood_table() {
    std::array<Mask,1<<13> neighborhoods{};
    for (Mask s=1; s<=half; ++s) {
        int p=std::countr_zero(s);
        Mask line_mask=0;
        for (int l=0; l<13; ++l) {
            int r=(p+l)%13;
            if (r==0 || r==1 || r==3 || r==9) line_mask |= Mask(1)<<l;
        }
        neighborhoods[s]=neighborhoods[s&(s-1)] | line_mask;
    }
    return neighborhoods;
}

template<class Visit> void each_subset(Mask mask, Visit visit) {
    for (Mask subset=mask;;subset=(subset-1)&mask) {
        visit(subset);
        if (!subset) return;
    }
}

struct Incidence {
    Mask support;
    int cut;
};

int main() {
    const auto neighbors=neighborhood_table();
    std::vector<Mask> cuts;
    std::vector<int> kinds;
    std::vector<Incidence> incidences;
    incidences.reserve(4400000);
    for (Mask points=0; points<=half; ++points) {
        Mask lines=half ^ neighbors[points];
        if ((half ^ neighbors[lines])!=points) continue;
        Mask cut=points | (lines<<13);
        int id=cuts.size();
        cuts.push_back(cut);
        auto it=std::find(sizes.begin(),sizes.end(),std::popcount(cut));
        require(it!=sizes.end(),"unknown size class");
        kinds.push_back(it-sizes.begin());
        // The residual vertices outside this cut and the singleton support
        // must form an independent set. Enumerate each such residual once.
        each_subset(half ^ points,[&](Mask residual_points) {
            Mask allowed=(half ^ lines) & ~neighbors[residual_points];
            each_subset(allowed,[&](Mask residual_lines) {
                Mask support=full ^ (cut | residual_points | (residual_lines<<13));
                incidences.push_back({support,id});
            });
        });
    }
    std::sort(incidences.begin(),incidences.end(),[](auto a,auto b){return a.support<b.support;});
    std::array<Wide,4> class_sizes{};
    std::vector<std::array<Wide,4>> memberships(cuts.size());
    int max_dual=0;
    for (std::size_t first=0;first<incidences.size();) {
        std::size_t end=first;
        Profile profile{};
        while (end<incidences.size() && incidences[end].support==incidences[first].support) {
            ++profile[kinds[incidences[end].cut]];
            ++end;
        }
        max_dual=std::max(max_dual,std::inner_product(profile.begin(),profile.end(),dual.begin(),0));
        auto it=std::find(selected.begin(),selected.end(),profile);
        if (it!=selected.end()) {
            unsigned c=it-selected.begin();
            ++class_sizes[c];
            for (std::size_t i=first;i<end;++i) ++memberships[incidences[i].cut][c];
        }
        first=end;
    }
    int dual_total=0;
    for (auto k:kinds) dual_total+=dual[k];
    require(cuts.size()==704 && incidences.size()==4363558,"enumeration totals");
    require(dual_total==686 && max_dual==10,"dual certificate");
    Wide denominator=10;
    for (auto n:class_sizes) {
        require(n>0,"empty support class");
        denominator=std::lcm(denominator,10*n);
    }
    std::array<Wide,4> numerators{};
    for (unsigned c=0;c<4;++c)
        numerators[c]=mass_tenths[c]*(denominator/(10*class_sizes[c]));
    Wide total=std::inner_product(class_sizes.begin(),class_sizes.end(),numerators.begin(),Wide(0));
    require(10*total==686*denominator,"fractional cover mass");
    std::cout<<"selected profile class sizes";
    for (auto x:class_sizes) std::cout<<' '<<x;
    std::cout<<"\ncut size | number of cuts | memberships per cut in columns 1-4 | coverage\n";
    for (unsigned k=0;k<sizes.size();++k) {
        int count=0;
        std::array<Wide,4> row{};
        Wide coverage=0;
        for (unsigned i=0;i<cuts.size();++i) if (kinds[i]==int(k)) {
            if (!count) row=memberships[i];
            require(row==memberships[i],"membership differs within a cut size");
            coverage=std::inner_product(memberships[i].begin(),memberships[i].end(),numerators.begin(),Wide(0));
            require(coverage>=denominator,"uncovered test");
            ++count;
        }
        std::cout<<sizes[k]<<" | "<<count<<" |";
        for(auto x:row) std::cout<<' '<<x;
        Wide g=std::gcd(coverage,denominator);
        std::cout<<" | "<<coverage/g<<'/'<<denominator/g<<'\n';
    }
    std::cout<<"fractional optimum "<<total/std::gcd(total,denominator)<<'/'<<denominator/std::gcd(total,denominator)
             <<" from "<<cuts.size()<<" cuts and "<<incidences.size()<<" cut-support incidences\n";
}
