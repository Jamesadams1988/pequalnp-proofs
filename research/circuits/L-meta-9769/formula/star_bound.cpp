#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>

int main() {
    constexpr int n = 21;
    std::array<unsigned,n> neighborhoods{};
    for (int p = 0; p < n; ++p)
        for (int d : {0,5,7,17,20}) {
            int l = (p+d)%n;
            if (p != 0 || l != 0) neighborhoods[l] |= 1u << p;
        }
    std::array<int,n+1> upper{};
    int largest=0;
    for (unsigned points=0; points<(1u<<n); ++points) {
        unsigned lightRows=0;
        int light=0;
        for(unsigned mask:neighborhoods) {
            unsigned inside=points&mask;
            if (std::popcount(inside) <= 1) { ++light; lightRows |= inside; }
        }
        std::array<int,6> histogram{};
        unsigned possibleRows=0;
        for(unsigned mask:neighborhoods) {
            unsigned inside=points&mask;
            if (!(inside&lightRows) && std::popcount(inside)>=2) {
                ++histogram[std::popcount(inside)]; possibleRows|=inside;
            }
        }
        // Pairwise disjoint sets cannot consume more distinct rows than their union.
        int budget=std::popcount(possibleRows);
        int extra=0;
        for(int size=2;size<=5;++size) {
            int take=std::min(histogram[size],budget/size);
            budget-=size*take;
            extra+=take;
        }
        int k=std::popcount(points);
        upper[k]=std::max(upper[k],light+extra);
        largest=std::max(largest,k+light+extra);
    }
    for(int s=0;s<=n;++s) std::cout<<s<<" "<<upper[s]<<"\n";
    std::cout<<"upper "<<largest<<"\n";
}
