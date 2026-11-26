// Independent lower-bound replay. Graph states are sets of surviving edges.
// Compile with c++ -O3 -std=c++20 and run with depth and, optionally, the literal assignment JSON.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <iterator>
#include <regex>
#include <string>
#include <map>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using E = std::uint64_t;
using V = std::uint32_t;
constexpr int n=26;
std::array<E,n> incident{};
std::vector<std::pair<int,int>> endpoints;
std::unordered_map<E,int> covers;
std::array<std::unordered_map<E,int>,7> computed;
int horizon=3;
std::array<std::map<int,int>,2> root_cases;
E full;
V neighbors(E graph, int v) {
    V result=0;
    for (E e=graph & incident[v];e;e &= e-1) {
        auto [a,b] = endpoints[std::countr_zero(e)];
        result |= V(1) << (a ^ b ^ v);
    }
    return result;
}
// A cover either contains v or contains all neighbors of v.
int cover(E graph) {
    if (!graph) return 0;
    if (covers.contains(graph)) return covers.at(graph);
    int choice=0;
    for (int v=1;v<n;++v)
        if (std::popcount(incident[v]&graph)>std::popcount(incident[choice]&graph)) choice=v;
    E withoutNeighbors=graph;
    V ns=neighbors(graph,choice);
    for (V w=ns;w;w&=w-1) withoutNeighbors &= ~incident[std::countr_zero(w)];
    int ans=std::min(1+cover(graph & ~incident[choice]), std::popcount(ns)+cover(withoutNeighbors));
    covers[graph]=ans;
    return ans;
}
int lower(E graph,int rounds) {
    if (!graph) return 0;
    auto& cache=computed.at(rounds);
    if (cache.contains(graph)) return cache.at(graph);
    V live=0;
    E interior=graph;
    std::array<V,n> ns{};
    for (int v=0;v<n;++v) {
        ns[v]=neighbors(graph,v);
        if (ns[v]) live|=V(1)<<v;
        if (std::popcount(ns[v])<2) interior &= ~incident[v];
    }
    int best=std::popcount(live)-1+cover(interior);
    if (rounds && std::popcount(graph)>=2) {
        std::array<std::array<int,2>,n> cofactor{};
        for (int v=0;v<n;++v) if (ns[v]) {
            E zero=graph&~incident[v], one=zero;
            for (V w=ns[v];w;w&=w-1) one &= ~incident[std::countr_zero(w)];
            int d=std::popcount(ns[v]);
            cofactor[v]={lower(zero,rounds-1), one ? lower(one,rounds-1)+d : d-1};
        }
        int allFirst=1000;
        for (int op=0;op<2;++op) for (int a=0;a<n;++a) for (int b=0;b<a;++b) {
            if (!ns[a]||!ns[b]) continue;
            bool adjacent=(ns[a]>>b)&1;
            if (!op && !adjacent) continue;
            if (op && adjacent && (std::has_single_bit(ns[a]) || std::has_single_bit(ns[b]))) continue;
            int oneFirst=0;
            for (auto [v,w]:{std::pair(a,b),std::pair(b,a)}) {
                bool two=op ? adjacent || (ns[v]&~ns[w]) : bool(ns[v] & ~(V(1)<<w));
                int A=cofactor[v][op], N=cofactor[v][1-op];
                int branch=std::max(A+2,N+1);
                if (two) {
                    branch=std::max(A+3,N+2);
                    if (graph & ~incident[v])
                        branch=std::min(std::max(A+3,N+3),std::max(A+4,N+2));
                }
                oneFirst=std::max(oneFirst,branch);
            }
            allFirst=std::min(allFirst,oneFirst);
            if (graph==full && rounds==horizon) ++root_cases[op][oneFirst];
        }
        // This replay does not use separate maximization over arbitrary one-gate restrictions.
        best=std::max(best,allFirst);
    }
    cache[graph]=best;
    return best;
}
int main(int argc,char** argv) {
    if (argc>1) horizon=std::stoi(argv[1]);
    if (horizon<0 || horizon>6 || argc>3) throw std::runtime_error("usage: verifier [depth 0..6] [assignment.json]");
    for (int p=0;p<13;++p) for (int w=0;w<13;++w) {
        int d=(p+13-w)%13;
        if ((p==0 && w==0) || (d!=0 && d!=1 && d!=3 && d!=9)) continue;
        E edge=E(1)<<endpoints.size();
        endpoints.push_back({p,13+w});
        incident[p] |=edge;
        incident[13+w] |=edge;
    }
    if (endpoints.size()!=51) throw std::logic_error("wrong edge count");
    if (argc==3) {
        std::ifstream in(argv[2]);
        if (!in) throw std::runtime_error("cannot open assignment");
        const std::string source{std::istreambuf_iterator<char>(in),std::istreambuf_iterator<char>()};
        const std::regex tuple(R"(\(([0-9]+),\s*([0-9]+)\))");
        std::vector<std::pair<int,int>> literal;
        for (auto it=std::sregex_iterator(source.begin(),source.end(),tuple);it!=std::sregex_iterator();++it)
            literal.emplace_back(std::stoi((*it)[1]),std::stoi((*it)[2]));
        if (literal!=endpoints) throw std::logic_error("ordered assignment mismatch");
        std::cout<<"ordered desk graph matched all 51 edges"<<std::endl;
    }
    full=(E(1)<<endpoints.size())-1;
    for (int a=0;a<n;++a) for (int b=0;b<a;++b)
        if (std::popcount(neighbors(full,a)&neighbors(full,b))>1) throw std::logic_error("four-cycle");
    for (int d=0;d<=horizon;++d) std::cout<<"round "<<d<<" bound "<<lower(full,d)<<std::endl;
    for (int op=0;op<2;++op) for (auto [s,count]:root_cases[op])
        std::cout<<(op?"OR":"AND")<<" bound "<<s<<" choices "<<count<<"\n";
}
