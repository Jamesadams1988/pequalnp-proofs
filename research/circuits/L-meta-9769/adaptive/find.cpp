#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <tuple>
#include <vector>
using Mask = std::uint32_t;
constexpr int n=21;
constexpr Mask full=(1u<<n)-1;
std::array<std::array<Mask,n>,2> adj{};
struct State {
    Mask side[2];
    int size() const {return std::popcount(side[0])+std::popcount(side[1]);}
    void prune() {
        for(int s=0;s<2;++s) {
            Mask keep=0;
            for(Mask a=side[s];a;a&=a-1) {
                int i=std::countr_zero(a);
                if(adj[s][i]&side[1-s])keep|=1u<<i;
            }
            side[s]=keep;
        }
    }
};
struct Choice {int vertex, units, immediate, freedom; State zero,one;};
using Key=std::tuple<Mask,Mask,int>;
std::map<Key,int> split;
std::set<Key> failed;
long long visits=0,limit=0;
int difficulty(const State& st) {
    int value=0;
    for(int s=0;s<2;++s)
        for(Mask a=st.side[s];a;a&=a-1) {
            int i=std::countr_zero(a);
            value+=std::min(3,std::popcount(adj[s][i]&st.side[1-s]));
        }
    return value;
}
bool prove(State st,int goal) {
    // In a residual function with u separate units the certified bound is
    // goal + u. The leaf needs at least one remaining essential variable.
    if(!st.size()) return false;
    if(st.size()-1>=goal)return true;
    Key key{st.side[0],st.side[1],goal};
    if(split.contains(key))return true;
    if(failed.contains(key)) return false;
    if(++visits>limit)throw std::runtime_error("search limit");
    std::vector<Choice> choices;
    int edgeCount=0;
    for(int s=0;s<2;++s)for(Mask a=st.side[s];a;a&=a-1) {
        int i=std::countr_zero(a);
        Mask neighbors=adj[s][i]&st.side[1-s];
        int d=std::popcount(neighbors);
        State z=st;z.side[s]^=1u<<i;
        State o=z;o.side[1-s]&=~neighbors;
        z.prune();o.prune();
        if(s==0)edgeCount+=d;
        if(!z.size() || !o.size())continue;
        int worst=std::min(z.size(),o.size()+d);
        choices.push_back({s*n+i,d,worst,difficulty(o)+difficulty(z),z,o});
    }
    if(edgeCount+std::min(std::popcount(st.side[0]),std::popcount(st.side[1]))-1<goal) return false;
    std::sort(choices.begin(),choices.end(),[](const Choice&a,const Choice&b) {
        return std::tie(a.immediate,a.freedom,a.vertex)>std::tie(b.immediate,b.freedom,b.vertex);
    });
    for(auto& c:choices) if(prove(c.one,goal-2-c.units) && prove(c.zero,goal-2)){
        split[key]=c.vertex;
        return true;
    }
    failed.insert(key);return false;
}
void collect(State st,int goal,std::set<Key>& used) {
    if(st.size()-1>=goal)return;
    Key k{st.side[0],st.side[1],goal};
    if(!used.insert(k).second)return;
    int v=split.at(k),s=v/n,i=v%n;
    Mask neighbors=adj[s][i]&st.side[1-s];
    State z=st;z.side[s]^=1u<<i;
    State o=z;o.side[1-s]&=~neighbors;
    z.prune();o.prune();
    collect(z,goal-2,used);collect(o,goal-2-std::popcount(neighbors),used);
}
int main(int argc,char**argv){
    if(argc!=5)return 1;
    std::ifstream input(argv[1]);int i,j;
    while(input>>i>>j){adj[0].at(i)|=1u<<j;adj[1].at(j)|=1u<<i;}
    int goal=std::stoi(argv[2]);limit=std::stoll(argv[3]);State initial{{full,full}};
    try{
        if(!prove(initial,goal)){std::cout<<"no certificate via this search\n";return 2;}
    }catch(const std::runtime_error&){std::cout<<"unresolved within "<<limit<<" search nodes\n";return 3;}
    std::set<Key> used;collect(initial,goal,used);
    std::ofstream out(argv[4]);
    for(auto& k:used){auto [l,r,g]=k;out<<l<<' '<<r<<' '<<g<<' '<<split.at(k)<<'\n';}
    std::cout<<goal<<" gates, "<<used.size()<<" certificate nodes, "<<visits<<" searched\n";
}
