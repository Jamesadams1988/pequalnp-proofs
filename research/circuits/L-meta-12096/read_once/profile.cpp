// Profile exact raw donor recursion. Memoization preserves multiplicities in
// the raw tree counts: each edge contributes the full count of its subtree.
#include "read_once.hpp"
#include <unordered_set>
#include <iomanip>
#include <iostream>
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using Word = std::uint64_t;
using Mask = unsigned __int128;
constexpr Word target = 0xfe80fe00fe00e800ULL;
constexpr int bound = 11;
struct Wire { Word table; Mask hi, lo, sep; };
struct State { std::array<unsigned,12> ids{}; bool operator==(const State&) const = default; };
struct Hash {
    std::size_t operator()(const State& s) const {
        Word h=1469598103934665603ULL;
        for (auto id:s.ids) h=(h^id)*1099511628211ULL;
        return h;
    }
};
struct Edge { int i,j,op,keep; };
struct Totals { Word nodes, leaves; bool hit; };
struct Entry { State state; Totals count{}; };
struct Layer { Word new_evals{}, reads{}, moves{}; std::vector<Entry> cache; };
struct Profile {
    std::unordered_map<Word,unsigned> index;
    std::vector<Wire> wires{{}};
    std::array<Layer,bound+1> layer;
    int slots=16;
    bool sorted=true;
    ro::Stats read_once_counts;
    std::unordered_map<State,bool,Hash> zero_memo;
    std::unordered_set<State,Hash> loose;
    bool log_examples=true;
    std::array<Word,12> nSize{};
    std::array<Word,12> nPassed{};
    bool solve_zero(const State& bank,int n) {
        State key=bank;std::sort(key.ids.begin(),key.ids.begin()+n);
        if(auto it=zero_memo.find(key);it!=zero_memo.end())return it->second;
        std::vector<Word> ws;for(int j=0;j<n;j++)ws.push_back(wires[key.ids[j]].table);
        ro::Solver ro_solver(ws,read_once_counts);
        bool value=ro_solver.solve(target);
        if(ro_solver.top_passes_rectangle){
            ++nPassed[n];
            if(log_examples && !value && nPassed[n]==1){
                std::cout<<"nontrivial n="<<n<<" tables";
                for(Word w:ws)std::cout<<" 0x"<<std::hex<<w;
                std::cout<<std::dec<<std::endl;
            }
        }
        ++nSize[n];
        zero_memo.emplace(key,value);
        return value;
    }


    unsigned add(Word table, Mask hi, Mask lo) {
        auto [it,inserted]=index.try_emplace(table,wires.size());
        if(inserted) wires.push_back({table,hi,lo,hi^lo});
        return it->second;
    }
    template<typename T> static T op(int k,T a,T b) {
        switch(k) {case 0:return a&b; case 1:return a|b; case 2:return a&~b; default:return b&~a;}
    }
    template<typename Fn>
    void next(const State& s,int count,int e,Fn callback) {
        for(int i=0;i<count;i++) for(int j=i+1;j<count;j++) {
            Wire a=wires[s.ids[i]], b=wires[s.ids[j]];
            Mask base=0;std::array<unsigned,12> rest{};int r=0;
            for(int p=0;p<count;p++) if(p!=i&&p!=j) {
                rest[r++]=s.ids[p];base|=wires[s.ids[p]].sep;
            }
            for(int k=0;k<4;k++) {
                Word t=op(k,a.table,b.table);
                Mask hi=op(k,a.hi,b.hi),lo=op(k,a.lo,b.lo), c=base|(hi^lo);
                for(int keep=0;keep<4;keep++) {
                    int cost=std::popcount(unsigned(keep));
                    if(cost>e || (c|(keep&1?a.sep:0)|(keep&2?b.sep:0))!=~Mask(0))continue;
                    State out;int n=0;out.ids[n++]=add(t,hi,lo);
                    if(keep&1)out.ids[n++]=s.ids[i];
                    if(keep&2)out.ids[n++]=s.ids[j];
                    for(int p=0;p<r;p++)out.ids[n++]=rest[p];
                    callback(out,n,e-cost,Edge{i,j,k,keep});
                }
            }
        }
    }

    Totals run(State s,int n,int k,int e) {
        if(e+n!=k+1)throw std::runtime_error("invalid donor extra allowance");
        if(sorted) std::sort(s.ids.begin(),s.ids.begin()+n);
        Layer& L=layer[k];++L.reads;
        if(slots && L.cache.empty())L.cache.resize(1u<<std::min(slots,k+12));
        Entry scratch{};
        Entry& E=slots ? L.cache[Hash{}(s)&(L.cache.size()-1)] : scratch;
        if(slots && E.state==s)return E.count;
        ++L.new_evals;
        bool hit=n==1&&(wires[s.ids[0]].table==target||wires[s.ids[0]].table==~target);
        Totals total{1,1,hit};
        if(!e){ total.hit=solve_zero(s,n); E={s,total}; return total; }
        if(k&&!hit)next(s,n,e,[&](const State& c,int m,int ee,Edge){
            if(total.hit)return;
            auto t=run(c,m,k-1,ee);
            if(total.nodes==1)total.leaves=0;
            total.nodes+=t.nodes;total.leaves+=t.leaves;
            total.hit=t.hit;++L.moves;
        });
        E={s,total};return total;
    }
    State seed(const char* file) {
        std::ifstream rows(file);std::array<int,256> r{};
        for(int j=0;j<256;j++) {
            if(!(rows>>r[j])||r[j]<0||r[j]>=64||int((target>>r[j])&1)!=(j>=128))throw std::runtime_error("invalid row projection");
        }
        State s{};
        for(int i=0;i<6;i++) {
            Word table=0;Mask hi=0,lo=0;
            for(int x=0;x<64;x++)if((x>>i)&1)table|=Word(1)<<x;
            for(int j=0;j<128;j++) {hi|=Mask((r[128+j]>>i)&1)<<j;lo|=Mask((r[j]>>i)&1)<<j;}
            s.ids[i]=add(table,hi,lo);
        }
        return s;
    }
};

int main(int argc,char**argv) {
    if(argc<3){std::fprintf(stderr,"profile rows.txt CHILD [CACHE_BITS=16] [SORT=1]\n");return 2;}
    int choice=std::atoi(argv[2]);Profile p;
    if(argc>3)p.slots=atoi(argv[3]);if(argc>4)p.sorted=atoi(argv[4]);
    if(p.slots<0 || p.slots>20)throw std::runtime_error("cache bits must be 0..20");
    auto root=p.seed(argv[1]);int ri=0,children=0;
    auto start=std::chrono::steady_clock::now();
    p.next(root,6,6,[&](const State& parent,int n,int e,Edge first){
        if(ri++!=13)return;
        if(first.i!=0||first.j!=4||first.op!=1||first.keep!=3)throw std::runtime_error("wrong parent");
        p.next(parent,n,e,[&](const State& c,int m,int e2,Edge cut){
            int at=children++;if(choice!=-1&&at!=choice)return;
            auto t=p.run(c,m,9,e2);
            double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
            std::printf("root=13 child=%d move=%d,%d,%d,%d n=%d extra=%d nodes=%llu leaves=%llu hit=%d seconds=%.3f\n",
               at,cut.i,cut.j,cut.op,cut.keep,m,e2,(unsigned long long)t.nodes,(unsigned long long)t.leaves,t.hit,elapsed);
            std::fflush(stdout);
        });
    });
    std::printf("zero_distinct=%zu partial_calls=%llu splits=%llu orientations=%llu rectangle_survivors=%llu smaller_side_trials=%llu collisions=%llu leaf_calls=%llu\n",p.zero_memo.size(),(unsigned long long)p.read_once_counts.fits,(unsigned long long)p.read_once_counts.split_tests,(unsigned long long)p.read_once_counts.orientations,(unsigned long long)p.read_once_counts.rectangles,(unsigned long long)p.read_once_counts.smaller_candidates,(unsigned long long)p.read_once_counts.collisions,(unsigned long long)p.read_once_counts.terminal_checks);
    for(int d=0;d<12;d++)if(p.read_once_counts.by_depth[d])std::printf("partial_depth=%d calls=%llu duplicate_projection_conflicts=%llu possible_rectangles=%llu left_candidates=%llu\n",d,(unsigned long long)p.read_once_counts.by_depth[d],(unsigned long long)p.read_once_counts.collision_depth[d],(unsigned long long)p.read_once_counts.feasible_split_depth[d],(unsigned long long)p.read_once_counts.candidate_depth[d]);
    for(int i=1;i<12;i++)if(p.nSize[i])std::printf("n=%d distinct=%llu pass_one_layer_rectangle=%llu\n",i,(unsigned long long)p.nSize[i],(unsigned long long)p.nPassed[i]);
    std::printf("rootChildren=%d branch13Children=%d signalCount=%zu\n",ri,children,p.wires.size()-1);
    for(int k=9;k>=0;k--){auto& L=p.layer[k];std::printf("k=%d cacheMiss=%llu calls=%llu admittedChildren=%llu\n",k,
      (unsigned long long)L.new_evals,(unsigned long long)L.reads,(unsigned long long)L.moves);}
}
