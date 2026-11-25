// Exact boundary search for a smaller replacement of a connected star-formula region.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using U = uint64_t;
using Bits = vector<U>;
struct Gate { int a=-1,b=-1; bool isOr=false; };
struct Formula {
    vector<Gate> gates=vector<Gate>(40);
    vector<int> parent;
    int emit(bool orGate,int a,int b) {gates.push_back({a,b,orGate});return int(gates.size())-1;}
    int join(vector<int> xs,bool balanced) {
        while(xs.size()>1) {
            if(!balanced) {int a=xs.back();xs.pop_back();int b=xs.back();xs.pop_back();xs.push_back(emit(true,b,a));continue;}
            vector<int> ys;
            size_t j=0;for(;j+1<xs.size();j+=2)ys.push_back(emit(true,xs[j],xs[j+1]));
            if(j<xs.size())ys.push_back(xs[j]);
            xs=move(ys);
        }
        return xs.front();
    }
    Formula(const vector<pair<int,int>>& edges,bool invert,bool balanced,unsigned seed) {
        mt19937 rng(seed);
        vector<vector<int>> nbr(20);
        for(auto [a,b]:edges)if(invert)nbr[b-20].push_back(a);else nbr[a].push_back(b);
        vector<int> terms;
        for(int i=0;i<20;i++) {
            if(seed)shuffle(nbr[i].begin(),nbr[i].end(),rng);
            terms.push_back(emit(false,i+(invert?20:0),join(nbr[i],balanced)));
        }
        if(seed)shuffle(terms.begin(),terms.end(),rng);
        join(terms,balanced);
        parent.assign(gates.size(),-1);
        for(int i=40;i<(int)gates.size();i++)for(int j:{gates[i].a,gates[i].b})
            if(j>=40){if(parent[j]>=0)throw logic_error("not a formula");parent[j]=i;}
    }
};
struct Samples {
    vector<U> states; Bits p,n;
    explicit Samples(const vector<pair<int,int>>& edges) {
        for(auto [i,j]:edges)states.push_back((U(1)<<i)|(U(1)<<j));
        constexpr unsigned all=(1u<<20)-1;
        array<unsigned,20> nbr{};
        for(auto [i,j]:edges)nbr[i]|=1u<<(j-20);
        vector<unsigned> nb(all+1);
        for(unsigned a=0;a<=all;a++) {
            if(a)nb[a]=nb[a&(a-1)]|nbr[countr_zero(a)];
            unsigned b=all^nb[a], other=all^a;
            while(other&&(nbr[countr_zero(other)]&b))other&=other-1;
            if(!other)states.push_back(a|(U(b)<<20));
        }
        p.assign((states.size()+63)/64,0);n=p;
        for(size_t i=0;i<states.size();i++)(i<edges.size()?p:n)[i/64]|=U(1)<<(i%64);
    }
};
struct Replace {
    const Formula& f; const Samples& s; vector<Bits> value;
    long long cuts[5]={};
    Replace(const Formula& ff,const Samples& ss):f(ff),s(ss),value(f.gates.size(),Bits(s.p.size(),0)) {
        for(int i=0;i<40;i++)for(size_t k=0;k<s.states.size();k++)
            if((s.states[k]>>i)&1)value[i][k/64]|=U(1)<<(k%64);
        for(size_t i=40;i<f.gates.size();i++){
            auto g=f.gates[i];for(size_t k=0;k<s.p.size();k++)
                value[i][k]=g.isOr ? value[g.a][k]|value[g.b][k] : value[g.a][k]&value[g.b][k];
        }
        if(value.back()!=s.p)throw logic_error("baseline mismatch");
    }
    bool covers(const Bits& bits,int wire,bool wanted) {
        for(size_t i=0;i<bits.size();i++)if(bits[i]&(wanted?~value[wire][i]:value[wire][i]))return false;
        return true;
    }
    // Synthesize at most one gate. An AND operand must cover every positive;
    // an OR operand must exclude every negative. Then test all eligible pairs.
    string one(const vector<int>& src,const Bits& p,const Bits& n,bool allowGate) {
        for(int a:src)if(covers(p,a,true)&&covers(n,a,false))return to_string(a);
        if(!allowGate)return {};
        for(bool OR:{false,true}){
            vector<int> eligible;
            for(int a:src)if(OR?covers(n,a,false):covers(p,a,true))eligible.push_back(a);
            for(size_t i=0;i<eligible.size();i++)for(size_t j=0;j<i;j++){
                int a=eligible[i],b=eligible[j];bool ok=true;
                const Bits &care=OR?p:n;
                for(size_t k=0;k<care.size();k++)if(care[k] & (OR?~(value[a][k]|value[b][k]):(value[a][k]&value[b][k]))){ok=false;break;}
                if(ok)return "("+to_string(a)+(OR?" OR ":" AND ")+to_string(b)+")";
            }
        }
        return {};
    }
    // For a chained expression, fix the direct root operand and remove
    // assignments it already settles before synthesizing the other operand.
    string two(const vector<int>& src,const Bits& p,const Bits& n) {
        string tiny=one(src,p,n,true);
        if(!tiny.empty())return tiny;
        for(bool OR:{false,true})for(int a:src){
            if(OR?!covers(n,a,false):!covers(p,a,true))continue;
            Bits pp=p,nn=n;
            for(size_t j=0;j<p.size();j++)if(OR)pp[j]&=~value[a][j];else nn[j]&=value[a][j];
            auto rem=one(src,pp,nn,true);
            if(!rem.empty())return "("+to_string(a)+(OR?" OR ":" AND ")+rem+")";
        }
        return {};
    }
    // Three-gate formulas are either chained or have two single-gate arms.
    string three(const vector<int>& src,const Bits& p,const Bits& n){
        string tiny=two(src,p,n);
        if(!tiny.empty())return tiny;
        for(bool OR:{false,true}){
            for(int a:src){
                if(OR?!covers(n,a,false):!covers(p,a,true))continue;
                Bits pp=p,nn=n;
                for(size_t j=0;j<p.size();j++)if(OR)pp[j]&=~value[a][j];else nn[j]&=value[a][j];
                auto rem=two(src,pp,nn);
                if(!rem.empty())return "("+to_string(a)+(OR?" OR ":" AND ")+rem+")";
            }
            set<Bits> already;
            for(size_t i=0;i<src.size();i++)for(size_t j=0;j<i;j++)for(bool inner:{false,true}){
                int a=src[i],b=src[j];bool good=true;
                const Bits &hard=OR?n:p;
                for(size_t h=0;h<hard.size();h++){
                    U v=inner?(value[a][h]|value[b][h]):(value[a][h]&value[b][h]);
                    if(hard[h]&(OR?v:~v)){good=false;break;}
                }
                if(!good)continue;
                Bits pp=p,nn=n;
                for(size_t h=0;h<p.size();h++){
                    U v=inner?(value[a][h]|value[b][h]):(value[a][h]&value[b][h]);
                    if(OR)pp[h]&=~v;else nn[h]&=v;
                }
                if(!already.insert(OR?pp:nn).second)continue;
                auto rem=one(src,pp,nn,true);
                if(!rem.empty())return "(("+to_string(a)+(inner?" OR ":" AND ")+to_string(b)+")"+
                    (OR?" OR ":" AND ")+rem+")";
            }
        }
        return {};
    }
    // Gates strictly downstream from the window are forbidden as sources.
    // A row matters only if the sibling on every path step lets changes pass.
    string search(const vector<int>& cut) {
        cuts[cut.size()]++;
        vector<bool> excluded(f.gates.size());
        for(int v:cut)excluded[v]=true;
        Bits p=s.p,n=s.n;
        for(int child=cut.front(),up=f.parent[child];up!=-1;child=up,up=f.parent[child]){
            excluded[up]=true; auto g=f.gates[up];int sibling=(g.a==child?g.b:g.a);
            for(size_t i=0;i<p.size();i++){
                U m=g.isOr?~value[sibling][i]:value[sibling][i];p[i]&=m;n[i]&=m;
            }
        }
        if(none_of(p.begin(),p.end(),[](U word){return word!=0;}) ||
           none_of(n.begin(),n.end(),[](U word){return word!=0;}))
            throw logic_error("window has a constant care domain");
        vector<int> src;
        set<Bits> signature;
        for(size_t j=0;j<f.gates.size();j++)if(!excluded[j]){
            Bits key=s.p; for(size_t i=0;i<key.size();i++)key[i]=(p[i]|n[i])&value[j][i];
            if(signature.insert(move(key)).second)src.push_back(j);
        }
        if(cut.size()<=2)return one(src,p,n,cut.size()==2);
        if(cut.size()==3)return two(src,p,n);
        return three(src,p,n);
    }
    bool sweep() {
        for(int root=40;root<(int)f.gates.size();root++){
            vector<vector<int>> current={{root}};
            for(int k=1;k<=4;k++){
                set<vector<int>> next;
                for(auto cut:current){
                    auto answer=search(cut);
                    if(!answer.empty()){
                        cout<<"CANDIDATE cut";for(int x:cut)cout<<" "<<x;cout<<" replacement "<<answer<<"\n";return true;
                    }
                    for(int x:cut)for(int y:{f.gates[x].a,f.gates[x].b}){
                        if(y<40||find(cut.begin(),cut.end(),y)!=cut.end())continue;
                        auto bigger=cut;bigger.push_back(y);sort(bigger.begin()+1,bigger.end());next.insert(bigger);
                    }
                }
                current.assign(next.begin(),next.end());
            }
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=4 && argc!=5)return 2;
    ifstream file("edges.txt"); vector<pair<int,int>> edges;int a,b;
    while(file>>a>>b)edges.emplace_back(a,b);
    if(edges.size()!=95)return 3;
    if(argc==5){
        if(string(argv[4])!="positive")return 4;
        edges.clear();
        for(int p=0;p<20;p++)for(int j=0;j<2;j++)edges.emplace_back(p,20+(p/2)*2+j);
    }
    int orient=stoi(argv[1]),balanced=stoi(argv[2]);unsigned seed=stoul(argv[3]);
    Samples s(edges);Formula f(edges,orient,balanced,seed);
    Replace r(f,s);bool hit=r.sweep();
    if(argc==5){
        // Independently probe the balanced two-arm case, on all 16 four-bit rows.
        vector<int> ports={0,1,2,3};
        Bits p(s.p.size(),0),n=p;
        for(int j:ports)fill(r.value[j].begin(),r.value[j].end(),0);
        for(int x=0;x<16;x++){
            for(int j:ports)if(x&(1<<j))r.value[j][0]|=U(1)<<x;
            ((x&3)==3||(x&12)==12?p:n)[0]|=U(1)<<x;
        }
        if(!r.two(ports,p,n).empty()||r.three(ports,p,n).empty())
            throw logic_error("balanced positive control failed");
        cout<<"(a AND b) OR (c AND d): two gates excluded, three found\n";
    }
    cout<<"orientation="<<orient<<" balanced="<<balanced<<" seed="<<seed<<" nodes="<<f.gates.size()-40
        <<" mintrue="<<edges.size()<<" maxfalse="<<s.states.size()-edges.size()
        <<" windows="<<r.cuts[1]<<","<<r.cuts[2]<<","<<r.cuts[3]<<","<<r.cuts[4]<<" improvement="<<hit<<"\n";
    return 0;
}
