// Derive each specified Hall clause once, then make it available to a second proof tree.
#include "hall_table.hpp"
#include <fstream>
#include <map>
#include <string>

struct Entry {
    unsigned pos, neg;
    int type, a, b, c;
};

class Emitter {
    const HallModel& model;
    const Table& t;
    int hall=-1;
    unsigned hallMask=0;
    std::map<std::pair<unsigned,unsigned>,int> axioms;
    std::vector<Entry> proof;

    int append(Entry e) {
        if(e.type!=2) {
            auto [where,added]=axioms.emplace(std::make_pair(e.pos,e.neg),int(proof.size()));
            if(!added) return where->second;
        }
        proof.push_back(e);
        return int(proof.size())-1;
    }
    int cost(State s,bool prepared) const {
        if(!prepared) { std::sort(s.begin(),s.end()); return t.costs[t.rank(s)]; }
        // Sort within each of the two exchangeable groups of columns.
        for(int i=1;i<4;++i) {
            int first=i<model.k ? 0 : model.k;
            for(int j=i;j>first && s[j]<s[j-1];--j) std::swap(s[j],s[j-1]);
        }
        State second{};
        std::copy(s.begin()+model.k,s.end(),second.begin());
        return model.values[model.groupRank(s,model.k)*int(model.out.size())+
                            model.groupRank(second,4-model.k)];
    }
    int derive(State s,bool prepared) {
        int absent=31, outside=31;
        for(int h=0;h<4;++h) {
            absent &= t.columns[s[h]].excluded;
            if(h>=model.k) outside &= t.columns[s[h]].excluded;
        }
        if(absent) {
            int p=std::countr_zero(unsigned(absent));
            return append({15u<<(4*p),0,0,p,0,0});
        }
        if(prepared && (outside & model.affected)==model.affected) return hall;
        int best=cost(s,prepared);
        for(int p=0;p<5;++p) for(int h=0;h<4;++h) {
            const Column& col=t.columns[s[h]];
            if((col.occupied|col.excluded)&(1<<p)) continue;
            State no=s, yes=s;
            no[h]=col.no[p]; yes[h]=col.yes[p];
            int second=col.yes[p]<0 ? 1 : cost(yes,prepared);
            if(cost(no,prepared)+second!=best) continue;
            int pos=derive(no,prepared), neg;
            int v=4*p+h;
            unsigned bit=1u<<v;
            if(col.yes[p]<0) {
                int q=std::countr_zero(unsigned(col.occupied));
                neg=append({0,bit|(1u<<(4*q+h)),1,std::min(p,q),std::max(p,q),h});
            } else neg=derive(yes,prepared);
            const auto& left=proof[pos]; const auto& right=proof[neg];
            if(!(left.pos&bit) || !(right.neg&bit)) throw std::logic_error("redundant split");
            return append({(left.pos & ~bit)|right.pos,left.neg|(right.neg & ~bit),2,neg,pos,v});
        }
        throw std::logic_error("no optimal split");
    }
public:
    Emitter(const HallModel& m) : model(m),t(m.base) {}
    void run(const std::string& filename) {
        State initial{};
        int outsideID=-1;
        for(int i=0;i<int(t.columns.size());++i)
            if(t.columns[i].occupied==0 && t.columns[i].excluded==model.affected) outsideID=i;
        if(outsideID<0) throw std::logic_error("missing state");
        for(int h=model.k;h<4;++h) {
            initial[h]=outsideID;
            for(int p=0;p<=model.k;++p) hallMask|=1u<<(4*p+h);
        }
        hall=derive(initial,false);
        if(proof[hall].pos!=hallMask || proof[hall].neg!=0)
            throw std::logic_error("preparation did not return the exact Hall clause");
        int root=derive({0,0,0,0},true);
        if(proof[root].pos || proof[root].neg || axioms.size()!=45 ||
           int(proof.size())!=45+model.premiseLeaves()+model.values[0]-2)
            throw std::logic_error("published length check failed");
        std::ofstream file(filename); if(!file) throw std::runtime_error("cannot write proof");
        file<<"[\n";
        for(int i=0;i<int(proof.size());++i) {
            const auto& l=proof[i];
            if(l.type==0) file<<"  {\"rule\":\"pigeon\",\"p\":"<<l.a;
            if(l.type==1) file<<"  {\"rule\":\"hole\",\"p\":"<<l.a<<",\"q\":"<<l.b<<",\"h\":"<<l.c;
            if(l.type==2) file<<"  {\"rule\":\"res\",\"neg\":"<<l.a<<",\"pos\":"<<l.b<<",\"pivot\":"<<l.c;
            file<<(i+1==int(proof.size())?"}\n":"},\n");
        }
        file<<"]\n";
        std::cout<<"k="<<model.k<<": "<<proof.size()<<" lines, exact intermediate at zero-based line "<<hall<<'\n';
    }
};
int main(int argc,char** argv) {
    if(argc!=2) { std::cerr<<"usage: hall_witness OUTPUT_PREFIX\n"; return 2; }
    Table base; base.build();
    for(int k=1;k<4;++k) {
        HallModel model(base,k); model.evaluate();
        Emitter emitter(model); emitter.run(std::string(argv[1])+std::to_string(k)+".json");
    }
}
