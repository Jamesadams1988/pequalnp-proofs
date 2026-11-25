// Convert an optimal decision tree into resolution; merge syntactically equal clauses.
#include "tree_table.hpp"
#include <fstream>
#include <numeric>
#include <random>
#include <unordered_map>
#include <string>

struct Line {
    unsigned positive, negative;
    int kind;  // 0 pigeon axiom, 1 collision axiom, 2 resolution
    int x, y, z;
};
struct Trace {
    const Table& table;
    std::vector<Line> lines;
    std::unordered_map<std::uint64_t,int> known;
    std::array<int,20> order;
    int leaves=0, resolved=0;
    bool share;
    Trace(const Table& t, std::array<int,20> perm, bool sharing) :
        table(t), order(perm), share(sharing) {}
    int add(Line line) {
        std::uint64_t key=(std::uint64_t(line.positive)<<20) | line.negative;
        if (share) {
            auto [it,inserted]=known.emplace(key,int(lines.size()));
            if (!inserted) return it->second;
        }
        lines.push_back(line);
        return int(lines.size())-1;
    }
    int solve(State state) {
        int emptyRows=31;
        for (int c : state) emptyRows &= table.columns[c].excluded;
        if (emptyRows) {
            int p=std::countr_zero(unsigned(emptyRows));
            ++leaves;
            return add({15u<<(4*p),0,0,p,0,0});
        }
        State sorted=state;
        std::sort(sorted.begin(),sorted.end());
        int best=table.costs[table.rank(sorted)];
        for(int v : order) {
            int p=v/4, h=v%4;
            const auto& col=table.columns[state[h]];
            if ((col.occupied | col.excluded) & (1<<p)) continue;
            int index=int(std::lower_bound(sorted.begin(),sorted.end(),state[h])-sorted.begin());
            if (table.child(sorted,index,col.no[p])+table.child(sorted,index,col.yes[p])!=best) continue;
            State child=state;
            child[h]=col.no[p];
            int positiveParent=solve(child);
            int negativeParent;
            if (col.yes[p]==-1) {
                int other=std::countr_zero(unsigned(col.occupied));
                ++leaves;
                unsigned mask=(1u<<v) | (1u<<(4*other+h));
                negativeParent=add({0,mask,1,std::min(p,other),std::max(p,other),h});
            } else {
                child[h]=col.yes[p];
                negativeParent=solve(child);
            }
            unsigned bit=1u<<v;
            const auto& pos=lines.at(positiveParent);
            const auto& neg=lines.at(negativeParent);
            if (!(pos.positive & bit) || !(neg.negative & bit))
                throw std::logic_error("redundant split in an optimal tree");
            ++resolved;
            return add({(pos.positive & ~bit) | neg.positive,
                        pos.negative | (neg.negative & ~bit),2,negativeParent,positiveParent,v});
        }
        throw std::logic_error("optimal split missing");
    }
    std::vector<Line> compact(int root) const {
        std::vector<bool> live(lines.size(),false);
        live[root]=true;
        for (int i=root;i>=0;--i) if (live[i] && lines[i].kind==2) {
            live[lines[i].x]=true;
            live[lines[i].y]=true;
        }
        std::vector<int> index(lines.size());
        std::vector<Line> result;
        for (int i=0;i<=root;++i) if (live[i]) {
            Line line=lines[i];
            if (line.kind==2) { line.x=index[line.x]; line.y=index[line.y]; }
            index[i]=int(result.size());
            result.push_back(line);
        }
        return result;
    }
};
void save(const std::vector<Line>& lines,const std::string& path) {
    std::ofstream out(path);
    if (!out) throw std::runtime_error("cannot create trace");
    out << "[\n";
    for (std::size_t i=0; i<lines.size(); ++i) {
        const auto& l=lines[i];
        if (l.kind==0) out<<"  {\"rule\":\"pigeon\",\"p\":"<<l.x;
        if (l.kind==1) out<<"  {\"rule\":\"hole\",\"p\":"<<l.x<<",\"q\":"<<l.y<<",\"h\":"<<l.z;
        if (l.kind==2) out<<"  {\"rule\":\"res\",\"neg\":"<<l.x<<",\"pos\":"<<l.y<<",\"pivot\":"<<l.z;
        out << (i+1==lines.size() ? "}\n" : "},\n");
    }
    out<<"]\n";
}
int main(int argc,char** argv) {
    if(argc!=4) {
        std::cerr<<"usage: sample_trees TRIALS TREE_JSON DAG_JSON\n";
        return 2;
    }
    Table t; t.build();
    std::array<int,20> order{};
    std::iota(order.begin(),order.end(),0);
    std::mt19937 rng(169);
    int best=1000;
    for(int trial=0;trial<std::stoi(argv[1]);++trial) {
        if (trial>0) std::shuffle(order.begin(),order.end(),rng);
        for (int share=(trial>0);share<2;++share) {
            Trace trace(t,order,share!=0);
            int root=trace.solve({t.empty,t.empty,t.empty,t.empty});
            if(trace.lines[root].positive || trace.lines[root].negative ||
               trace.leaves!=189 || trace.resolved+1!=trace.leaves)
                throw std::logic_error("root or leaf count failed");
            auto result=trace.compact(root);
            if (!share) {
                if(result.size()!=377) throw std::logic_error("wrong unshared trace");
                save(result,argv[2]);
            } else if (int(result.size())<best) {
                best=int(result.size()); save(result,argv[3]);
                std::cout<<"Trial "<<trial<<", DAG lines "<<best<<"\n"<<std::flush;
            }
        }
    }
}
