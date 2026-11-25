#pragma once
// Price a single reusable Hall clause by two exact tree computations.
#include "../tree_table.hpp"
#include <functional>

using Groups = std::vector<State>;

Groups multisets(int length, int types) {
    State current{};
    Groups out;
    std::function<void(int,int)> visit=[&](int index,int end) {
        if (index<0) { out.push_back(current); return; }
        for (int i=0;i<end;++i) { current[index]=i; visit(index-1,i+1); }
    };
    visit(length-1,types);
    return out;
}

struct HallModel {
    const Table& base;
    int k, affected;
    Groups in, out;
    std::vector<int> values;
    HallModel(const Table& t,int size) : base(t), k(size), affected((1<<(k+1))-1),
        in(multisets(k,int(t.columns.size()))), out(multisets(4-k,int(t.columns.size()))),
        values(in.size()*out.size()) {}

    int groupRank(const State& s,int length) const {
        int rank=0;
        for(int i=0;i<length;++i) rank+=base.choose[s[i]+i][i+1];
        return rank;
    }
    int updatedRank(State s,int size,int index,int next) const {
        while (index+1<size && s[index+1]<next) {
            s[index]=s[index+1]; ++index;
        }
        s[index]=next;
        return groupRank(s,size);
    }
    void evaluate() {
        for(int i=int(in.size())-1;i>=0;--i) for(int j=int(out.size())-1;j>=0;--j) {
            int idx=i*int(out.size())+j;
            int rejectedIn=31, rejectedOut=31;
            for(int c=0;c<k;++c) rejectedIn &= base.columns[in[i][c]].excluded;
            for(int c=0;c<4-k;++c) rejectedOut &= base.columns[out[j][c]].excluded;
            if ((rejectedIn & rejectedOut) || ((rejectedOut & affected)==affected)) {
                values[idx]=1; continue;
            }
            int best=1000000;
            for(int side=0;side<2;++side) {
                const State& s=side ? out[j] : in[i];
                int length=side ? 4-k : k;
                for(int c=0;c<length;++c) {
                    if(c && s[c]==s[c-1]) continue;
                    const Column& col=base.columns[s[c]];
                    int available=31 ^ (col.occupied | col.excluded);
                    auto cost=[&](int replacement) {
                        if (replacement==-1) return 1;
                        int rank=updatedRank(s,length,c,replacement);
                        int index=side ? i*int(out.size())+rank : rank*int(out.size())+j;
                        if(index<=idx || !values[index]) throw std::logic_error("invalid child");
                        return values[index];
                    };
                    while (available) {
                        int p=std::countr_zero(unsigned(available));
                        available &= available-1;
                        best=std::min(best,cost(col.yes[p])+cost(col.no[p]));
                    }
                }
            }
            if(best==1000000) throw std::logic_error("no informative variable");
            values[idx]=best;
        }
    }
    int premiseLeaves() const {
        int maskId=-1;
        for(int id=0;id<int(base.columns.size());++id)
            if(base.columns[id].occupied==0 && base.columns[id].excluded==affected) maskId=id;
        if(maskId<0) throw std::logic_error("missing normalized column");
        State s{};
        for(int i=k;i<4;++i) s[i]=maskId;
        return base.costs[base.rank(s)];
    }
};
