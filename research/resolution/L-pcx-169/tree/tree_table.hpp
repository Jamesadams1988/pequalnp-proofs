#pragma once
// Exact optimal leaf count for a plain resolution search tree on unary PHP(5,4).
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

struct Column {
    int occupied;  // bit mask with at most one true variable
    int excluded;  // variables already set false
    std::array<int,5> yes{}, no{};
};

using State = std::array<int,4>;
class Table {
public:
    std::vector<Column> columns;
    std::vector<int> costs;
    std::array<std::array<int,5>,117> choose{};
    int empty;
    Table() {
        int ids[32][32]{};
        for (int size=0; size<=5; ++size)
            for (int yes=0; yes<32; ++yes)
                for (int no=0; no<32; ++no) {
                    if ((yes & no) || std::popcount(unsigned(yes))>1 ||
                        std::popcount(unsigned(yes | no))!=size) continue;
                    ids[yes][no]=int(columns.size());
                    columns.push_back({yes,no});
                }
        empty=ids[0][0];
        for (auto& c : columns) for (int p=0; p<5; ++p) {
            int bit=1<<p;
            if ((c.occupied | c.excluded) & bit) continue;
            c.no[p]=ids[c.occupied][c.excluded | bit];
            c.yes[p]=c.occupied ? -1 : ids[bit][c.excluded];
        }
        for (int i=0;i<int(choose.size());++i) {
            choose[i][0]=1;
            if (i) for(int k=1;k<=4;++k)
                choose[i][k]=choose[i-1][k-1]+choose[i-1][k];
        }
        costs.resize(choose[columns.size()+3][4]);
    }
    int rank(const State& s) const {
        return s[0]+choose[s[1]+1][2]+choose[s[2]+2][3]+choose[s[3]+3][4];
    }
    int child(const State& s,int i,int replacement) const {
        if (replacement==-1) return 1;
        State t=s;
        while (i<3 && t[i+1]<replacement) { t[i]=t[i+1]; ++i; }
        t[i]=replacement;
        return costs[rank(t)];
    }
    void build() {
        // One more assigned bit always raises the column ID. The sorted child
        // is therefore later in colex order and its optimum is already known.
        for(int d=int(columns.size())-1;d>=0;--d) for(int c=d;c>=0;--c)
        for(int b=c;b>=0;--b) for(int a=b;a>=0;--a) {
            State s{a,b,c,d};
            int& value=costs[rank(s)];
            if (columns[a].excluded & columns[b].excluded & columns[c].excluded & columns[d].excluded) {
                value=1;
                continue;
            }
            value=1<<21;
            for(int i=0;i<4;++i) {
                if (i && s[i-1]==s[i]) continue;
                const Column& col=columns[s[i]];
                int available=31 ^ (col.occupied | col.excluded);
                while (available) {
                    int p=std::countr_zero(unsigned(available));
                    available &= available-1;
                    int left=child(s,i,col.no[p]), right=child(s,i,col.yes[p]);
                    if (left<=0 || right<=0) throw std::logic_error("child was not evaluated");
                    value=std::min(value,left+right);
                }
            }
            if (value==1<<21) throw std::logic_error("live state without a query");
        }
    }
};
