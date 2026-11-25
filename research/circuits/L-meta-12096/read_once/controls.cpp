#include "read_once.hpp"
#include <cstdio>
#include <random>
#include <stdexcept>
using ro::Word;
bool brute(const std::vector<Word>& w,Word p,Word n){
    if(w.size()==1){Word a=w[0];return (!(p&~a)&&!(n&a))||(!(p&a)&&!(n&~a));}
    for(unsigned i=0;i<w.size();++i)for(unsigned j=i+1;j<w.size();++j){
        Word a=w[i],b=w[j];std::vector<Word> next;
        next.push_back(0);
        for(unsigned k=0;k<w.size();++k)if(k!=i&&k!=j)next.push_back(w[k]);
        for(Word value:{a&b,a|b,a&~b,~a&b}){
            next[0]=value;
            if(brute(next,p,n))return true;
        }
    }
    return false;
}
int main(){
    std::mt19937_64 rng(1209617);int tests=0,positive=0;
    for(int n=1;n<=5;n++)for(int t=0;t<(n==5?66:180);t++){
        std::vector<Word> ws(n);for(auto& w:ws)w=rng();
        if(t%5==0)ws[0]=0;
        if(n>1 && t%4==0)ws[1]=ws[0];
        if(n>2 && t%3==0)ws[2]=~ws[0];
        Word expected=ws[0];
        for(int j=1;j<n;j++)expected=(rng()%2?expected:~expected)&(rng()%2?ws[j]:~ws[j]);
        Word care=t%3==0?~Word(0):t%3==1?rng():0x000000000000ffffULL;
        if(t%2)expected=rng();
        const Word p=expected&care, q=~expected&care;
        ro::Stats stats; ro::Solver solver(ws,stats);
        bool a=solver.fit((1u<<n)-1,p,q),b=brute(ws,p,q);
        if(a!=b)throw std::runtime_error("partial-label solver disagrees with direct gate-order traversal");
        tests++;positive+=a;
    }
    std::printf("%d partial/complete cases, %d feasible, %d infeasible; leaf signs, duplicates, constants and don't-cares checked\n",tests,positive,tests-positive);
}
