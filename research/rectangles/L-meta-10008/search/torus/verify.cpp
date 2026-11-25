#ifdef NDEBUG
#error "The verifier requires assertions."
#endif
#ifdef NDEBUG
#error Compile this verifier with assertions enabled.
#endif

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <unordered_set>
#include <vector>

using Mask = uint32_t;
using Perm = std::array<int,62>;
constexpr Mask full = (1u<<31)-1;
std::vector<Perm> group;
std::array<Mask,31> zeros;
int cell[31][31], cellSize[67], weight[67], maxArea[17];
int rectangleCount=0, orbitCount=0;
std::unordered_set<Mask> seen;

Mask permute(Mask a,const Perm& g){
    Mask image=0;
    for(int i=0;i<31;i++) if((a>>i)&1u) image |= 1u<<g[i];
    return image;
}

void verifyOrbit(Mask a,Mask b){
    ++rectangleCount;
    if(seen.count(a)) return;
    ++orbitCount;
    std::set<Mask> orbit;
    for(const auto& g:group) orbit.insert(permute(a,g));
    seen.insert(orbit.begin(),orbit.end());
    const int cost=orbit.size();
    assert(cost==1||cost==2||cost==4||cost==8||cost==16);
    // Each cell orbit intersecting the representative is covered completely.
    std::set<int> covered;
    for(int i=0;i<31;i++) if((a>>i)&1u)
        for(int j=0;j<31;j++) if((b>>j)&1u) {
            assert(cell[i][j]>=0); covered.insert(cell[i][j]);
        }
    int area=0, value=0;
    for(int k:covered){area+=cellSize[k];value+=weight[k];}
    maxArea[cost]=std::max(maxArea[cost],area);
    if(cost<=8) assert(value<=cost+(cost==8?4:0));
}

// Enumerate closed row sets in increasing generator order. A new closure
// introducing a row below its generator belongs to an earlier subtree.
void enumerate(Mask rows,Mask cols,int start){
    if(rows&&cols) verifyOrbit(rows,cols);
    for(int i=start;i<31;i++) if(!((rows>>i)&1u)){
        Mask newCols=cols&zeros[i],newRows=0;
        for(int j=0;j<31;j++) if(!(newCols&~zeros[j])) newRows |= 1u<<j;
        if(!((newRows^rows)&((1u<<i)-1))) enumerate(newRows,newCols,i+1);
    }
}

int main(int argc,char** argv){
    std::ifstream input(argc>1?argv[1]:"group.txt");
    int order;assert(input>>order&&order==16);
    for(int k=0;k<order;k++){
        Perm p;
        for(int& x:p) {assert(input>>x);assert(0<=x&&x<31);}
        for(int j:{0,31}) assert(std::set<int>(p.begin()+j,p.begin()+j+31).size()==31);
        group.push_back(p);
    }
    std::set<Perm> perms(group.begin(),group.end());assert(perms.size()==16);
    for(auto& p:group)for(auto& q:group){
        Perm r;for(int i=0;i<31;i++){r[i]=p[q[i]];r[31+i]=p[31+q[31+i]];}
        assert(perms.count(r));
    }
    constexpr Mask rowMasks[31]={
        1141899472,136315297,272630594,545261188,1090522376,33561105,
        67122210,134244420,268488840,536977680,1073955360,427073,854146,
        1708292,3416584,6833168,13666336,27332672,54665344,109330688,
        218661376,437322752,874645504,1749291008,1351098369,554713091,
        1109426182,71368717,142737434,285474868,570949736
    };
    for(int i=0;i<31;i++) zeros[i]=full^rowMasks[i];
    for(auto& row:cell)std::fill(row,row+31,-1);
    int n=0;
    for(int i=0;i<31;i++)for(int j=0;j<31;j++)if((zeros[i]>>j)&1u){
        if(cell[i][j]!=-1)continue;
        assert(n<67);
        for(const auto& p:group){int x=p[i],y=p[31+j];assert((zeros[x]>>y)&1u);
            assert(cell[x][y]==-1||cell[x][y]==n);
            if(cell[x][y]==-1){++cellSize[n];cell[x][y]=n;}
        }
        ++n;
    }
    assert(n==67);
    for(int i:{11,14,19})weight[i]=2;
    for(int i:{15,25,26,32,40,49})weight[i]=4;
    assert(std::accumulate(weight,weight+67,0)==30);
    assert(std::accumulate(cellSize,cellSize+67,0)==775);
    seen.reserve(1600000);
    enumerate(0,full,0);
    assert(rectangleCount==1565748&&seen.size()==1565748);
    assert(maxArea[1]==48&&maxArea[8]==352&&maxArea[16]==604);
    assert(maxArea[16]+maxArea[1]<775&&2*maxArea[8]+maxArea[1]<775);
    std::cout<<rectangleCount<<" maximal rectangles, "<<orbitCount
             <<" rectangle orbits. No invariant cover of size at most 17.\n";
}
