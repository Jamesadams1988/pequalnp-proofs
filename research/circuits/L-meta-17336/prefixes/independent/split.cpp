// One exact minimum leaf count per stdin record, with explicit KW rectangle partitions.
// Input is a list of true/false separator profiles, generated independently from assignments.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using Cost = uint8_t;
using Table = std::vector<Cost>;
constexpr int positives=4096, negatives=8192;
constexpr Cost infinity=60;
using namespace std;

static vector<vector<int>> halves(int n) {
    vector<vector<int>> out(n);
    for (int set=1;set<n;set++) {
        // Enumerate the nonempty halves omitting the smallest element.
        int others=set & (set-1);
        for (int x=others; x; x=(x-1)&others) out[set].push_back(x);
    }
    return out;
}
static inline void relax(Cost* __restrict__ dest, const Cost* __restrict__ x, const Cost* __restrict__ y, int n) {
    for (int k=0;k<n;k++) dest[k]=min<Cost>(dest[k],x[k]+y[k]);
}
int main() {
    auto pSplit=halves(positives), nSplit=halves(negatives);
    vector<vector<int>> sizes(14);
    for(int n=1;n<negatives;n++) sizes[popcount((unsigned)n)].push_back(n);
    Table result(negatives*positives);
    int count;
    while(cin >> count) {
        vector<int> yes(count),no(count);
        for(int i=0;i<count;i++) cin>>yes[i]>>no[i];
        for(const auto& group:sizes) {
            if(group.empty()) continue;
            // Prior smaller negative sets are final, so their arbitrary splits are available now.
            for(int n:group) {
                Cost* row=result.data()+n*positives;
                fill(row,row+positives,infinity);
                for(int i=0;i<count;i++) if((n&no[i])==n)
                    for(int p=yes[i];p;p=(p-1)&yes[i]) row[p]=1;
                for(int small:nSplit[n]) relax(row,&result[small*positives],&result[(n^small)*positives],positives);
            }
            int width=(group.size()+63)/64*64;
            Table rotated(positives*width);
            for(int j=0;j<(int)group.size();j++)
                for(int p=1;p<positives;p++) rotated[p*width+j]=result[group[j]*positives+p];
            for(int p=1;p<positives;p++) {
                Cost* col=&rotated[p*width];
                for(int small:pSplit[p]) relax(col,&rotated[small*width],&rotated[(p^small)*width],width);
            }
            for(int j=0;j<(int)group.size();j++)
                for(int p=1;p<positives;p++) result[group[j]*positives+p]=rotated[p*width+j];
        }
        cout<<int(result.back())<<endl;
    }
}
