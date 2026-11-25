#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

// Each bit is the output on one sampled input. Generate all function signatures
// realizable with exactly the indicated minimum leaf count by AND/OR closure.
int smallest(const std::vector<int>& rows, int inputs, int positives, bool signedLeaves) {
    int mask=(1<<rows.size())-1, target=(1<<positives)-1;
    std::vector<unsigned char> seen(mask+1);
    std::vector<std::vector<int>> layer(11);
    auto insert=[&](int k,int x){ if(!seen[x]) {seen[x]=k; layer[k].push_back(x);} };
    for(int j=0;j<inputs;j++) {
        int col=0;
        for(unsigned i=0;i<rows.size();i++) col |= ((rows[i]>>j)&1)<<i;
        insert(1,col);
        if(signedLeaves) insert(1,col^mask);
    }
    for(int k=2;k<=10 && !seen[target];k++) {
        for(int a=1;a<=k/2;a++) {
            for(auto x:layer[a]) for(auto y:layer[k-a]) { insert(k,x&y); insert(k,x|y); }
        }
    }
    return seen[target];
}
int main() {
    std::vector<int> core={7,11,13,14,19,21,27,30,3,5,22,25,26,28,8,6};
    std::vector<int> six={1,14,22,26,28,38,42,54,60,6,10,44,50,52,56,16,12};
    uint64_t table=(uint64_t(4276809450)<<32)+4276808362;
    int counted=0;
    for(int bits=0;bits<64;bits++) {
        auto x=[&](int i){return (bits>>i)&1;};
        int formula = x(0) | (x(3)&(x(1)|x(4))&x(2)) | ((x(4)|x(5))&x(1)&(x(2)|x(3)));
        counted += (formula==int((table>>bits)&1));
    }
    std::cout<<"witness rows matched="<<counted<<"/64\n";
    for(bool s:{false,true}) {
        int a=smallest(core,5,8,s), b=smallest(six,6,9,s);
        std::cout<<"signed="<<s<<" core="<<a<<" target="<<b<<"\n";
        if(a!=9 || b!=10 || counted!=64) return 1;
    }
}
