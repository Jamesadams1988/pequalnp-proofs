#include "hall_table.hpp"
int main() {
    Table base; base.build();
    for(int k=1;k<4;++k) {
        HallModel extra(base,k);
        extra.evaluate();
        int first=extra.premiseLeaves(), last=extra.values[0];
        std::cout<<"k="<<k<<" preparation leaves "<<first<<", final leaves "<<last
                 <<", mechanism needs at least "<<45+(first-1)+(last-1)<<" lines ("
                 <<extra.values.size()<<" states for the final tree).\n";
    }
}
