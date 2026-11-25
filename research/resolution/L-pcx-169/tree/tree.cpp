#include "tree_table.hpp"

int main() {
    Table t;
    t.build();
    std::cout << "column types " << t.columns.size() << ", table states " << t.costs.size()
              << ", optimum leaves " << t.costs[t.rank({t.empty,t.empty,t.empty,t.empty})] << '\n';
}
