#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <unordered_set>
#include <vector>

namespace ro {
using Word = std::uint64_t;
struct Stats {
    std::uint64_t entries{}, fits{}, split_tests{}, rectangles{}, orientations{}, smaller_candidates{};
    std::uint64_t collisions{}, terminal_checks{}, top_rectangles{};
    std::array<std::uint64_t,12> by_depth{}, collision_depth{}, feasible_split_depth{}, candidate_depth{};
};
struct Solver {
    using Part = unsigned;
    const std::vector<Word> wires;
    const Part full;
    Stats& stats;
    std::vector<std::vector<Word>> classes, small_tables;
    bool top_passes_rectangle=false;

    Solver(std::vector<Word> bank,Stats& counts):
        wires(std::move(bank)), full((1u<<wires.size())-1), stats(counts), classes(full+1), small_tables(full+1) {}

    const std::vector<Word>& partition(Part s) {
        auto& out=classes[s];
        if(!out.empty())return out;
        if(!s){out={~Word(0)};return out;}
        Part first=s&-s;
        Word w=wires[std::countr_zero(first)];
        auto& parent=partition(s^first);
        for(Word block:parent){
            if(block&w)out.push_back(block&w);
            if(block&~w)out.push_back(block&~w);
        }
        return out;
    }

    Word closure(Part s,Word examples) {
        Word covered=0;
        for(Word block:partition(s))if(block&examples)covered|=block;
        return covered;
    }

    // All determinate operations on S with every position used exactly once
    // and free output sign. Small side is at most four positions here.
    const std::vector<Word>& tables(Part s) {
        auto& out=small_tables[s];
        if(!out.empty())return out;
        if(std::has_single_bit(s)){
            Word a=wires[std::countr_zero(s)];
            out={a,~a};return out;
        }
        std::unordered_set<Word> options;
        for(Part a=(s-1)&s;a;a=(a-1)&s){
            Part b=s^a;
            if(a>b)continue;
            for(Word left:tables(a))for(Word right:tables(b)) {
                Word z=left&right;
                options.insert(z);options.insert(~z);
            }
        }
        out.assign(options.begin(),options.end());
        return out;
    }

    bool fit(Part s,Word yes,Word no,int depth=0) {
        ++stats.by_depth[depth];
        ++stats.fits;
        if(std::has_single_bit(s)){
            ++stats.terminal_checks;
            Word w=wires[std::countr_zero(s)];
            return (!(yes&~w)&&!(no&w))||(!(yes&w)&&!(no&~w));
        }
        if(closure(s,yes)&no){++stats.collisions;++stats.collision_depth[depth];return false;}
        for(Part a=(s-1)&s;a;a=(a-1)&s){
            Part b=s^a;
            auto na=std::popcount(a), nb=std::popcount(b);
            if(na>nb||(na==nb&&a>b))continue;
            ++stats.split_tests;
            for(int reverse=0;reverse<2;reverse++){
                Word ones=reverse?no:yes, zeros=reverse?yes:no;
                ++stats.orientations;
                if(closure(a,ones)&closure(b,ones)&zeros)continue;
                ++stats.rectangles;++stats.feasible_split_depth[depth];
                if(s==full){top_passes_rectangle=true;++stats.top_rectangles;}
                // Fix the smaller child literally. A negative row where this
                // child is already false has no constraint on the right side.
                for(Word u:tables(a)){
                    if(ones&~u)continue;
                    ++stats.smaller_candidates;++stats.candidate_depth[depth];
                    if(fit(b,ones,zeros&u,depth+1))return true;
                }
            }
        }
        return false;
    }

    bool solve(Word wanted) {++stats.entries;return fit(full,wanted,~wanted);}
};
}
