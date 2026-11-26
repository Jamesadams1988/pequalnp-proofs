"""Generate a Lean proof from a certified adaptive gate-elimination manifest."""
import argparse
import json
from functools import lru_cache
from pathlib import Path
import re


def vertex_mask(edges):
    return sum(1 << v for v in {i for edge in edges for i in edge})


def make(assignment, certificate, goal, fast=False):
    statement = json.loads(assignment.read_text())['statement']
    edges = frozenset(tuple(map(int, pair)) for pair in
                      re.findall(r'x (\d+) && x (\d+)', statement))
    if len(edges) != 104 or any(not 0 <= u < 21 <= v < 42 for u,v in edges):
        raise ValueError('unexpected literal graph')
    policy = {}
    for line in certificate.read_text().splitlines():
        left, right, k, v = map(int, line.split())
        key = (left | (right << 21), k)
        if key in policy:
            raise ValueError('duplicate certificate key')
        policy[key] = v
    used = set()
    declarations = []
    dec = '(by decide +kernel)'

    @lru_cache(None)
    def visit(residual, k):
        mask = vertex_mask(residual)
        if not residual:
            raise ValueError('constant residual')
        budget = max(0, k)
        if mask.bit_count() - 1 >= k:
            if fast:
                term = f'fastLeaf {mask} {budget} {dec} {dec}'
            else:
                term = f'leaf (by unfold Live; decide +kernel) {dec}'
        else:
            key = (mask, k)
            v = policy[key]
            used.add(key)
            unit = {u for edge in residual if v in edge for u in edge if u != v}
            if not unit:
                raise ValueError('inessential pivot')
            zero = frozenset(edge for edge in residual if v not in edge)
            one = frozenset(edge for edge in zero if unit.isdisjoint(edge))
            z = visit(zero, k - 2)
            o = visit(one, k - 2 - len(unit))
            nm = sum(1 << i for i in unit)
            zm, om = vertex_mask(zero), vertex_mask(one)
            if fast:
                z0 = mask ^ (1 << v)
                o0 = z0 & ~nm
                args = [mask, z0, o0, nm, zm, om, budget, max(k - 2, 0),
                        max(k - 2 - len(unit), 0), v, min(zero)[0], min(one)[0], min(unit)]
                term = 'fastBranch ' + ' '.join(map(str, args)) + ' ' + ' '.join([dec] * 11)
            else:
                term = (f'branch (v := {v}) (N := members {nm}) '
                        f'(Z := members {zm}) (O := members {om}) ' + ' '.join([dec] * 9))
            term += f' node{z} node{o}'
        index = len(declarations)
        declarations.append(f'theorem node{index} : Bound graph (members {mask}) {budget} := by\n  exact {term}\n')
        return index

    root = visit(edges, goal)
    if used != set(policy):
        raise ValueError('unreachable certificate entries')
    mod = 'Fast' if fast else 'Graph'
    namespaces = 'ProjectiveEdge.Fast ' if fast else ''
    namespaces += 'ProjectiveEdge.Adaptive ProjectiveEdge.Instance Row9769.Elimination PEqualNP.MetaComplexity'
    prologue = (f'import {mod}\n\nnamespace ProjectiveEdge.Cert{goal}\nopen {namespaces}\n'
                'set_option maxRecDepth 16000\nset_option maxHeartbeats 1000000\n\n')
    epilogue = (f'\ntheorem lower (s : ℕ) (h : HasCircuitSize 42 literal s) : {goal} ≤ s := '
                f'literalBridge _ node{root} _ h\nend ProjectiveEdge.Cert{goal}\n'
                f'#print axioms ProjectiveEdge.Cert{goal}.lower\n')
    return prologue + '\n'.join(declarations) + epilogue


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('goal', type=int)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('assignment', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--fast', action='store_true', help='generate bitmask transition checks')
    args = parser.parse_args()
    args.output.write_text(make(args.assignment, args.certificate, args.goal, args.fast))
