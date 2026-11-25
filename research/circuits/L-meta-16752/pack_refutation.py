#!/usr/bin/env python3
"""Rebuild the refutation of the posted negative L-meta-16752 statement.

Run python3 pack_refutation.py /path/to/pequalnp-proofs /tmp/L_meta_16752.lean.
Keep statement.txt and PositiveTwin.lean beside this script. FreshOutput.lean is
read from the adjacent L-meta-15094 research directory, or from --fresh-output.
The output must be a new file. Use the official checker in refute mode.
"""
import argparse
from hashlib import sha256
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROW = 'PEqualNP.Outside.L_meta_16752'
ELIM = 'PEqualNP.Outside.L_meta_4795_aux'
FIVE = 'PEqualNP.Outside.L_meta_8642'


def pinned(path, digest):
    data = path.read_bytes()
    actual = sha256(data).hexdigest()
    if actual != digest:
        raise ValueError(f'{path}: expected SHA-256 {digest}, got {actual}')
    return data.decode('utf-8')


def section(name, body):
    qualified = ROW + '.' + name
    return f'namespace {qualified}\n\n{body.strip()}\n\nend {qualified}'


def assemble(upstream, fresh_path):
    outside = upstream / 'lean/PEqualNP/Outside'
    eliminate = pinned(outside / 'L_meta_4795.lean',
        '5e85e410b1778e17b12481072680e6bdc76b5a8de2aa1d9ac6d69d1ee1c43c33')
    core = pinned(outside / 'L_meta_8642.lean',
        '9fb59e06d77355982a78271929fb1e9f0d4964d713787d29f74157257edd849a')
    fresh = pinned(fresh_path,
        '463c100cd53707a525f490537fe82c4026c11f17e4a63373afbae0ca8cb34083')
    case = pinned(HERE / 'PositiveTwin.lean',
        'c13bde6e77e3d90d815575d46e89b9028ea6d3fe9546be9953346fe9f30894fe')
    statement = pinned(HERE / 'statement.txt',
        'b0c15cf3ee0b58ae3f554e7ab9ecf78a4e689abc44c5fc7888a012c6a16986af')

    # The proof uses gate_elim_one and the relabeling machinery through relabel_size.
    _, eliminate = eliminate.split(f'namespace {ELIM}\n', 1)
    first, rest = eliminate.split('\ntheorem simplify_const ', 1)
    _, second = rest.split('\ndef wmap ', 1)
    second, _ = second.split('\ntheorem snoc_swap ', 1)
    eliminate = first.rstrip() + '\n\ndef wmap ' + second.rstrip()

    # The donor's local solve lemma is definitionally equal to its public theorem.
    _, core = core.split(f'namespace {FIVE}\n', 1)
    core, _ = core.split(f'\nend {FIVE}\n', 1)
    _, fresh = fresh.split('namespace FreshOutput\n', 1)
    fresh, _ = fresh.split('\nnamespace Row15094\n', 1)
    fresh = fresh.replace(ELIM, ROW + '.Elimination')
    _, case = case.split('namespace Row16752\n', 1)
    case, _ = case.split('\nend Row16752\n', 1)
    case = case.replace(ELIM, ROW + '.Elimination').replace(FIVE, ROW + '.FiveInput.solve')
    case = case.replace('open FreshOutput', f'open {ROW}.FreshOutput')

    credits = ('/-! Fresh-output transfer by James Adams. The five-input monotone replacement\n'
               'is k-sandhu’s L-meta-8642 (PR 12867), drawing on L-meta-8463 and L-meta-1449.\n'
               'The elimination and input relabeling proofs are from Nico Habets (nicohabets),\n'
               'L-meta-4795 (PR 9322), crediting sanchan’s L-meta-927 (PR 1992).\n'
               'Earlier positive proofs for L-meta-16751 are by azizsayadi1155 (PR 21184)\n'
               'and Leg0shii (PR 21234). -/')
    final = f'theorem {ROW} : ¬ ({statement}) :=\n  {ROW}.Application.assignedNegativeFalse'
    parts = ['import PEqualNP.Defs', credits, section('Elimination', eliminate),
             section('FiveInput', core), section('FreshOutput', fresh), section('Application', case), final]
    return '\n'.join(line.rstrip() for line in '\n\n'.join(parts).splitlines()) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('upstream', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--fresh-output', type=Path,
                        default=HERE.parent / 'L-meta-15094/FreshOutput.lean')
    args = parser.parse_args()
    try:
        data = assemble(args.upstream, args.fresh_output).encode('utf-8')
        with args.output.open('xb') as out:
            out.write(data)
    except (OSError, ValueError) as error:
        parser.exit(1, f'{parser.prog}: {error}\n')


if __name__ == '__main__':
    main()
