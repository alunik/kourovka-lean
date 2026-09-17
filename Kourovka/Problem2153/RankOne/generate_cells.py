#!/usr/bin/env python3
"""Generate sparse suffix certificates for all 70 nonidentity rank-one cells.

Python is an untrusted producer. Every multiplication and every final word
identity is proved by the ordinary Lean kernel from the actual group matrices.
"""
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
STRUCT = INPUTS
sys.path.insert(0, str(STRUCT))
import collection_probe as c

DATA = json.loads((STRUCT / 'rank-one-certificate.json').read_text())
OUT = HERE / 'Cells'
OUT.mkdir(exist_ok=True)
NS = 'Kourovka.Problem2153.RootSystem.RankOne'
HEADER = '''import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.RankOne
open WilsonModel Field8 F8
'''


def atom(a):
    if a[0] in ['root', 'torus']:
        return f'Atom.{a[0]} {a[1]} {a[2]}'
    return f'Atom.{a[0]}'


def atoms(w):
    return '[' + ', '.join(atom(a) for a in w) + ']'


def matrix(a):
    if a[0] == 'root':
        return c.RF[a[1]][a[2]]
    if a[0] == 'torus':
        return c.torus(a[1] + 1, a[2] + 1)
    return c.rho if a[0] == 'rho' else c.sigma


def evaluate(w):
    result = c.I.copy()
    for a in w:
        result = c.mm(result, matrix(a))
    return result


def rword(p):
    return [('root', 1, p[0]), ('root', 3, p[1])]


def sword(p):
    return [('root', 0, p[0])]


def table(name, m):
    if c.eq(m, c.I):
        return f'private def {name} : WilsonModel.Mat := 1\n'
    rows = ['[' + ', '.join(f'({j}, e{v})' for j, v in enumerate(row) if v) + ']'
            for row in m]
    return f'private def {name} : WilsonModel.Mat := Sparse.eval (![' + ',\n    '.join(rows) + '])\n'


def emit_word(name, w, target):
    if not w:
        return f'private theorem {name} : wordMatrix [] = {target} := by decide +kernel\n'
    previous = f'{name}_s{len(w)-1}'
    result = (f'private theorem {previous} : wordMatrix {atoms(w[-1:])} = '
              f'atomMatrix ({atom(w[-1])}) := by simp\n')
    for j in reversed(range(len(w)-1)):
        this = f'{name}_s{j}'
        dest = target if j == 0 else f'{name}_m{j}'
        if j:
            result += table(dest, evaluate(w[j:]))
        result += f'''private theorem {this} : wordMatrix {atoms(w[j:])} = {dest} := by
  rw [wordMatrix_cons, {previous}]
  apply Sparse.mul_eq_of_check (atomRows ({atom(w[j])}))
  decide +kernel
'''
        previous = this
    if len(w) == 1:
        result += f'''private theorem {name} : wordMatrix {atoms(w)} = {target} := by
  rw [{previous}]
  decide +kernel
'''
    else:
        result += f'private theorem {name} : wordMatrix {atoms(w)} = {target} := {previous}\n'
    return result


families = {}
metadata = HEADER
for family in DATA['rankone']:
    kind = family['name']
    rows = family['rankone_cases']
    n = len(rows)
    pair_type = 'Fin 8 × Fin 8' if kind == 'r' else 'Fin 8'
    for name, key in [('Input', 'u'), ('Left', 'left'), ('Right', 'right')]:
        vals = [f'({p[key][0]}, {p[key][1]})' if kind == 'r' else str(p[key][0]) for p in rows]
        metadata += f'def {kind}{name} : Fin {n} → {pair_type} :=\n  ![' + ', '.join(vals) + ']\n\n'
    vals = [f'({p["torus"][0]-1}, {p["torus"][1]-1})' for p in rows]
    metadata += f'def {kind}Torus : Fin {n} → Fin 7 × Fin 7 :=\n  ![' + ', '.join(vals) + ']\n\n'
    ww = rword if kind == 'r' else sword
    nn = ('rho',) if kind == 'r' else ('sigma',)
    pairs = []
    for row in rows:
        lhs = [nn] + ww(row['u']) + [nn]
        rhs = ww(row['left']) + [('torus', row['torus'][0]-1, row['torus'][1]-1), nn] + ww(row['right'])
        assert c.eq(evaluate(lhs), evaluate(rhs)), (kind, row)
        pairs.append((lhs, rhs))
    families[kind] = pairs
    for side, idx in [('lhs', 0), ('rhs', 1)]:
        metadata += f'def {kind}_{side} : Fin {n} → List Atom :=\n  ![' + ',\n    '.join(atoms(p[idx]) for p in pairs) + ']\n\n'

metadata += f'end {NS}\n'
(OUT / 'Metadata.lean').write_text(metadata)
modules = []
for kind, pairs in families.items():
    for start in range(0, len(pairs), 6):
        module = kind.upper() + f'{start//6:02}'
        modules.append(module)
        result = HEADER.replace('RankOne.Words', 'RankOne.Cells.Metadata')
        for k in range(start, min(start + 6, len(pairs))):
            lhs, rhs = pairs[k]
            name = f'{kind}_cell_{k}'
            target = name + '_target'
            result += table(target, evaluate(lhs))
            result += emit_word(name + '_left', lhs, target)
            result += emit_word(name + '_right', rhs, target)
            result += f'''theorem {name} : wordGroup ({kind}_lhs {k}) = wordGroup ({kind}_rhs {k}) := by
  apply word_eq_of_matrix_eq
  exact {name}_left.trans {name}_right.symm

'''
        result += f'end {NS}\n'
        (OUT / (module + '.lean')).write_text(result)

result = ''.join(f'import Kourovka.Problem2153.RankOne.Cells.{m}\n' for m in modules)
result += f'\nset_option autoImplicit false\nnamespace {NS}\n'
for kind, pairs in families.items():
    result += f'''theorem {kind}_cell_checked (k : Fin {len(pairs)}) :
    wordGroup ({kind}_lhs k) = wordGroup ({kind}_rhs k) := by
  fin_cases k
'''
    result += ''.join(f'  · exact {kind}_cell_{k}\n' for k in range(len(pairs)))
result += f'end {NS}\n'
(HERE / 'Cells.lean').write_text(result)
print({'rank_one_cells': {k: len(v) for k,v in families.items()}, 'modules': modules})
