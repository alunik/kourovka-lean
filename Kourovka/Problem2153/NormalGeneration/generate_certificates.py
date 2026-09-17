#!/usr/bin/env python3
"""Generate sparse suffix certificates for normal generation and perfectness.

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

OUT = HERE
OUT.mkdir(exist_ok=True)
NS = 'Kourovka.Problem2153.RootSystem.NormalGeneration'
HEADER = '''import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
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


D=json.loads((STRUCT / 'simplicity-certificate.json').read_text())
def root(i,a): return ('root',i,a)
rho=('rho',); sigma=('sigma',)
def tor(a,b): return ('torus',a-1,b-1)
z0=root(3,1)
k=next(a for a in range(8) if c.eq(c.conj(c.RF[3][1],c.torus(1,2)), c.RF[3][a]))
za=next(a for a in range(8) if c.eq(c.conj(c.RF[11][1],c.torus(6,1)),c.RF[11][a]))
gens=[[z0],[root(3,k)],[rho,z0,rho]]
cases={}
for key,target in [('rho',[rho]),('x',[root(1,1)]),('h(1,2)',[tor(1,2)])]:
 name={'rho':'SuzukiR','x':'SuzukiX','h(1,2)':'SuzukiH'}[key]
 cases[name]=(sum((gens[i] for i in D['suzuki_target_words'][key]),[]),target)
cases['RootComm']=([root(1,1)]*3+[root(4,1)]*3+[root(1,1),root(4,1)],[root(5,1)])
cases['SL2']=([root(0,1),sigma,root(0,1),sigma,root(0,1)],[sigma])
cases['Perfect']=([root(11,za),tor(5,1),root(11,za),tor(2,1)],[root(11,1)])
cases['PerfectSquare']=([root(11,za)]*2,[])
w0=[rho,sigma]*4
cases['W0SL2']=([root(0,1)]+w0[::-1]+[root(0,1)]+w0+[root(0,1)],[sigma])
mods=[]
for name,(lhs,rhs) in cases.items():
 assert c.eq(evaluate(lhs),evaluate(rhs)),name
 out=HEADER+table(name+'_target',evaluate(rhs))
 out+=emit_word(name+'_left',lhs,name+'_target')+emit_word(name+'_right',rhs,name+'_target')
 out+=f"theorem {name}_checked : wordGroup {atoms(lhs)} = wordGroup {atoms(rhs)} := by\n  apply word_eq_of_matrix_eq\n  exact {name}_left.trans {name}_right.symm\n\nend {NS}\n"
 (OUT/(name+'.lean')).write_text(out)
 mods.append(name)
(OUT/'Certificates.lean').write_text(''.join(f'import Kourovka.Problem2153.NormalGeneration.{m}\n' for m in mods if m != 'W0SL2'))
print({'suzuki_parameter':k,'perfect_parameter':za,'word_lengths':{k:len(v[0]) for k,v in cases.items()}})
