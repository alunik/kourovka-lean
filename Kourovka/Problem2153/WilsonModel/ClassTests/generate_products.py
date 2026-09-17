from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
INPUTS = next(p for p in HERE.parents if p.name == 'Problem2153') / 'campaign-inputs'
STRUCT = INPUTS
sys.path.insert(0,str(STRUCT))
import collection_probe as c
W=[m for _,m in c.W]
invs=[next(j for j,n in enumerate(W) if c.eq(c.mm(m,n),c.I)) for m in W]
H='''import Kourovka.Problem2153.WilsonModel.ClassTests.Base
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
'''
s=H+f'def inverseIndex : Fin 16 → Fin 16 := ![{", ".join(map(str,invs))}]\n'
s+='''private theorem inverse_index_check : (fun i => Weyl.mulIndex (inverseIndex i) i) = (fun _ => (0 : Fin 16)) := by decide +kernel

theorem rep_inverse (i : Fin 16) : (Weyl.rep i)⁻¹ = Weyl.rep (inverseIndex i) := by
  apply inv_eq_of_mul_eq_one_left
  rw [Weyl.rep_mul, congrFun inverse_index_check i, Weyl.rep_zero]

def classProduct (a : Fin 7) (w : Fin 16) : RootSystem.G :=
  root 11 1 * rightConj (root 11 a.succ) (Weyl.rep w)

theorem classProduct_matrix (a : Fin 7) (w : Fin 16) :
    matrixHom (classProduct a w) = rootMatrix 11 1 *
      (WeylData.matrix (inverseIndex w) * rootMatrix 11 a.succ * WeylData.matrix w) := by
  simp only [classProduct, rightConj, rep_inverse, map_mul, matrixHom_root, matrixHom_rep]

end Kourovka.Problem2153.WilsonModel.ClassTests
'''
(HERE/'ProductBase.lean').write_text(s)
def rows(m):return '!['+',\n    '.join('['+', '.join(f'({j}, e{v})' for j,v in enumerate(row) if v)+']' for row in m)+']'
def table(n,m):return f'private def {n}Rows : Sparse.Table (Fin 26) := {rows(m)}\nprivate def {n} : Mat := Sparse.eval {n}Rows\n'
orders=[]
for w in range(0,16,2):
 s=H.replace('ClassTests.Base','ClassTests.ProductBase')
 for a in range(7):
  prefix=f'p{a}_{w}'
  q=c.mm(W[invs[w]],c.RF[11][a+1]);r=c.mm(q,W[w]);p=c.mm(c.RF[11][1],r)
  n=next(n for n in [1,2,4,5,7,13] if c.eq(c.mpow(p,n),c.I));orders.append((a,w,n))
  for name,m in [('q',q),('r',r),('p',p)]:s+=table(prefix+name,m)
  for name,leftRows,right,dest in [('q',f'WeylData.rows (inverseIndex {w})',f'rootMatrix 11 {a+1}',prefix+'q'),('r',prefix+'qRows',f'WeylData.matrix {w}',prefix+'r'),('p',f'rootRows 11 1',prefix+'r',prefix+'p')]:
   s+=f'private theorem {prefix}{name}_check : Sparse.mulEval ({leftRows}) ({right}) = {dest} := by decide +kernel\n'
  s+=f'''private theorem {prefix}_alignment : matrixHom (classProduct {a} {w}) = {prefix}p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex {w})) * rootMatrix 11 {a+1} * WeylData.matrix {w}) = {prefix}p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex {w})) _ _ {prefix}q_check]
  rw [show {prefix}q * WeylData.matrix {w} = {prefix}r from Sparse.mul_eq_of_check {prefix}qRows _ _ {prefix}r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ {prefix}p_check
'''
  # Sequential binary addition chain, with every multiplication checked on sparse rows.
  done={1:(prefix+'p',p)}
  def power(k):
   nonlocal_dummy=None
   global s
   if k in done:return done[k][0]
   b=k//2 if k%2==0 else k-1;d=k-b
   bn=power(b);dn=power(d);target=f'{prefix}pow{k}'
   m=c.mpow(p,k);s+=table(target,m)
   s+=f'''private theorem {target}_check : {bn} * {dn} = {target} := by
  apply Sparse.mul_eq_of_check {bn}Rows
  decide +kernel
private theorem {target}_eq : {prefix}p ^ {k} = {target} := by
  rw [show {k} = {b} + {d} from rfl, pow_add]
'''
   for v in set([b,d]):
    if v==1:s+='  simp only [pow_one]\n'
    else:s+=f'  rw [{prefix}pow{v}_eq]\n'
   s+=f'  exact {target}_check\n'
   done[k]=(target,m);return target
  name=power(n)
  s+=f'''theorem product_power_{a}_{w} : classProduct {a} {w} ^ {n} = 1 := by
  apply matrixHom_injective
  rw [map_pow, {prefix}_alignment, map_one]
'''
  if n!=1:s+=f'  rw [{name}_eq]\n'
  else:s+='  rw [pow_one]\n'
  s+='  decide +kernel\n\n'
 s+='end Kourovka.Problem2153.WilsonModel.ClassTests\n'
 (HERE/f'Product{w:02}.lean').write_text(s)
(HERE/'product-orders.txt').write_text(str(orders))
