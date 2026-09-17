import Kourovka.Problem2153.WilsonModel
import Kourovka.Problem2153.Collection
import Kourovka.Problem2153.BruhatReduction

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem

abbrev G := WilsonModel.ambient

def t : G := ⟨WilsonModel.tUnit, WilsonModel.tUnit_mem⟩
def x : G := ⟨WilsonModel.xUnit, WilsonModel.xUnit_mem⟩
def r : G := ⟨WilsonModel.rhoUnit, WilsonModel.rhoUnit_mem⟩
def s : G := ⟨WilsonModel.sigmaUnit, WilsonModel.sigmaUnit_mem⟩
def torus (a b : Fin 7) : G := ⟨WilsonModel.torusUnit a b, WilsonModel.torusUnit_mem a b⟩

/-- Explicit positive root curves in the certificate's fixed order. -/
def rootBase : Fin 12 → G :=
  ![t, x, rightConj x s, x ^ 2, rightConj x (s * r), rightConj t r,
    rightConj x (s * r * s), rightConj (x ^ 2) s, rightConj t (r * s),
    rightConj t (r * s * r), rightConj (x ^ 2) (s * r),
    rightConj (x ^ 2) (s * r * s)]

/-- Canonical torus sections from the independently computed collection certificate.
Field parameters use binary polynomial codes; each torus index is its nonzero field code minus1.
The zero column is unused by the definition of `root`. -/
def sectionParameters : Fin 12 → Fin 8 → Fin 7 × Fin 7 :=
  ![![(0, 0), (0, 0), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2), (0, 3)],
    ![(0, 0), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 1)],
    ![(0, 0), (0, 0), (0, 3), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2)],
    ![(0, 0), (0, 0), (0, 3), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2)],
    ![(0, 0), (0, 0), (0, 6), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)],
    ![(0, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)],
    ![(0, 0), (0, 0), (6, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)],
    ![(0, 0), (0, 0), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2), (0, 3)],
    ![(0, 0), (0, 0), (0, 3), (0, 4), (0, 5), (0, 6), (0, 1), (0, 2)],
    ![(0, 0), (0, 0), (0, 6), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)],
    ![(0, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)],
    ![(0, 0), (0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0)]]

/-- Every root value is an actual element of the generated ambient matrix subgroup. -/
def root (i : Fin 12) (a : Fin 8) : G :=
  if a = 0 then 1 else
    rightConj (rootBase i) (torus (sectionParameters i a).1 (sectionParameters i a).2)

@[simp] theorem root_zero (i : Fin 12) : root i 0 = 1 := by simp [root]

def roots : List (Fin 8 → G) :=
  [root 0, root 1, root 2, root 3, root 4, root 5,
   root 6, root 7, root 8, root 9, root 10, root 11]

def U : Subgroup G := Collection.rootClosure roots

def H : Subgroup G := Subgroup.closure (Set.range (fun p : Fin 7 × Fin 7 => torus p.1 p.2))

def W : Subgroup G := Subgroup.closure ({r, s} : Set G)

def B : Subgroup G := U ⊔ H

def N : Subgroup G := H ⊔ W

def P : Subgroup G := B ⊔ Subgroup.closure ({r} : Set G)

def Z : Subgroup G := Subgroup.closure (Set.range (root 11))

theorem torus_mem_H (a b : Fin 7) : torus a b ∈ H :=
  Subgroup.subset_closure ⟨(a,b), rfl⟩

theorem r_mem_W : r ∈ W := Subgroup.subset_closure (by simp)
theorem s_mem_W : s ∈ W := Subgroup.subset_closure (by simp)

theorem root_mem_U (i : Fin 12) (a : Fin 8) : root i a ∈ U := by
  apply Subgroup.subset_closure
  refine ⟨root i, ?_, a, rfl⟩
  fin_cases i <;> simp [roots]

end Kourovka.Problem2153.RootSystem
