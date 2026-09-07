import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! The monomial group `C₂⁶ ⋊ D₁₈` on nine ternary coordinates. -/

namespace Kourovka.P21_29

open scoped BigOperators

abbrev Coord := ZMod 9
abbrev P := DihedralGroup 9
abbrev Sign := Multiplicative (ZMod 2)
abbrev SignPattern := Coord → Sign
abbrev FreePattern := Fin 3 → Fin 2 → Sign
abbrev V := Coord → ZMod 3

def dihedralApply : P → Coord → Coord
  | .r a, x => a + x
  | .sr a, x => -a - x

instance : MulAction P Coord where
  smul := dihedralApply
  one_smul x := by change (0 : Coord) + x = x; simp
  mul_smul g h x := by
    change dihedralApply (g * h) x = dihedralApply g (dihedralApply h x)
    cases g <;> cases h <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, dihedralApply] <;> ring

def cell (i : Fin 3) (j : Fin 3) : Coord := i.val + 3 * j.val

def row (x : Coord) : Fin 3 := ⟨x.val % 3, Nat.mod_lt _ (by omega)⟩
def col (x : Coord) : Fin 3 := ⟨x.val / 3, by have := ZMod.val_lt x; omega⟩

theorem cell_row_col (x : Coord) : cell (row x) (col x) = x := by
  revert x
  decide +kernel

def blockProd (e : SignPattern) (i : Fin 3) : Sign := ∏ j, e (cell i j)

def evenSigns : Subgroup SignPattern where
  carrier := {e | ∀ i, blockProd e i = 1}
  one_mem' := by simp [blockProd]
  mul_mem' := by
    intro a b ha hb i
    simp only [blockProd, Pi.mul_apply, Finset.prod_mul_distrib]
    exact (congrArg₂ (· * ·) (ha i) (hb i)).trans (one_mul 1)
  inv_mem' := by
    intro a ha i
    simpa [blockProd, Finset.prod_inv_distrib] using congrArg Inv.inv (ha i)

abbrev D := evenSigns

instance : Fintype Sign := Fintype.ofEquiv (ZMod 2) Multiplicative.ofAdd

def completePattern (f : FreePattern) (x : Coord) : Sign :=
  ![f (row x) 0, f (row x) 1, f (row x) 0 * f (row x) 1] (col x)

theorem completePattern_mem (f : FreePattern) : completePattern f ∈ evenSigns := by
  change ∀ i, blockProd (completePattern f) i = 1
  revert f
  decide +kernel

def complete (f : FreePattern) : D := ⟨completePattern f, completePattern_mem f⟩

def restrictPattern (e : D) : FreePattern :=
  fun i j => e.1 (cell i ⟨j.val, by omega⟩)

theorem restrict_complete (f : FreePattern) : restrictPattern (complete f) = f := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sign_sq (s : Sign) : s * s = 1 := by
  revert s
  decide +kernel

theorem prod_fin_three {M : Type*} [CommMonoid M] (f : Fin 3 → M) :
    (∏ i, f i) = f 0 * f 1 * f 2 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [mul_assoc]

theorem complete_restrict (e : D) : complete (restrictPattern e) = e := by
  apply Subtype.ext
  funext x
  rw [← cell_row_col x]
  generalize row x = i
  generalize col x = j
  have hprod := e.2 i
  rw [blockProd, prod_fin_three] at hprod
  have hlast : e.1 (cell i 0) * e.1 (cell i 1) = e.1 (cell i 2) := by
    have h := congrArg (fun z : Sign => z * e.1 (cell i 2)) hprod
    simpa only [mul_assoc, sign_sq, mul_one, one_mul] using h
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact hlast

def dEquivFree : D ≃ FreePattern where
  toFun := restrictPattern
  invFun := complete
  left_inv := complete_restrict
  right_inv := restrict_complete

instance : Fintype D := Fintype.ofEquiv FreePattern dEquivFree.symm

def reindexAut : P →* MulAut SignPattern where
  toFun p := MulEquiv.arrowCongr (MulAction.toPerm p) (MulEquiv.refl Sign)
  map_one' := by ext e x; simp
  map_mul' p q := by ext e x; simp [mul_smul]

theorem reindex_preserves_even (p : P) (e : D) :
    reindexAut p e.1 ∈ evenSigns := by
  have h : ∀ (q : P) (f : FreePattern),
      ∀ i, blockProd (reindexAut q (completePattern f)) i = 1 := by decide +kernel
  rw [← complete_restrict e]
  exact h p (restrictPattern e)

def dAction : P →* MulAut D where
  toFun p :=
    { toFun := fun e => ⟨reindexAut p e.1, reindex_preserves_even p e⟩
      invFun := fun e => ⟨reindexAut p⁻¹ e.1, reindex_preserves_even p⁻¹ e⟩
      left_inv := by
        intro e
        apply Subtype.ext
        change reindexAut p⁻¹ (reindexAut p e.1) = e.1
        rw [map_inv]
        exact (reindexAut p).left_inv e.1
      right_inv := by
        intro e
        apply Subtype.ext
        change reindexAut p (reindexAut p⁻¹ e.1) = e.1
        rw [map_inv]
        exact (reindexAut p).right_inv e.1
      map_mul' := by intro a b; ext x; simp }
  map_one' := by ext e x; simp
  map_mul' p q := by ext e x; simp

abbrev H := D ⋊[dAction] P

instance : Fintype H := Fintype.ofEquiv (D × P) SemidirectProduct.equivProd.symm

def signUnit (s : Sign) : (ZMod 3)ˣ := if s.toAdd = 0 then 1 else -1

theorem signUnit_one : signUnit 1 = 1 := rfl

theorem signUnit_mul (s t : Sign) : signUnit (s * t) = signUnit s * signUnit t := by
  revert s t
  decide +kernel

instance : DistribMulAction H V where
  smul g v x := (signUnit (g.left.1 x) : ZMod 3) * v (g.right⁻¹ • x)
  one_smul v := by funext x; change (signUnit 1 : ZMod 3) * v ((1 : P)⁻¹ • x) = v x; simp [signUnit_one]
  mul_smul g h v := by
    funext x
    change
      (signUnit ((g.left * dAction g.right h.left).1 x) : ZMod 3) *
          v ((g.right * h.right)⁻¹ • x) =
        (signUnit (g.left.1 x) : ZMod 3) *
          ((signUnit (h.left.1 (g.right⁻¹ • x)) : ZMod 3) *
            v (h.right⁻¹ • (g.right⁻¹ • x)))
    simp only [Subgroup.coe_mul, Pi.mul_apply, signUnit_mul, Units.val_mul]
    rw [mul_inv_rev, mul_smul]
    exact mul_assoc _ _ _
  smul_zero g := by funext x; exact mul_zero _
  smul_add g v w := by funext x; exact mul_add _ _ _

@[simp] theorem h_smul_apply (g : H) (v : V) (x : Coord) :
    (g • v) x = (signUnit (g.left.1 x) : ZMod 3) * v (g.right⁻¹ • x) := rfl

instance : SMulCommClass H (ZMod 3) V where
  smul_comm g a v := by
    funext x
    change (signUnit (g.left.1 x) : ZMod 3) * (a * v (g.right⁻¹ • x)) =
      a * ((signUnit (g.left.1 x) : ZMod 3) * v (g.right⁻¹ • x))
    ac_rfl

end Kourovka.P21_29
