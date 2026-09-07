import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-! Affine group actions and primitivity over a prime field. -/

namespace Kourovka.P21_29

open scoped Pointwise

variable (H V : Type*) [Group H] [AddCommGroup V] [DistribMulAction H V]

/-- The action of `H` on the multiplicative wrapper of the additive group `V`. -/
def affineLinearAut : H →* MulAut (Multiplicative V) :=
  (MulAutMultiplicative V).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut H V)

/-- The affine semidirect product `V ⋊ H`. -/
abbrev AffineGroup := Multiplicative V ⋊[affineLinearAut H V] H

@[simp]
theorem affineLinearAut_apply (h : H) (v : Multiplicative V) :
    (affineLinearAut H V h v).toAdd = h • v.toAdd := rfl

instance affineMulAction : MulAction (AffineGroup H V) V where
  smul g x := g.left.toAdd + g.right • x
  one_smul x := by
    change (0 : V) + (1 : H) • x = x
    rw [one_smul, zero_add]
  mul_smul g k x := by
    change
      (g.left * affineLinearAut H V g.right k.left).toAdd +
          (g.right * k.right) • x =
        g.left.toAdd + g.right • (k.left.toAdd + k.right • x)
    simp only [toAdd_mul, affineLinearAut_apply, mul_smul, smul_add]
    abel

@[simp]
theorem affine_smul_def (g : AffineGroup H V) (x : V) :
    g • x = g.left.toAdd + g.right • x := rfl

/-- An irreducible linear group over a prime field has a preprimitive affine action. -/
theorem affine_primitive_of_irreducible
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) V]
    [SMulCommClass H (ZMod p) V]
    [Representation.IsIrreducible
      (Representation.ofDistribMulAction (ZMod p) H V)] :
    MulAction.IsPreprimitive (AffineGroup H V) V := by
  let : MulAction.IsPretransitive (AffineGroup H V) V := {
    exists_smul_eq x y := by
      refine ⟨⟨Multiplicative.ofAdd (y - x), 1⟩, ?_⟩
      change (y - x) + (1 : H) • x = y
      simp }
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (0 : V)
  intro B hzero hB
  let K : AddSubgroup V := {
    carrier := B
    zero_mem' := hzero
    add_mem' := by
      intro x y hx hy
      let tx : AffineGroup H V := ⟨Multiplicative.ofAdd x, 1⟩
      have htx0 : tx • (0 : V) = x := by simp [tx, affine_smul_def]
      have htx0_mem : tx • (0 : V) ∈ B := by simpa only [htx0] using hx
      have hEq : tx • B = B := hB.smul_eq_of_mem hzero htx0_mem
      have : tx • y ∈ tx • B := Set.mem_smul_set.mpr ⟨y, hy, rfl⟩
      rw [hEq] at this
      simpa [tx, affine_smul_def] using this
    neg_mem' := by
      intro x hx
      let tn : AffineGroup H V := ⟨Multiplicative.ofAdd (-x), 1⟩
      have htnx : tn • x = (0 : V) := by simp [tn, affine_smul_def]
      have htnx_mem : tn • x ∈ B := by simpa only [htnx] using hzero
      have hEq : tn • B = B := hB.smul_eq_of_mem hx htnx_mem
      have : tn • (0 : V) ∈ tn • B := Set.mem_smul_set.mpr ⟨0, hzero, rfl⟩
      rw [hEq] at this
      simpa [tn, affine_smul_def] using this }
  let ρ : Representation (ZMod p) H V :=
    Representation.ofDistribMulAction (ZMod p) H V
  let W : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule p K
    apply_mem_toSubmodule := by
      intro h x hx
      let lh : AffineGroup H V := ⟨1, h⟩
      have hlh0 : lh • (0 : V) = 0 := by simp [lh, affine_smul_def]
      have hlh0_mem : lh • (0 : V) ∈ B := by simpa only [hlh0] using hzero
      have hEq : lh • B = B := hB.smul_eq_of_mem hzero hlh0_mem
      have : lh • x ∈ lh • B := Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
      rw [hEq] at this
      simpa [ρ, K, lh, affine_smul_def] using this }
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · left
    intro x hx y hy
    have hx' : x ∈ W := hx
    have hy' : y ∈ W := hy
    rw [hW] at hx' hy'
    simpa using hx'.trans hy'.symm
  · right
    ext x
    simp only [Set.mem_univ, iff_true]
    have : x ∈ W := by
      rw [hW]
      exact Submodule.mem_top
    exact this

end Kourovka.P21_29
