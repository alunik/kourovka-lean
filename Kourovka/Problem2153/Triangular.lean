import Kourovka.Problem2153.WilsonModel.RootData.Alignment

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem

open WilsonModel

/-- Lower triangularity of the actual matrix representation. -/
def IsLower (g : G) : Prop :=
  ∀ i j : Fin 26, i < j → RootData.matrixHom g i j = 0

private def lowerMonoid : Submonoid G where
  carrier := {g | IsLower g}
  one_mem' := by
    intro i j hij
    change (1 : Mat) i j = 0
    exact Matrix.one_apply_ne (ne_of_lt hij)
  mul_mem' := by
    intro g h hg hh i j hij
    rw [map_mul, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i < k
    · rw [hg i k hik, zero_mul]
    · rw [hh k j (lt_of_le_of_lt (le_of_not_gt hik) hij), mul_zero]

/-- In a finite group, closure under multiplication also supplies inverses. -/
def lowerSubgroup : Subgroup G where
  carrier := {g | IsLower g}
  one_mem' := lowerMonoid.one_mem
  mul_mem' := lowerMonoid.mul_mem
  inv_mem' := by
    intro g hg
    change g⁻¹ ∈ lowerMonoid
    rw [← one_mul g⁻¹, ← pow_one g, ← pow_orderOf_eq_one g,
      ← pow_sub g (orderOf_pos g)]
    exact lowerMonoid.pow_mem hg (orderOf g - 1)

def upperPart (m : Mat) : Mat := fun i j => if i < j then m i j else 0

theorem rootMatrix_upper_check : ∀ i : Fin 12, ∀ a : Fin 8,
    upperPart (RootData.rootMatrix i a) = 0 := by
  decide +kernel

theorem rootMatrix_lower (i : Fin 12) (a : Fin 8) (j k : Fin 26) (hjk : j < k) :
    RootData.rootMatrix i a j k = 0 := by
  have h := congrFun (congrFun (rootMatrix_upper_check i a) j) k
  simpa only [upperPart, hjk, ite_true, Matrix.zero_apply] using h

theorem root_lower (i : Fin 12) (a : Fin 8) : root i a ∈ lowerSubgroup := by
  intro j k hjk
  change ((root i a).val : Mat) j k = 0
  rw [RootData.root_alignment]
  exact rootMatrix_lower i a j k hjk

theorem U_le_lower : U ≤ lowerSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨curve, hcurve, a, rfl⟩
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hcurve
  rcases hcurve with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact root_lower _ a

theorem torus_lower (a b : Fin 7) : torus a b ∈ lowerSubgroup := by
  intro i j hij
  change Matrix.diagonal (torusDiag a b) i j = 0
  exact Matrix.diagonal_apply_ne _ (ne_of_lt hij)

theorem H_le_lower : H ≤ lowerSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨a,b⟩, rfl⟩
  exact torus_lower a b

theorem B_le_lower : B ≤ lowerSubgroup := sup_le U_le_lower H_le_lower

end Kourovka.Problem2153.RootSystem
