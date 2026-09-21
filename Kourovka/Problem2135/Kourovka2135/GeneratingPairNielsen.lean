import Kourovka2135.GoodSetLifting
import Mathlib.Tactic.Group

/-! The two elementary changes of a generating pair used to remove
trace-zero or trace-two second inputs without changing the commutator. -/

set_option autoImplicit false
namespace Kourovka2135.GeneratingPairNielsen
variable {G : Type*} [Group G]

theorem closure_pair_mul_left (a b : G) :
    Subgroup.closure ({a, a * b} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  let H := Subgroup.closure ({a, b} : Set G)
  let K := Subgroup.closure ({a, a * b} : Set G)
  have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbH : b ∈ H := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have haK : a ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have habK : a * b ∈ K := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rw [Set.pair_subset_iff]
    change a ∈ H ∧ a * b ∈ H
    exact ⟨haH, H.mul_mem haH hbH⟩
  · apply (Subgroup.closure_le _).mpr
    rw [Set.pair_subset_iff]
    change a ∈ K ∧ b ∈ K
    exact ⟨haK, by simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem haK) habK⟩

theorem closure_pair_inv_mul_left (a b : G) :
    Subgroup.closure ({a, a⁻¹ * b} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  simpa only [mul_inv_cancel_left] using (closure_pair_mul_left a (a⁻¹ * b)).symm

theorem commutator_mul_left (a b : G) : paperCommutator a (a * b) = paperCommutator a b := by
  unfold paperCommutator
  group

theorem commutator_inv_mul_left (a b : G) :
    paperCommutator a (a⁻¹ * b) = paperCommutator a b := by
  unfold paperCommutator
  group

end Kourovka2135.GeneratingPairNielsen
