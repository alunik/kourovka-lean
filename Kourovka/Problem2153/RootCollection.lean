import Kourovka.Problem2153.RootRelations
import Kourovka.Problem2153.RankOne.Basic

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.RootCollection
open WilsonModel.RootData.Relations RootRelations RankOne

theorem coordinateGroup_mem (v : Coordinates) (Q : Subgroup G)
    (h : ∀ i, v i ≠ 0 → root i (v i) ∈ Q) : coordinateGroup v ∈ Q := by
  apply Q.list_prod_mem
  intro g hg
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
  by_cases hi : v i = 0
  · simp [hi]
  · exact h i hi

theorem singleton_product_check : ∀ i : Fin 12, i = 0 ∨ i = 3 → ∀ a b : Fin 8,
    productCoordinates i a b = singleCoordinate i (productCoordinates i a b i) := by
  decide +kernel

theorem singleton_inverse_check : ∀ i : Fin 12, i = 0 ∨ i = 3 → ∀ a : Fin 8,
    inverseCoordinates i a = singleCoordinate i a := by decide +kernel

def pair13Coordinates (a b : Fin 8) : Coordinates :=
  fun j => if j = 1 then a else if j = 3 then b else 0

theorem pair13_product_check : ∀ a b : Fin 8,
    productCoordinates 1 a b =
      pair13Coordinates (productCoordinates 1 a b 1) (productCoordinates 1 a b 3) := by
  decide +kernel

theorem pair13_inverse_check : ∀ a : Fin 8,
    inverseCoordinates 1 a =
      pair13Coordinates (inverseCoordinates 1 a 1) (inverseCoordinates 1 a 3) := by
  decide +kernel

theorem pair13_commutator_check : ∀ a b : Fin 8,
    commutatorCoordinates 1 3 a b = (fun _ => 0) := by decide +kernel

theorem coordinateGroup_pair13 (a b : Fin 8) :
    coordinateGroup (pair13Coordinates a b) = root 1 a * root 3 b := by
  simp [coordinateGroup, pair13Coordinates, List.ofFn_succ]

theorem singleton_product (i : Fin 12) (hi : i = 0 ∨ i = 3) (a b : Fin 8) :
    root i a * root i b = root i (productCoordinates i a b i) := by
  conv_lhs => rw [root_product, singleton_product_check i hi, coordinateGroup_single]

theorem singleton_inverse (i : Fin 12) (hi : i = 0 ∨ i = 3) (a : Fin 8) :
    (root i a)⁻¹ = root i a := by
  rw [root_inverse, singleton_inverse_check i hi, coordinateGroup_single]

/-- The rank-one root curves at indices 0 and 3 are actual eight-element parameter families. -/
def singletonSubgroup (i : Fin 12) (hi : i = 0 ∨ i = 3) : Subgroup G where
  carrier := Set.range (root i)
  one_mem' := ⟨0, root_zero i⟩
  mul_mem' := by
    rintro g h ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨_, (singleton_product i hi a b).symm⟩
  inv_mem' := by
    rintro g ⟨a,rfl⟩
    exact ⟨a, (singleton_inverse i hi a).symm⟩

theorem singletonSubgroup_eq_closure (i : Fin 12) (hi : i = 0 ∨ i = 3) :
    singletonSubgroup i hi = Subgroup.closure (Set.range (root i)) := by
  apply le_antisymm
  · rintro g ⟨a,rfl⟩
    exact Subgroup.subset_closure ⟨a,rfl⟩
  · exact (Subgroup.closure_le _).mpr (fun _ h => h)

theorem root_one_three_commute (a b : Fin 8) : Commute (root 1 a) (root 3 b) := by
  have h := root_commutator 1 3 a b (by decide)
  rw [pair13_commutator_check, coordinateGroup_zero] at h
  change root 1 a * root 3 b = root 3 b * root 1 a
  have hh := congrArg (fun g => root 3 b * root 1 a * g) h
  simpa [mul_assoc] using hh

def rankStep : Collection.Step (singletonSubgroup 3 (Or.inr rfl)) (root 1) where
  zero := 0
  at_zero := root_zero 1
  multiply := by
    intro a b
    refine ⟨productCoordinates 1 a b 1, root 3 (productCoordinates 1 a b 3),
      ⟨_,rfl⟩, ?_⟩
    conv_lhs => rw [root_product, pair13_product_check, coordinateGroup_pair13]
  invert := by
    intro a
    refine ⟨inverseCoordinates 1 a 1, root 3 (inverseCoordinates 1 a 3),
      ⟨_,rfl⟩, ?_⟩
    conv_lhs => rw [root_inverse, pair13_inverse_check, coordinateGroup_pair13]
  normalize := by
    rintro a g ⟨b,rfl⟩
    change rightConj (root 3 b) (root 1 a) ∈ singletonSubgroup 3 (Or.inr rfl)
    rw [(rightConj_fixed_iff _ _).mpr (root_one_three_commute a b).symm]
    exact ⟨b,rfl⟩

theorem Rr_eq_rankStep : Rr = rankStep.subgroup := by
  rw [Rr_eq, rankStep.subgroup_eq_closure]
  rfl

theorem Rr_coverage {g : G} (hg : g ∈ Rr) : ∃ p : Fin 8 × Fin 8, g = rRoot p := by
  rw [Rr_eq_rankStep] at hg
  obtain ⟨a,z,⟨b,rfl⟩,h⟩ := hg
  exact ⟨(a,b),h⟩

theorem Rs_coverage {g : G} (hg : g ∈ Rs) : ∃ a : Fin 8, g = sRoot a := by
  change g ∈ Subgroup.closure (Set.range (root 0)) at hg
  rw [← singletonSubgroup_eq_closure 0 (Or.inl rfl)] at hg
  obtain ⟨a,rfl⟩ := hg
  exact ⟨a,rfl⟩

end Kourovka.Problem2153.RootSystem.RootCollection
