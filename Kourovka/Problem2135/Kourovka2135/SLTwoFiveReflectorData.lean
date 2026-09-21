import Kourovka2135.SLTwoFiveAlternating
import Kourovka2135.A5RelativeModuleCertificate
import Kourovka2135.DerivedCentralization
import Mathlib.Tactic.IntervalCases

/-! Concrete matrix witnesses for the order-three reflector over the fixed
A5 relative-module certificate. All matrix and finite permutation identities
are checked by ordinary decide. Images under the noncomputable epimorphism
are proved from its actual conjugation-index specification. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section

namespace Kourovka2135.SLTwoFiveReflectorData

open Matrix SLTwoFiveAlternating A5RelativeModuleCertificate
open scoped MatrixGroups

/-- The involution (01)(34), fixing the point 2 stabilized by L. -/
def t : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
  simp [Equiv.Perm.mem_alternatingGroup]⟩

/-- The first projective input is the three-cycle (043). -/
def projectiveB : A5 := ⟨Equiv.swap 0 4 * Equiv.swap 4 3, by
  simp [Equiv.Perm.mem_alternatingGroup]⟩

def uE : S := ⟨!![0, 1; 4, 4], by decide⟩
def b : S := ⟨!![0, 1; 4, 1], by decide⟩
def c : S := ⟨!![0, 2; 2, 1], by decide⟩
def a : S := ⟨!![2, 0; 3, 3], by decide⟩

/-- Identify the actual epimorphism without evaluating its classical index choice. -/
theorem toAlternating_eq_of_conjugateSet (g : S) (p : A5)
    (hp : ∀ i : Fin 5,
      conjugateSet g (quaternionSet i) = quaternionSet (p.val i)) :
    toAlternating g = p := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change actionIndex g i = p.val i
  apply quaternionSet_injective
  exact (actionIndex_spec g i).trans (hp i)

@[simp] theorem toAlternating_uE : toAlternating uE = u :=
  toAlternating_eq_of_conjugateSet uE u (by decide)

@[simp] theorem toAlternating_b : toAlternating b = projectiveB :=
  toAlternating_eq_of_conjugateSet b projectiveB (by decide)

@[simp] theorem toAlternating_c : toAlternating c = w :=
  toAlternating_eq_of_conjugateSet c w (by decide)

@[simp] theorem toAlternating_a : toAlternating a = t :=
  toAlternating_eq_of_conjugateSet a t (by decide)

theorem orderOf_uE : orderOf uE = 3 := by
  apply (orderOf_eq_iff (by decide : 0 < 3)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hp
  interval_cases m <;> decide

theorem orderOf_b : orderOf b = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hp
  interval_cases m <;> decide

theorem orderOf_c : orderOf c = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hp
  interval_cases m <;> decide

theorem orderOf_a : orderOf a = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hp
  interval_cases m <;> decide

/-- The actual reflector is a commutator of the two order-six matrices. -/
theorem a_eq_commutator : a = paperCommutator b c := by decide

/-- The actual reflector inverts the chosen order-three subgroup. -/
theorem a_inv_conjugates_uE : a⁻¹ * uE * a = uE⁻¹ := by decide

theorem a_conjugates_uE : a * uE * a⁻¹ = uE⁻¹ := by decide

/-- The corresponding projective reflector has the required inversion action. -/
theorem t_inv_conjugates_u : t⁻¹ * u * t = u⁻¹ := by decide

theorem t_mem_L : t ∈ L := by
  change t.val (2 : Fin 5) = 2
  decide

theorem projectiveB_mem_L : projectiveB ∈ L := by
  change projectiveB.val (2 : Fin 5) = 2
  decide

theorem image_b_mem_L : toAlternating b ∈ L := by
  rw [toAlternating_b]
  exact projectiveB_mem_L

theorem image_c_mem_L : toAlternating c ∈ L := by
  rw [toAlternating_c]
  exact w_mem_L

/-- The relative-module certificate's w is already the second input's image. -/
theorem w_mem_image_closure :
    w ∈ Subgroup.closure ({toAlternating b, toAlternating c} : Set A5) := by
  rw [← toAlternating_c]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The concrete final odd commutator identity, with the paper convention. -/
theorem commutator_a_conjugate : paperCommutator a (uE⁻¹ * a * uE) = uE := by decide

end Kourovka2135.SLTwoFiveReflectorData
