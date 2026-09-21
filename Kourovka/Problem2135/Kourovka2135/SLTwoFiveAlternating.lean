import Kourovka2135.SLTwoUnipotent
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! An actual epimorphism from SL2(F5) to A5 with kernel its two-element
center. The action is conjugation on five explicit subgroups of order eight.
Only bounded finite matrix certificates use `decide`; the homomorphism laws
come from the actual conjugation action, and surjectivity follows from the
proved group cardinalities and kernel. No exceptional isomorphism or Schur
multiplier statement is assumed. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section

namespace Kourovka2135.SLTwoFiveAlternating

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev S := SL(2, ZMod 5)
abbrev A := alternatingGroup (Fin 5)

def minusOne : S := ⟨!![4, 0; 0, 4], by decide⟩

/-- The five finite quaternion configurations, represented by actual matrices. -/
def quaternionSet : Fin 5 → Finset S :=
  ![{⟨!![0, 1; 4, 0], by decide⟩, ⟨!![0, 2; 2, 0], by decide⟩, ⟨!![0, 3; 3, 0], by decide⟩, ⟨!![0, 4; 1, 0], by decide⟩, ⟨!![1, 0; 0, 1], by decide⟩, ⟨!![2, 0; 0, 3], by decide⟩, ⟨!![3, 0; 0, 2], by decide⟩, ⟨!![4, 0; 0, 4], by decide⟩},
    {⟨!![1, 0; 0, 1], by decide⟩, ⟨!![1, 1; 3, 4], by decide⟩, ⟨!![2, 0; 1, 3], by decide⟩, ⟨!![2, 2; 0, 3], by decide⟩, ⟨!![3, 0; 4, 2], by decide⟩, ⟨!![3, 3; 0, 2], by decide⟩, ⟨!![4, 0; 0, 4], by decide⟩, ⟨!![4, 4; 2, 1], by decide⟩},
    {⟨!![1, 0; 0, 1], by decide⟩, ⟨!![1, 2; 4, 4], by decide⟩, ⟨!![2, 0; 3, 3], by decide⟩, ⟨!![2, 4; 0, 3], by decide⟩, ⟨!![3, 0; 2, 2], by decide⟩, ⟨!![3, 1; 0, 2], by decide⟩, ⟨!![4, 0; 0, 4], by decide⟩, ⟨!![4, 3; 1, 1], by decide⟩},
    {⟨!![1, 0; 0, 1], by decide⟩, ⟨!![1, 3; 1, 4], by decide⟩, ⟨!![2, 0; 2, 3], by decide⟩, ⟨!![2, 1; 0, 3], by decide⟩, ⟨!![3, 0; 3, 2], by decide⟩, ⟨!![3, 4; 0, 2], by decide⟩, ⟨!![4, 0; 0, 4], by decide⟩, ⟨!![4, 2; 4, 1], by decide⟩},
    {⟨!![1, 0; 0, 1], by decide⟩, ⟨!![1, 4; 2, 4], by decide⟩, ⟨!![2, 0; 4, 3], by decide⟩, ⟨!![2, 3; 0, 3], by decide⟩, ⟨!![3, 0; 1, 2], by decide⟩, ⟨!![3, 2; 0, 2], by decide⟩, ⟨!![4, 0; 0, 4], by decide⟩, ⟨!![4, 1; 3, 1], by decide⟩}]

/-- Every listed configuration has eight distinct elements. -/
theorem quaternionSet_card (i : Fin 5) : (quaternionSet i).card = 8 := by
  fin_cases i <;> decide

theorem quaternionSet_injective : Function.Injective quaternionSet := by decide

theorem quaternionSet_one_mem : ∀ i : Fin 5, (1 : S) ∈ quaternionSet i := by decide

theorem quaternionSet_mul_mem : ∀ (i : Fin 5) (g h : S),
    g ∈ quaternionSet i → h ∈ quaternionSet i → g * h ∈ quaternionSet i := by decide

theorem quaternionSet_inv_mem : ∀ (i : Fin 5) (g : S),
    g ∈ quaternionSet i → g⁻¹ ∈ quaternionSet i := by decide

/-- The five configurations are actual subgroups. -/
def quaternionSubgroup (i : Fin 5) : Subgroup S where
  carrier := {g | g ∈ quaternionSet i}
  one_mem' := quaternionSet_one_mem i
  mul_mem' := quaternionSet_mul_mem i _ _
  inv_mem' := quaternionSet_inv_mem i _

theorem quaternionSubgroup_card (i : Fin 5) : Nat.card (quaternionSubgroup i) = 8 := by
  change Nat.card {g : S // g ∈ quaternionSet i} = 8
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact quaternionSet_card i

/-- Actual group conjugation on finite sets. -/
def conjugateSet (g : S) (s : Finset S) : Finset S :=
  s.image (fun x => g * x * g⁻¹)

@[simp] theorem conjugateSet_one (s : Finset S) : conjugateSet 1 s = s := by
  simp [conjugateSet]

theorem conjugateSet_mul (g h : S) (s : Finset S) :
    conjugateSet (g * h) s = conjugateSet g (conjugateSet h s) := by
  simp only [conjugateSet, Finset.image_image]
  congr 1
  funext x
  dsimp only [Function.comp_apply]
  group

/-- The ten elementary transvections preserve the five configurations. -/
theorem transvection_preserves (i j : Fin 2) (hij : i ≠ j) (c : ZMod 5) :
    ∀ t : Fin 5, ∃ u : Fin 5,
      conjugateSet (SpecialLinearGroup.transvection hij c) (quaternionSet t) =
        quaternionSet u := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · fin_cases c <;> decide +revert
  · fin_cases c <;> decide +revert
  · exact (hij rfl).elim

/-- Preservation by every actual SL2 matrix follows from transvection induction. -/
theorem exists_conjugateSet (g : S) :
    ∀ i : Fin 5, ∃ j : Fin 5, conjugateSet g (quaternionSet i) = quaternionSet j := by
  apply Matrix.SL2.transvection_induction
    (fun g : S => ∀ i : Fin 5, ∃ j : Fin 5,
      conjugateSet g (quaternionSet i) = quaternionSet j)
  · exact transvection_preserves
  · intro g h hg hh i
    obtain ⟨j, hj⟩ := hh i
    obtain ⟨k, hk⟩ := hg j
    exact ⟨k, by rw [conjugateSet_mul, hj, hk]⟩

/-- The unique index obtained by actual conjugation. -/
def actionIndex (g : S) (i : Fin 5) : Fin 5 :=
  Classical.choose (exists_conjugateSet g i)

theorem actionIndex_spec (g : S) (i : Fin 5) :
    quaternionSet (actionIndex g i) = conjugateSet g (quaternionSet i) :=
  (Classical.choose_spec (exists_conjugateSet g i)).symm

@[simp] theorem actionIndex_one (i : Fin 5) : actionIndex 1 i = i := by
  apply quaternionSet_injective
  rw [actionIndex_spec, conjugateSet_one]

theorem actionIndex_mul (g h : S) (i : Fin 5) :
    actionIndex (g * h) i = actionIndex g (actionIndex h i) := by
  apply quaternionSet_injective
  rw [actionIndex_spec, conjugateSet_mul, ← actionIndex_spec,
    ← actionIndex_spec]

/-- Actual conjugation induces a permutation of the five subgroups. -/
def permutation (g : S) : Equiv.Perm (Fin 5) where
  toFun := actionIndex g
  invFun := actionIndex g⁻¹
  left_inv i := by rw [← actionIndex_mul, inv_mul_cancel, actionIndex_one]
  right_inv i := by rw [← actionIndex_mul, mul_inv_cancel, actionIndex_one]

def permutationHom : S →* Equiv.Perm (Fin 5) where
  toFun := permutation
  map_one' := by apply Equiv.ext; intro i; exact actionIndex_one i
  map_mul' g h := by apply Equiv.ext; intro i; exact actionIndex_mul g h i

/-- Perfectness is supplied by the proved elementary-transvection commutator
 identity, using the scalar 2 whose square is not one in F5. -/
theorem isPerfect : Group.IsPerfect S :=
  ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)⟩

theorem permutation_sign (g : S) : Equiv.Perm.sign (permutationHom g) = 1 := by
  let := isPerfect
  exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp permutationHom)
    (Group.IsPerfect.mem_commutator (g := g))

/-- The actual action lands in A5. -/
def toAlternating : S →* A :=
  permutationHom.codRestrict (alternatingGroup (Fin 5))
    (fun g => Equiv.Perm.mem_alternatingGroup.mpr (permutation_sign g))

/-- Finite matrix certificate for the common stabilizer of the five sets. -/
theorem kernel_certificate : ∀ g : S,
    (∀ i : Fin 5, conjugateSet g (quaternionSet i) = quaternionSet i) ↔
      g = 1 ∨ g = minusOne := by decide

theorem toAlternating_eq_one_iff (g : S) :
    toAlternating g = 1 ↔ g = 1 ∨ g = minusOne := by
  constructor
  · intro hg
    apply (kernel_certificate g).mp
    intro i
    have hi := congrArg (fun p : A => (p : Equiv.Perm (Fin 5)) i) hg
    change actionIndex g i = i at hi
    rw [← actionIndex_spec, hi]
  · intro hg
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply quaternionSet_injective
    exact (actionIndex_spec g i).trans ((kernel_certificate g).mpr hg i)

theorem minusOne_ne_one : minusOne ≠ (1 : S) := by decide

theorem minusOne_mem_center : minusOne ∈ Subgroup.center S := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨4, by decide, ?_⟩
  decide

/-- Central elements act trivially by actual conjugation. -/
theorem toAlternating_eq_one_of_mem_center {g : S} (hg : g ∈ Subgroup.center S) :
    toAlternating g = 1 := by
  apply (toAlternating_eq_one_iff g).mpr
  apply (kernel_certificate g).mp
  intro i
  have hfun : (fun x : S => g * x * g⁻¹) = id := by
    funext x
    have hc := Subgroup.mem_center_iff.mp hg x
    rw [← hc]
    simp [mul_assoc]
  simp only [conjugateSet, hfun, Finset.image_id]

/-- The kernel is exactly the actual center. -/
theorem ker_eq_center : toAlternating.ker = Subgroup.center S := by
  ext g
  constructor
  · intro hg
    rcases (toAlternating_eq_one_iff g).mp hg with rfl | rfl
    · exact (Subgroup.center S).one_mem
    · exact minusOne_mem_center
  · exact toAlternating_eq_one_of_mem_center

/-- The actual kernel contains exactly the matrices I and -I. -/
theorem card_ker : Nat.card toAlternating.ker = 2 := by
  apply Nat.card_eq_two_iff.mpr
  let x : toAlternating.ker := ⟨1, by simp⟩
  let y : toAlternating.ker := ⟨minusOne, (toAlternating_eq_one_iff minusOne).mpr (Or.inr rfl)⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    exact minusOne_ne_one (congrArg Subtype.val h).symm
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (toAlternating_eq_one_iff g.val).mp g.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem card_source : Nat.card S = 120 := by
  rw [SLTwo.sl2_card_formula]
  norm_num [Nat.card_eq_fintype_card]

theorem card_target : Nat.card A = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num

/-- The conjugation action is surjective onto the actual alternating group. -/
theorem toAlternating_surjective : Function.Surjective toAlternating := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup toAlternating.ker
  rw [card_source, card_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange toAlternating).toEquiv] at hc
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [card_target]
  omega

/-- The actual central quotient is isomorphic to A5. -/
def quotientCenterEquiv : S ⧸ Subgroup.center S ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq ker_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective toAlternating toAlternating_surjective)

end Kourovka2135.SLTwoFiveAlternating
