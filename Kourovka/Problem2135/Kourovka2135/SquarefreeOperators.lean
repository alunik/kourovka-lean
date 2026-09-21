import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Creation and annihilation operators on the free module with basis indexed
by finite subsets. Their explicit relations give a contracting homotopy for
any nonempty finite sum of creation operators in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SquarefreeOperators

open Finset
open scoped CharTwo

variable {ι : Type*} [DecidableEq ι]

/-- The free module whose basis vectors are finite subsets of the index type. -/
abbrev Space (ι : Type*) (k : Type*) [Zero k] := Finset ι →₀ k

variable (k : Type*) [Semiring k]

/-- Insert an index when it is absent, and kill basis vectors containing it. -/
def creation (i : ι) : Module.End k (Space ι k) :=
  Finsupp.linearCombination k fun J =>
    if i ∈ J then 0 else Finsupp.single (insert i J) 1

/-- Remove an index when it is present, and kill basis vectors not containing it. -/
def annihilation (i : ι) : Module.End k (Space ι k) :=
  Finsupp.linearCombination k fun J =>
    if i ∈ J then Finsupp.single (J.erase i) 1 else 0

@[simp] theorem creation_single (i : ι) (J : Finset ι) (c : k) :
    creation k i (Finsupp.single J c) =
      if i ∈ J then 0 else Finsupp.single (insert i J) c := by
  by_cases hi : i ∈ J <;> simp [creation, hi, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem annihilation_single (i : ι) (J : Finset ι) (c : k) :
    annihilation k i (Finsupp.single J c) =
      if i ∈ J then Finsupp.single (J.erase i) c else 0 := by
  by_cases hi : i ∈ J <;> simp [annihilation, hi, Finsupp.smul_single, smul_eq_mul]

/-- Creation has square zero over every coefficient semiring. -/
@[simp] theorem creation_mul_self (i : ι) : creation k i * creation k i = 0 := by
  apply Finsupp.lhom_ext
  intro J c
  by_cases hi : i ∈ J <;> simp [Module.End.mul_apply, hi]

/-- Annihilation has square zero over every coefficient semiring. -/
@[simp] theorem annihilation_mul_self (i : ι) :
    annihilation k i * annihilation k i = 0 := by
  apply Finsupp.lhom_ext
  intro J c
  by_cases hi : i ∈ J <;> simp [Module.End.mul_apply, hi]

/-- Exactly one of creation-after-annihilation and annihilation-after-creation
fixes each basis vector. -/
theorem creation_annihilation_add (i : ι) :
    creation k i * annihilation k i + annihilation k i * creation k i = 1 := by
  apply Finsupp.lhom_ext
  intro J c
  by_cases hi : i ∈ J
  · simp [Module.End.mul_apply, hi, Finset.insert_erase hi]
  · simp [Module.End.mul_apply, hi, Finset.erase_insert hi]

/-- Creation and annihilation at different indices commute. -/
theorem creation_annihilation_commute (i j : ι) (hij : i ≠ j) :
    creation k i * annihilation k j = annihilation k j * creation k i := by
  apply Finsupp.lhom_ext
  intro J c
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J <;>
    simp [Module.End.mul_apply, hi, hj, hij, Ne.symm hij, Finset.erase_insert_of_ne hij]

/-- Creation operators commute, including at a repeated index. -/
theorem creation_commute (i j : ι) :
    creation k i * creation k j = creation k j * creation k i := by
  by_cases hij : i = j
  · subst j
    rfl
  apply Finsupp.lhom_ext
  intro J c
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J <;>
    simp [Module.End.mul_apply, hi, hj, hij, Ne.symm hij, Finset.insert_comm]

/-- Every nonzero basis term produced by creation raises the subset degree by one. -/
theorem creation_single_support_card (i : ι) (J K : Finset ι) (c : k)
    (hK : K ∈ (creation k i (Finsupp.single J c)).support) :
    K.card = J.card + 1 := by
  by_cases hi : i ∈ J
  · simp [hi] at hK
  · rw [creation_single, ite_eq_right hi] at hK
    have hKeq : K = insert i J := (Finsupp.mem_support_single _ _ _).mp hK |>.1
    rw [hKeq, Finset.card_insert_of_notMem hi]

/-- Every nonzero basis term produced by annihilation lowers the subset degree by one. -/
theorem annihilation_single_support_card (i : ι) (J K : Finset ι) (c : k)
    (hK : K ∈ (annihilation k i (Finsupp.single J c)).support) :
    K.card + 1 = J.card := by
  by_cases hi : i ∈ J
  · rw [annihilation_single, ite_eq_left hi] at hK
    have hKeq : K = J.erase i := (Finsupp.mem_support_single _ _ _).mp hK |>.1
    rw [hKeq]
    exact Finset.card_erase_add_one hi
  · simp [hi] at hK

/-- The differential attached to a finite collection of active indices. -/
def differential (S : Finset ι) : Module.End k (Space ι k) :=
  ∑ i ∈ S, creation k i

@[simp] theorem differential_empty : differential k (∅ : Finset ι) = 0 := by
  simp [differential]

@[simp] theorem differential_insert (S : Finset ι) (i : ι) (hi : i ∉ S) :
    differential k (insert i S) = creation k i + differential k S := by
  simp [differential, hi]

/-- A basis-level formula retaining the degree-raising nature of the differential. -/
theorem differential_single (S J : Finset ι) (c : k) :
    differential k S (Finsupp.single J c) =
      ∑ i ∈ S, if i ∈ J then 0 else Finsupp.single (insert i J) c := by
  simp [differential]

section CharacteristicTwo
variable [CharP k 2]

omit [DecidableEq ι] in
/-- Endomorphisms of the squarefree module add to zero with themselves in
characteristic two. This proof does not need a separate characteristic instance
on the endomorphism ring. -/
theorem end_add_self (F : Module.End k (Space ι k)) : F + F = 0 := by
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro J
  change F x J + F x J = 0
  exact CharTwo.add_self_eq_zero _

/-- Any active index supplies an explicit contracting homotopy for the
finite creation differential. -/
theorem differential_annihilation_add (S : Finset ι) (j : ι) (hj : j ∈ S) :
    differential k S * annihilation k j + annihilation k j * differential k S = 1 := by
  calc
    _ = ∑ i ∈ S, (creation k i * annihilation k j +
        annihilation k j * creation k i) := by
      rw [differential, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
    _ = creation k j * annihilation k j + annihilation k j * creation k j := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        rw [creation_annihilation_commute k i j hij]
        exact end_add_self k _
      · intro hnot
        exact (hnot hj).elim
    _ = 1 := creation_annihilation_add k j

/-- Pairwise commutation and characteristic two cancel all cross terms;
each diagonal term already vanishes. -/
theorem differential_mul_self (S : Finset ι) :
    differential k S * differential k S = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [differential_insert k S i hi, add_mul, mul_add, mul_add,
        creation_mul_self, ih, zero_add, add_zero]
      have hcomm : creation k i * differential k S = differential k S * creation k i := by
        simp only [differential, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        exact creation_commute k i j
      rw [hcomm]
      exact end_add_self k _

/-- The explicit contracting identity proves exactness for every nonempty
active set. No exactness hypothesis is assumed. -/
theorem differential_ker_eq_range (S : Finset ι) (hS : S.Nonempty) :
    (differential k S).ker = (differential k S).range := by
  obtain ⟨j, hj⟩ := hS
  ext x
  constructor
  · intro hx
    refine ⟨annihilation k j x, ?_⟩
    have h := LinearMap.congr_fun (differential_annihilation_add k S j hj) x
    have hx0 : differential k S x = 0 := hx
    simpa [Module.End.mul_apply, hx0] using h
  · rintro ⟨y, rfl⟩
    change differential k S (differential k S y) = 0
    exact LinearMap.congr_fun (differential_mul_self k S) y

end CharacteristicTwo
end Kourovka2135.SquarefreeOperators
