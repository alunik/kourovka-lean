import Kourovka.Problems.P21_03.Proof.CycleCentralizerBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A finite conjugation union bound

This file turns the usual class-sum argument into exact finite cardinality statements.
For two finite sets of permutations, every conjugation hit lies in a union of transporter
sets; every nonempty transporter is a torsor for a centralizer.
-/

open Subgroup Set
open scoped BigOperators

namespace Kourovka213

variable {G : Type*} [Group G]

/-- Elements conjugating `a` to `b`, as a subtype. -/
def Conjugating (a b : G) := {x : G // x * a * x⁻¹ = b}

/-- A nonempty conjugating transporter is a torsor for the centralizer of its source. -/
noncomputable def conjugatingEquivCentralizer (a b : G)
    (h : Nonempty (Conjugating a b)) :
    Conjugating a b ≃ Subgroup.centralizer ({a} : Set G) := by
  let x0 : G := (Classical.choice h).1
  have hx0 : x0 * a * x0⁻¹ = b := (Classical.choice h).2
  exact
    { toFun := fun x => by
        let xv : G := x.1
        have hx : xv * a * xv⁻¹ = b := x.2
        exact ⟨x0⁻¹ * xv, by
          rw [mem_centralizer_singleton_iff]
          calc
            (x0⁻¹ * xv) * a = x0⁻¹ * (xv * a * xv⁻¹) * xv := by group
            _ = x0⁻¹ * b * xv := by rw [hx]
            _ = a * (x0⁻¹ * xv) := by rw [← hx0]; group⟩
      invFun := fun c => ⟨x0 * c.1, by
          have hc : c.1 * a = a * c.1 :=
            mem_centralizer_singleton_iff.mp c.property
          calc
            (x0 * c.1) * a * (x0 * c.1)⁻¹ =
                x0 * (c.1 * a) * c.1⁻¹ * x0⁻¹ := by group
            _ = x0 * (a * c.1) * c.1⁻¹ * x0⁻¹ := by rw [hc]
            _ = b := by rw [← hx0]; group⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun c => by apply Subtype.ext; simp }

section Finite

variable [Fintype G] [DecidableEq G]

/-- Finset version of a conjugating transporter. -/
def conjugatingElements (a b : G) : Finset G :=
  Finset.univ.filter fun x => x * a * x⁻¹ = b

@[simp]
theorem mem_conjugatingElements {a b x : G} :
    x ∈ conjugatingElements a b ↔ x * a * x⁻¹ = b := by
  simp [conjugatingElements]

theorem card_conjugatingElements_eq_centralizer (a b : G) (h : IsConj a b) :
    (conjugatingElements a b).card = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  have hnon : Nonempty (Conjugating a b) := by
    obtain ⟨x, hx⟩ := isConj_iff.mp h
    exact ⟨⟨x, hx⟩⟩
  calc
    (conjugatingElements a b).card = Nat.card (Conjugating a b) := by
      simp [conjugatingElements, Conjugating, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    _ = Nat.card (Subgroup.centralizer ({a} : Set G)) :=
      Nat.card_congr (conjugatingEquivCentralizer a b hnon)

theorem card_conjugatingElements_eq_zero (a b : G) (h : ¬ IsConj a b) :
    (conjugatingElements a b).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  exact h (isConj_iff.mpr ⟨x, mem_conjugatingElements.mp hx⟩)

/-- The union of all transporters from `A` into `B`. -/
def conjugationHits (A B : Finset G) : Finset G :=
  A.biUnion fun a => B.biUnion fun b => conjugatingElements a b

@[simp]
theorem mem_conjugationHits {A B : Finset G} {x : G} :
    x ∈ conjugationHits A B ↔ ∃ a ∈ A, x * a * x⁻¹ ∈ B := by
  simp only [conjugationHits, Finset.mem_biUnion, mem_conjugatingElements]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, hab ▸ hb⟩
  · rintro ⟨a, ha, hxa⟩
    exact ⟨a, ha, x * a * x⁻¹, hxa, rfl⟩

/-- Raw union bound by transporter cardinalities. -/
theorem card_conjugationHits_le_sum (A B : Finset G) :
    (conjugationHits A B).card ≤
      ∑ a ∈ A, ∑ b ∈ B, (conjugatingElements a b).card := by
  unfold conjugationHits
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun a _ => Finset.card_biUnion_le)

/-- Uniform transporter bounds give the familiar product union bound. -/
theorem card_conjugationHits_le_mul (A B : Finset G) (C : ℕ)
    (hC : ∀ a ∈ A, ∀ b ∈ B, (conjugatingElements a b).card ≤ C) :
    (conjugationHits A B).card ≤ A.card * B.card * C := by
  refine (card_conjugationHits_le_sum A B).trans ?_
  calc
    (∑ a ∈ A, ∑ b ∈ B, (conjugatingElements a b).card) ≤
        ∑ _a ∈ A, ∑ _b ∈ B, C := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hC a ha b hb
    _ = A.card * B.card * C := by simp [Nat.mul_assoc]

end Finite

section Perm

variable {n : ℕ}

/-- Orbit--stabilizer, expressed for one permutation transporter. -/
theorem card_isConj_mul_card_conjugatingElements_eq_factorial
    (a b : Equiv.Perm (Fin n)) (h : IsConj a b) :
    Nat.card {g : Equiv.Perm (Fin n) | IsConj a g} *
        (conjugatingElements a b).card = n.factorial := by
  rw [card_conjugatingElements_eq_centralizer a b h,
    Equiv.Perm.nat_card_centralizer]
  simpa only [Fintype.card_fin] using Equiv.Perm.card_isConj_mul_eq a

/-- If the class of `a` has at least `L` elements, each transporter from `a`
has at most `n! / L` elements. -/
theorem card_conjugatingElements_le_factorial_div
    (a b : Equiv.Perm (Fin n)) (L : ℕ) (hL : 0 < L)
    (hclass : L ≤ Nat.card {g : Equiv.Perm (Fin n) | IsConj a g}) :
    (conjugatingElements a b).card ≤ n.factorial / L := by
  by_cases hab : IsConj a b
  · apply (Nat.le_div_iff_mul_le hL).mpr
    calc
      (conjugatingElements a b).card * L ≤
          (conjugatingElements a b).card *
            Nat.card {g : Equiv.Perm (Fin n) | IsConj a g} :=
        Nat.mul_le_mul_left _ hclass
      _ = n.factorial := by
        rw [Nat.mul_comm]
        exact card_isConj_mul_card_conjugatingElements_eq_factorial a b hab
  · rw [card_conjugatingElements_eq_zero a b hab]
    exact Nat.zero_le _

/-- Direct centralizer upper bound in terms of support alone. -/
theorem natCard_centralizer_le_fixedFactorial_mul_supportPowHalf
    (a : Equiv.Perm (Fin n)) :
    Nat.card (Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin n)))) ≤
      (n - a.support.card).factorial * a.support.card ^ (a.support.card / 2) := by
  rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.sum_cycleType]
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_left (n - a.support.card).factorial
      (cycleType_prod_mul_count_factorial_le_support_pow_half a)

/-- The same support-only bound for every transporter, empty or nonempty. -/
theorem card_conjugatingElements_le_fixedFactorial_mul_supportPowHalf
    (a b : Equiv.Perm (Fin n)) :
    (conjugatingElements a b).card ≤
      (n - a.support.card).factorial * a.support.card ^ (a.support.card / 2) := by
  by_cases hab : IsConj a b
  · rw [card_conjugatingElements_eq_centralizer a b hab]
    exact natCard_centralizer_le_fixedFactorial_mul_supportPowHalf a
  · rw [card_conjugatingElements_eq_zero a b hab]
    exact Nat.zero_le _

/-- A support-homogeneous source set gives a uniform transporter union bound. -/
theorem card_conjugationHits_le_of_source_support
    (A B : Finset (Equiv.Perm (Fin n))) (s : ℕ)
    (hA : ∀ a ∈ A, a.support.card = s) :
    (conjugationHits A B).card ≤
      A.card * B.card * ((n - s).factorial * s ^ (s / 2)) := by
  apply card_conjugationHits_le_mul
  intro a ha b _hb
  simpa [hA a ha] using
    card_conjugatingElements_le_fixedFactorial_mul_supportPowHalf a b

end Perm

end Kourovka213
