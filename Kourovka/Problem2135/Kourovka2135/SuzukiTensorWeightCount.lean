import Kourovka2135.SuzukiTensorBaseChange
import Kourovka2135.SuzukiPairWeightFiveBound

/-! Count the actual Frobenius-supported tensor tuples by fixing all but
two factors. Each fiber injects into the proved five-position pair bound;
coincident characters keep their original tuple multiplicity. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorWeightCount

open Finset SuzukiTensorBorelFiltration SuzukiTensorBorelCohomology
open SuzukiPairWeightCollisions SuzukiPairWeightFiveBound
open SuzukiNaturalWeightDifferences
open scoped Classical

variable (m : ℕ) (I : Finset (Fin (2 * m + 1)))

def weight (a : Fin 4) : Residue m := diagonalExponent m a

theorem weight_eq_rev (a : Fin 4) : weight m a = baseWeight m a.rev := by
  fin_cases a <;> simp [weight, diagonalExponent, baseWeight, baseValue, Fin.rev] <;> ring

def totalWeight (a : Index m I) : Residue m :=
  ∑ i : I, (2 : Residue m) ^ i.val.val * weight m (a i)

theorem supported_totalWeight (a : Index m I) (ha : Supported m I a) :
    IsFrobenius m (totalWeight m I a) := by
  obtain ⟨j, hj⟩ := supported_residue m I a ha
  refine ⟨j, ?_⟩
  simpa [totalWeight, tensorExponent, weight] using hj

def remainderSum (i j : I) (a : Index m I) : Residue m :=
  ∑ t ∈ (Finset.univ.erase i).erase j,
    (2 : Residue m) ^ t.val.val * weight m (a t)

theorem totalWeight_split (i j : I) (hij : i ≠ j) (a : Index m I) :
    totalWeight m I a = remainderSum m I i j a +
      (2 : Residue m) ^ i.val.val * weight m (a i) +
      (2 : Residue m) ^ j.val.val * weight m (a j) := by
  classical
  have hi := Finset.sum_erase_add Finset.univ
    (fun t : I => (2 : Residue m) ^ t.val.val * weight m (a t)) (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i)
    (fun t : I => (2 : Residue m) ^ t.val.val * weight m (a t))
    (show j ∈ Finset.univ.erase i by simp [hij.symm])
  change (∑ t : I, (2 : Residue m) ^ t.val.val * weight m (a t)) =
    (∑ t ∈ (Finset.univ.erase i).erase j,
      (2 : Residue m) ^ t.val.val * weight m (a t)) +
      (2 : Residue m) ^ i.val.val * weight m (a i) +
      (2 : Residue m) ^ j.val.val * weight m (a j)
  rw [← hi, ← hj]
  ring

def shift (i j : I) (a : Index m I) : Residue m :=
  (2 : Residue m) ^ ((2 * m + 1) - i.val.val) * remainderSum m I i j a

theorem supported_pair (i j : I) (hij : i.val.val < j.val.val)
    (a : Index m I) (ha : Supported m I a) :
    ((a i).rev, (a j).rev) ∈ selected m (j.val.val - i.val.val) (shift m I i j a) := by
  have hi : i.val.val ≤ 2 * m + 1 := Nat.le_of_lt i.val.isLt
  have hmul : (2 : Residue m) ^ ((2 * m + 1) - i.val.val) * 2 ^ i.val.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hi, two_pow_cycle]
  have hjmul : (2 : Residue m) ^ ((2 * m + 1) - i.val.val) * 2 ^ j.val.val =
      2 ^ (j.val.val - i.val.val) := by
    calc
      _ = (2 : Residue m) ^ ((2 * m + 1) - i.val.val) *
          (2 ^ i.val.val * 2 ^ (j.val.val - i.val.val)) := by
        rw [← pow_add (2 : Residue m) i.val.val (j.val.val - i.val.val),
          Nat.add_sub_of_le (Nat.le_of_lt hij)]
      _ = _ := by rw [← mul_assoc, hmul, one_mul]
  have h := isFrobenius_mul m ((2 * m + 1) - i.val.val)
    (supported_totalWeight m I a ha)
  rw [totalWeight_split m I i j (by intro he; subst j; omega), mul_add, mul_add,
    ← mul_assoc, hmul, one_mul, ← mul_assoc, hjmul] at h
  simpa only [mem_selected, pairValue, shift, weight_eq_rev, add_assoc] using h

abbrev Remaining (i j : I) := {t : I // t ≠ i ∧ t ≠ j}

def restrict (i j : I) (a : Index m I) : Remaining m I i j → Fin 4 := fun t => a t.val

theorem shift_eq_of_restrict_eq (i j : I) (a b : Index m I)
    (h : restrict m I i j a = restrict m I i j b) : shift m I i j a = shift m I i j b := by
  classical
  apply congrArg (fun x : Residue m => (2 : Residue m) ^ ((2 * m + 1) - i.val.val) * x)
  apply Finset.sum_congr rfl
  intro t ht
  have htj : t ≠ j := (Finset.mem_erase.mp ht).1
  have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
  have he := congrFun h (⟨t, hti, htj⟩ : Remaining m I i j)
  change a t = b t at he
  rw [he]

theorem fiber_card_le_five (hm : 2 ≤ m) (i j : I) (hij : i.val.val < j.val.val)
    (r : Remaining m I i j → Fin 4) :
    ((Finset.univ.filter (Supported m I)).filter
      (fun a => restrict m I i j a = r)).card ≤ 5 := by
  classical
  let T := (Finset.univ.filter (Supported m I)).filter
    (fun a => restrict m I i j a = r)
  by_cases hT : T.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hT
    have hbound := pair_bound hm (show 0 < j.val.val - i.val.val by omega)
      (show j.val.val - i.val.val < 2 * m + 1 by have := j.val.isLt; omega)
      (shift m I i j a₀)
    apply (Finset.card_le_card_of_injOn
      (fun a : Index m I => ((a i).rev, (a j).rev)) ?_ ?_).trans hbound
    · intro a ha
      have he : restrict m I i j a = restrict m I i j a₀ :=
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha₀).2.symm
      rw [← shift_eq_of_restrict_eq m I i j a a₀ he]
      exact supported_pair m I i j hij a
        (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    · intro a ha b hb he
      funext t
      by_cases hti : t = i
      · subst t
        exact Fin.rev_injective (congrArg Prod.fst he)
      by_cases htj : t = j
      · subst t
        exact Fin.rev_injective (congrArg Prod.snd he)
      have hr : restrict m I i j a = restrict m I i j b :=
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      exact congrFun hr (⟨t, hti, htj⟩ : Remaining m I i j)
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 5
    simp [hz]

theorem remaining_card (i j : I) (hij : i ≠ j) :
    Fintype.card (Remaining m I i j) = I.card - 2 := by
  classical
  have he : (Finset.univ.filter (fun t : I => t ≠ i ∧ t ≠ j)) =
      (Finset.univ.erase i).erase j := by ext t; simp [and_comm]
  rw [Fintype.card_subtype, he, Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp [Nat.sub_sub]

theorem supportCount_le_of_pair (hm : 2 ≤ m) (i j : I) (hij : i.val.val < j.val.val) :
    supportCount m I ≤ 5 * 4 ^ (I.card - 2) := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise
    (f := restrict m I i j) (s := Finset.univ.filter (Supported m I))
    (t := Finset.univ) (fun a _ => Finset.mem_univ (restrict m I i j a))
  change supportCount m I = _ at hc
  rw [hc]
  calc
    _ ≤ ∑ r : Remaining m I i j → Fin 4, 5 :=
      Finset.sum_le_sum (fun r _ => fiber_card_le_five m I hm i j hij r)
    _ = 5 * 4 ^ (I.card - 2) := by
      simp [remaining_card m I i j (by intro he; subst j; omega), Nat.mul_comm]

/-- Two selected factors suffice; all remaining coordinates retain multiplicity. -/
theorem supportCount_le (hm : 2 ≤ m) (hI : 2 ≤ I.card) :
    supportCount m I ≤ 5 * 4 ^ (I.card - 2) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact supportCount_le_of_pair m I hm ⟨i, hi⟩ ⟨j, hj⟩ hlt
  · exact supportCount_le_of_pair m I hm ⟨j, hj⟩ ⟨i, hi⟩ hgt

theorem finrank_H1_le_five (k : Type) [Field k] [CharP k 2]
    (σ : SuzukiTorusMovingRank.K m →+* k) (hm : 2 ≤ m) (hI : 2 ≤ I.card) :
    Module.finrank k (groupCohomology
      (Rep.of (SuzukiTensorNatural.representation k m I σ)) 1) ≤ 5 * 4 ^ (I.card - 2) :=
  (SuzukiTensorBaseChange.finrank_H1_embedding_le_count k m I σ).trans
    (supportCount_le m I hm hI)

end Kourovka2135.SuzukiTensorWeightCount
