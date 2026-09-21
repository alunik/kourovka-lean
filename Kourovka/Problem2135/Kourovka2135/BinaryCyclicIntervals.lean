import Kourovka2135.BinaryWeights
import Mathlib.Data.ZMod.Basic

/-! Binary supports modulo `2^f - 1`, including the actual cyclic interval
encoding of a difference of powers.  These lemmas are uniform in `f`; no
finite exponent search is used. -/

set_option autoImplicit false
namespace Kourovka2135.BinaryCyclicIntervals

open Finset BinaryWeights

/-- Ordinary binary subset weight. -/
def weight (I : Finset ℕ) : ℕ := ∑ i ∈ I, 2 ^ i

theorem weight_range (f : ℕ) : weight (range f) = 2 ^ f - 1 := by
  have h : ∀ n : ℕ, weight (range n) + 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => simp [weight]
    | succ n ih =>
      simp only [weight, sum_range_succ, pow_succ] at *
      omega
  have := h f
  omega

theorem weight_Ico_add {a b : ℕ} (hba : b ≤ a) :
    weight (Ico b a) + 2 ^ b = 2 ^ a := by
  have h := sum_range_add_sum_Ico (fun i : ℕ => 2 ^ i) hba
  change weight (range b) + weight (Ico b a) = weight (range a) at h
  rw [weight_range, weight_range] at h
  have hb : 0 < 2 ^ b := by positivity
  have ha : 0 < 2 ^ a := by positivity
  omega

/-- Proper binary supports have weights strictly below the torus modulus. -/
theorem weight_lt_modulus {f : ℕ} {I : Finset ℕ}
    (hI : I ⊆ range f) (hne : I ≠ range f) : weight I < 2 ^ f - 1 := by
  have hle := subsetWeight_le_modulus I hI
  change weight I ≤ 2 ^ f - 1 at hle
  refine lt_of_le_of_ne hle ?_
  intro h
  apply hne
  apply Finset.geomSum_injective (n := 2) (by decide)
  change weight I = weight (range f)
  rw [weight_range]
  exact h

/-- Modulo the torus order, two proper binary supports are equal precisely
when their residues agree. -/
theorem weight_modEq_iff {f : ℕ} {I J : Finset ℕ}
    (hI : I ⊆ range f) (hJ : J ⊆ range f)
    (hI' : I ≠ range f) (hJ' : J ≠ range f) :
    Nat.ModEq (2 ^ f - 1) (weight I) (weight J) ↔ I = J := by
  constructor
  · intro h
    apply Finset.geomSum_injective (n := 2) (by decide)
    exact h.eq_of_lt_of_lt (weight_lt_modulus hI hI') (weight_lt_modulus hJ hJ')
  · rintro rfl
    exact Nat.ModEq.rfl

/-- The cyclic interval from `b` to just before `a`.  Equal endpoints encode
the empty interval, not the full binary cycle. -/
def interval (f a b : ℕ) : Finset ℕ :=
  if b ≤ a then Ico b a else range f \ Ico a b

theorem interval_subset {f a b : ℕ} (ha : a < f) : interval f a b ⊆ range f := by
  intro i hi
  unfold interval at hi
  split_ifs at hi with hba
  · exact mem_range.mpr (lt_trans (mem_Ico.mp hi).2 ha)
  · exact (mem_sdiff.mp hi).1

theorem end_not_mem_interval {f a b : ℕ} : a ∉ interval f a b := by
  unfold interval
  split_ifs with hba
  · simp
  · have hab' : a < b := by omega
    simp [hab']

theorem start_mem_interval {f a b : ℕ} (hb : b < f) (hab : a ≠ b) :
    b ∈ interval f a b := by
  unfold interval
  split_ifs with hba
  · have hba' : b < a := by omega
    simp [hba']
  · simp [hb]

theorem interval_ne_range {f a b : ℕ} (ha : a < f) :
    interval f a b ≠ range f := by
  intro h
  have hh : a ∈ interval f a b := by rw [h]; exact mem_range.mpr ha
  exact end_not_mem_interval hh

/-- The binary interval has exactly the actual modular difference as weight,
including the wraparound case. -/
theorem interval_weight {f a b : ℕ} (_ha : a < f) (hb : b < f) :
    (weight (interval f a b) : ZMod (2 ^ f - 1)) = 2 ^ a - 2 ^ b := by
  unfold interval
  split_ifs with hba
  · have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ f - 1))) (weight_Ico_add hba)
    push_cast at h
    exact eq_sub_of_add_eq h
  · have hab : a ≤ b := by omega
    have hsub : Ico a b ⊆ range f := by
      intro i hi
      exact mem_range.mpr (lt_trans (mem_Ico.mp hi).2 hb)
    have hs := sum_sdiff (f := fun i : ℕ => 2 ^ i) hsub
    change weight (range f \ Ico a b) + weight (Ico a b) = weight (range f) at hs
    rw [weight_range] at hs
    have hs' := congrArg (fun n : ℕ => (n : ZMod (2 ^ f - 1))) hs
    have hi := congrArg (fun n : ℕ => (n : ZMod (2 ^ f - 1))) (weight_Ico_add hab)
    push_cast at hs' hi
    have hn : ((2 ^ f - 1 : ℕ) : ZMod (2 ^ f - 1)) = 0 := by simp
    rw [hn] at hs'
    linear_combination hs' - hi

private theorem pair_subset {f a b : ℕ} (ha : a < f) (hb : b < f) :
    ({a, b} : Finset ℕ) ⊆ range f := by
  intro i hi
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact mem_range.mpr ha
  · exact mem_range.mpr hb

private theorem pair_ne_range {f a b : ℕ} (hf : 3 ≤ f) :
    ({a, b} : Finset ℕ) ≠ range f := by
  intro h
  have hc := congrArg Finset.card h
  have hle : ({a, b} : Finset ℕ).card ≤ 2 := card_le_two
  simp only [card_range] at hc
  omega

/-- A sum of two distinct reduced powers cannot equal one power modulo the
odd binary torus order. -/
theorem pair_not_modEq_single {f a b c : ℕ} (hf : 2 ≤ f)
    (ha : a < f) (hb : b < f) (hc : c < f) (hab : a ≠ b) :
    ¬ Nat.ModEq (2 ^ f - 1) (2 ^ a + 2 ^ b) (2 ^ c) := by
  intro h
  have hs : ({a, b} : Finset ℕ) = {c} :=
    (subsetWeight_modEq_pow_iff hf hc {a, b} (pair_subset ha hb)).mp
      (by simpa only [sum_pair hab] using h)
  have hac : a = c := by
    have : a ∈ ({a, b} : Finset ℕ) := by simp
    simpa only [hs, mem_singleton] using this
  have hbc : b = c := by
    have : b ∈ ({a, b} : Finset ℕ) := by simp
    simpa only [hs, mem_singleton] using this
  exact hab (hac.trans hbc.symm)

/-- Binary powers are a modular Sidon set. Repeated summands are included;
there is no exceptional equality produced by a carry. -/
theorem pair_modEq_iff {f a b c d : ℕ} (hf : 3 ≤ f)
    (ha : a < f) (hb : b < f) (hc : c < f) (hd : d < f) :
    Nat.ModEq (2 ^ f - 1) (2 ^ a + 2 ^ b) (2 ^ c + 2 ^ d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    by_cases hab : a = b
    · subst b
      have hcarry : 2 ^ a + 2 ^ a = 2 ^ (a + 1) := by rw [pow_succ]; omega
      rw [hcarry] at h
      by_cases hcd : c = d
      · subst d
        have hcarry' : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := by rw [pow_succ]; omega
        rw [hcarry'] at h
        have hh := (two_pow_modEq_reduced f (a + 1)).symm.trans
          (h.trans (two_pow_modEq_reduced f (c + 1)))
        have he := Nat.pow_right_injective (by decide : 2 ≤ 2)
          (hh.eq_of_lt_of_lt (two_pow_lt_modulus (by omega) (Nat.mod_lt _ (by omega)))
            (two_pow_lt_modulus (by omega) (Nat.mod_lt _ (by omega))))
        have hac := cyclic_add_injective ha hc 1 he
        exact Or.inl ⟨hac, hac⟩
      · exact False.elim (pair_not_modEq_single (by omega) hc hd
          (Nat.mod_lt _ (by omega)) hcd
          (h.symm.trans (two_pow_modEq_reduced f (a + 1))))
    · by_cases hcd : c = d
      · subst d
        have hcarry : 2 ^ c + 2 ^ c = 2 ^ (c + 1) := by rw [pow_succ]; omega
        rw [hcarry] at h
        exact False.elim (pair_not_modEq_single (by omega) ha hb
          (Nat.mod_lt _ (by omega)) hab
          (h.trans (two_pow_modEq_reduced f (c + 1))))
      · have hs : ({a, b} : Finset ℕ) = {c, d} :=
          (weight_modEq_iff (pair_subset ha hb) (pair_subset hc hd)
            (pair_ne_range hf) (pair_ne_range hf)).mp
              (by simpa only [weight, sum_pair hab, sum_pair hcd] using h)
        have hmem : a = c ∨ a = d := by
          have : a ∈ ({c, d} : Finset ℕ) := by rw [← hs]; simp
          simpa only [mem_insert, mem_singleton] using this
        rcases hmem with hac | had
        · left
          refine ⟨hac, ?_⟩
          have : b ∈ ({c, d} : Finset ℕ) := by rw [← hs]; simp
          simp only [mem_insert, mem_singleton] at this
          rcases this with hbc | hbd
          · exact False.elim (hab (hac.trans hbc.symm))
          · exact hbd
        · right
          refine ⟨had, ?_⟩
          have : b ∈ ({c, d} : Finset ℕ) := by rw [← hs]; simp
          simp only [mem_insert, mem_singleton] at this
          rcases this with hbc | hbd
          · exact hbc
          · exact False.elim (hab (had.trans hbd.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Nat.ModEq.rfl
    · exact congrArg (fun n : ℕ => n % (2^f-1)) (Nat.add_comm _ _)

/-- Every nonzero ordered difference has a unique pair of reduced Frobenius
indices. This is the Sidon property in the form used by the weighted graph. -/
theorem difference_injective {f a b c d : ℕ} (hf : 3 ≤ f)
    (ha : a < f) (hb : b < f) (hc : c < f) (hd : d < f)
    (hab : a ≠ b)
    (h : (2 : ZMod (2 ^ f - 1)) ^ a - 2 ^ b = 2 ^ c - 2 ^ d) :
    a = c ∧ b = d := by
  have hsum : ((2 ^ a + 2 ^ d : ℕ) : ZMod (2 ^ f - 1)) =
      ((2 ^ c + 2 ^ b : ℕ) : ZMod (2 ^ f - 1)) := by
    push_cast
    linear_combination h
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsum
  rcases (pair_modEq_iff hf ha hd hc hb).mp he with hgood | hbad
  · exact ⟨hgood.1, hgood.2.symm⟩
  · exact False.elim (hab hbad.1)

/-- In particular, the actual interval encoding has unique ordered endpoints. -/
theorem interval_injective {f a b c d : ℕ} (hf : 3 ≤ f)
    (ha : a < f) (hb : b < f) (hc : c < f) (hd : d < f)
    (hab : a ≠ b) (h : interval f a b = interval f c d) : a = c ∧ b = d := by
  apply difference_injective hf ha hb hc hd hab
  rw [← interval_weight ha hb, ← interval_weight hc hd, h]

end Kourovka2135.BinaryCyclicIntervals
