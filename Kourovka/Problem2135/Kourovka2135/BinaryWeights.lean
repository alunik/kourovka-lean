import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! Exact binary torus-weight arithmetic, uniformly in the extension degree.
The congruences compare natural weights directly, so no truncated subtraction
is used to represent a signed weight. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryWeights

open Finset

/-- Reduction of an exponent modulo `f` reduces the corresponding binary power
modulo `2^f - 1`. This identity also holds at `f = 0`. -/
theorem two_pow_modEq_reduced (f n : ℕ) :
    Nat.ModEq (2 ^ f - 1) (2 ^ n) (2 ^ (n % f)) := by
  have h : Nat.ModEq (2 ^ f - 1) (2 ^ f) 1 :=
    Nat.modEq_sub (by
      have hpos : 0 < 2 ^ f := by positivity
      omega)
  calc
    2 ^ n = 2 ^ (n % f) * (2 ^ f) ^ (n / f) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    _ ≡ 2 ^ (n % f) * 1 ^ (n / f) [MOD 2 ^ f - 1] :=
      Nat.ModEq.rfl.mul (h.pow (n / f))
    _ = 2 ^ (n % f) := by simp

/-- A single binary power with index below `f` is strictly below the torus
modulus, provided `f ≥ 2`. -/
theorem two_pow_lt_modulus {f i : ℕ} (hf : 2 ≤ f) (hi : i < f) :
    2 ^ i < 2 ^ f - 1 := by
  have hle : 2 ^ i ≤ 2 ^ (f - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have htwo : 2 ≤ 2 ^ (f - 1) := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2)
      (by omega : 1 ≤ f - 1))
  have heq : 2 ^ f = 2 ^ (f - 1) * 2 := by
    conv_lhs => rw [show f = (f - 1) + 1 by omega]
    rw [pow_succ]
  omega

/-- Every binary subset weight on the indices below `f` is at most `2^f - 1`. -/
theorem subsetWeight_le_modulus {f : ℕ} (I : Finset ℕ)
    (hI : I ⊆ range f) : (∑ i ∈ I, 2 ^ i) ≤ 2 ^ f - 1 := by
  have hlt : (∑ i ∈ I, 2 ^ i) < 2 ^ f :=
    Nat.geomSum_lt (by decide) (fun i hi => mem_range.mp (hI hi))
  omega

/-- A binary subset weight congruent to one reduced binary power has precisely
that singleton as its support. The full-subset case has residue zero. -/
theorem subsetWeight_modEq_pow_iff {f i : ℕ} (hf : 2 ≤ f) (hi : i < f)
    (I : Finset ℕ) (hI : I ⊆ range f) :
    Nat.ModEq (2 ^ f - 1) (∑ j ∈ I, 2 ^ j) (2 ^ i) ↔ I = {i} := by
  constructor
  · intro h
    have hp := two_pow_lt_modulus hf hi
    have hpos : 0 < 2 ^ i := by positivity
    have hle := subsetWeight_le_modulus I hI
    have hlt : (∑ j ∈ I, 2 ^ j) < 2 ^ f - 1 := by
      by_contra hnot
      have heq : (∑ j ∈ I, 2 ^ j) = 2 ^ f - 1 := by omega
      have hz : 0 = 2 ^ i := by
        simpa only [Nat.ModEq, heq, Nat.mod_self, Nat.mod_eq_of_lt hp] using h
      omega
    apply Finset.geomSum_injective (n := 2) (by decide)
    simpa using h.eq_of_lt_of_lt hlt hp
  · rintro rfl
    simpa only [sum_singleton] using (Nat.ModEq.rfl :
      Nat.ModEq (2 ^ f - 1) (2 ^ i) (2 ^ i))

/-- The degree-one torus-weight equation selects the cyclic successor
singleton, for every `f ≥ 2`. -/
theorem subsetWeight_modEq_singleton_iff {f j : ℕ} (hf : 2 ≤ f) (_hj : j < f)
    (I : Finset ℕ) (hI : I ⊆ range f) :
    Nat.ModEq (2 ^ f - 1) (∑ i ∈ I, 2 ^ i) (2 ^ (j + 1)) ↔
      I = {(j + 1) % f} := by
  have hr := Nat.mod_lt (j + 1) (by omega : 0 < f)
  have hp := two_pow_modEq_reduced f (j + 1)
  constructor
  · intro h
    exact (subsetWeight_modEq_pow_iff hf hr I hI).mp (h.trans hp)
  · intro h
    exact ((subsetWeight_modEq_pow_iff hf hr I hI).mpr h).trans hp.symm

/-- Translation modulo `f` is injective on the reduced indices. -/
theorem cyclic_add_injective {f j k : ℕ} (hj : j < f) (hk : k < f) (a : ℕ)
    (h : (j + a) % f = (k + a) % f) : j = k := by
  exact (Nat.ModEq.add_right_cancel' a h).eq_of_lt_of_lt hj hk

/-- The degree-two binary torus-weight equation is necessarily diagonal, and
its target index is the second cyclic successor. -/
theorem two_terms_modEq_singleton_iff {f i j k : ℕ} (hf : 2 ≤ f)
    (hi : i < f) (hj : j < f) (hk : k < f) :
    Nat.ModEq (2 ^ f - 1) (2 ^ i) (2 ^ (j + 1) + 2 ^ (k + 1)) ↔
      j = k ∧ i = (j + 2) % f := by
  have hcarry : 2 ^ (j + 1) + 2 ^ (j + 1) = 2 ^ (j + 2) := by
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    omega
  constructor
  · intro h
    have hjk : j = k := by
      by_contra hne
      let a := (j + 1) % f
      let b := (k + 1) % f
      have ha : a < f := Nat.mod_lt _ (by omega)
      have hb : b < f := Nat.mod_lt _ (by omega)
      have hab : a ≠ b := fun hh => hne (cyclic_add_injective hj hk 1 hh)
      have hpair : Nat.ModEq (2 ^ f - 1) (∑ r ∈ ({a, b} : Finset ℕ), 2 ^ r)
          (2 ^ i) := by
        have hh := h.trans ((two_pow_modEq_reduced f (j + 1)).add
          (two_pow_modEq_reduced f (k + 1)))
        simpa [a, b, Finset.sum_pair hab] using hh.symm
      have hs : ({a, b} : Finset ℕ) = {i} :=
        (subsetWeight_modEq_pow_iff hf hi _ (by
          intro r hr
          simp only [mem_insert, mem_singleton] at hr
          rcases hr with rfl | rfl <;> simpa using ‹_ < f›)).mp hpair
      have hai : a = i := by
        have hh : a ∈ ({a, b} : Finset ℕ) := by simp
        simpa [hs] using hh
      have hbi : b = i := by
        have hh : b ∈ ({a, b} : Finset ℕ) := by simp
        simpa [hs] using hh
      exact hab (hai.trans hbi.symm)
    refine ⟨hjk, ?_⟩
    rw [← hjk, hcarry] at h
    have hh := h.trans (two_pow_modEq_reduced f (j + 2))
    exact Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hh.eq_of_lt_of_lt (two_pow_lt_modulus hf hi)
        (two_pow_lt_modulus hf (Nat.mod_lt _ (by omega))))
  · rintro ⟨rfl, hii⟩
    rw [hcarry, hii]
    exact (two_pow_modEq_reduced f (j + 2)).symm

/-- At degree two the forbidden-index conditions remove every degree-two
natural-factor weight. -/
theorem natural_h2_no_weight_at_two (i j k : Fin 2) (hji : j ≠ i) (_hki : k ≠ i) :
    ¬ Nat.ModEq 3 (2 ^ i.val) (2 ^ (j.val + 1) + 2 ^ (k.val + 1)) := by
  intro h
  have hh := (two_terms_modEq_singleton_iff (by decide : 2 ≤ 2)
    i.isLt j.isLt k.isLt).mp h
  have hij : i.val = j.val := by simpa [Nat.add_mod, Nat.mod_eq_of_lt j.isLt] using hh.2
  exact hji (Fin.ext hij.symm)

/-- In every degree at least three, exactly one ordered pair of permitted
indices has the degree-two natural-factor weight. -/
theorem natural_h2_weight_unique {f : ℕ} (hf : 3 ≤ f) (i : Fin f) :
    ∃! jk : Fin f × Fin f,
      jk.1 ≠ i ∧ jk.2 ≠ i ∧
        Nat.ModEq (2 ^ f - 1) (2 ^ i.val)
          (2 ^ (jk.1.val + 1) + 2 ^ (jk.2.val + 1)) := by
  let j : Fin f := ⟨(i.val + f - 2) % f, Nat.mod_lt _ (by omega)⟩
  have hji : (j.val + 2) % f = i.val := by
    change ((i.val + f - 2) % f + 2) % f = i.val
    calc
      _ = (i.val + f - 2 + 2) % f := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = (i.val + f) % f := by congr 1; omega
      _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
  have hne : j ≠ i := by
    intro heq
    have hcong : Nat.ModEq f (i.val + 2) i.val := by
      rw [heq] at hji
      exact hji.trans (Nat.mod_eq_of_lt i.isLt).symm
    have hdiv : f ∣ 2 := Nat.add_modEq_left_iff.mp hcong
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  refine ⟨(j, j), ⟨hne, hne,
    (two_terms_modEq_singleton_iff (by omega) i.isLt j.isLt j.isLt).mpr
      ⟨rfl, hji.symm⟩⟩, ?_⟩
  intro jk hjk
  have hh := (two_terms_modEq_singleton_iff (by omega : 2 ≤ f)
    i.isLt jk.1.isLt jk.2.isLt).mp hjk.2.2
  have hfirst : jk.1 = j := Fin.ext (cyclic_add_injective jk.1.isLt j.isLt 2
    (hh.2.symm.trans hji.symm))
  have hsecond : jk.2 = j := (Fin.ext hh.1).symm.trans hfirst
  exact Prod.ext hfirst hsecond


/-- Congruence of two single binary powers is exactly equality of the reduced
exponent, when the first exponent is already below `f`. -/
theorem single_power_modEq_iff {f i n : ℕ} (hf : 2 ≤ f) (hi : i < f) :
    Nat.ModEq (2 ^ f - 1) (2 ^ i) (2 ^ n) ↔ i = n % f := by
  constructor
  · intro h
    have hh := h.trans (two_pow_modEq_reduced f n)
    exact Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hh.eq_of_lt_of_lt (two_pow_lt_modulus hf hi)
        (two_pow_lt_modulus hf (Nat.mod_lt _ (by omega))))
  · rintro rfl
    exact (two_pow_modEq_reduced f n).symm

/-- The cyclic successor on the binary-weight indices. -/
def cycSucc {f : ℕ} (hf : 2 ≤ f) (j : Fin f) : Fin f :=
  ⟨(j.val + 1) % f, Nat.mod_lt _ (by omega)⟩

/-- Finite-index version of the degree-one support calculation. -/
theorem fin_subsetWeight_modEq_singleton_iff {f : ℕ} (hf : 2 ≤ f)
    (j : Fin f) (I : Finset (Fin f)) :
    Nat.ModEq (2 ^ f - 1) (∑ i ∈ I, 2 ^ i.val) (2 ^ (j.val + 1)) ↔
      I = {cycSucc hf j} := by
  let e : Fin f ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hI : I.map e ⊆ range f := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := mem_map.mp hn
    exact mem_range.mpr i.isLt
  have hh := subsetWeight_modEq_singleton_iff hf j.isLt (I.map e) hI
  simp only [sum_map] at hh
  constructor
  · intro h
    apply map_injective e
    simpa [e, cycSucc] using hh.mp h
  · rintro rfl
    apply hh.mpr
    simp [e, cycSucc]

/-- A singleton support has exactly one permitted degree-one coordinate. -/
theorem natural_h1_weight_unique {f : ℕ} (hf : 2 ≤ f) (i : Fin f) :
    ∃! j : Fin f, j ≠ i ∧
      Nat.ModEq (2 ^ f - 1) (2 ^ i.val) (2 ^ (j.val + 1)) := by
  let j : Fin f := ⟨(i.val + f - 1) % f, Nat.mod_lt _ (by omega)⟩
  have hji : (j.val + 1) % f = i.val := by
    change ((i.val + f - 1) % f + 1) % f = i.val
    calc
      _ = (i.val + f - 1 + 1) % f := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = (i.val + f) % f := by congr 1; omega
      _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
  have hne : j ≠ i := by
    intro heq
    have hcong : Nat.ModEq f (i.val + 1) i.val := by
      rw [heq] at hji
      exact hji.trans (Nat.mod_eq_of_lt i.isLt).symm
    have hdiv : f ∣ 1 := Nat.add_modEq_left_iff.mp hcong
    have := Nat.le_of_dvd (by decide : 0 < 1) hdiv
    omega
  refine ⟨j, ⟨hne, (single_power_modEq_iff hf i.isLt).mpr hji.symm⟩, ?_⟩
  intro k hk
  have hh := (single_power_modEq_iff hf i.isLt).mp hk.2
  exact Fin.ext (cyclic_add_injective k.isLt j.isLt 1 (hh.symm.trans hji.symm))

/-- Exact number of permitted degree-one torus-weight coordinates. -/
theorem natural_h1_weight_card {f : ℕ} (hf : 2 ≤ f) (I : Finset (Fin f)) :
    ((univ : Finset (Fin f)).filter fun j =>
      j ∉ I ∧ Nat.ModEq (2 ^ f - 1)
        (∑ i ∈ I, 2 ^ i.val) (2 ^ (j.val + 1))).card =
      if I.card = 1 then 1 else 0 := by
  by_cases hcard : I.card = 1
  · rw [if_pos hcard]
    obtain ⟨i, rfl⟩ := card_eq_one.mp hcard
    rw [card_eq_one_iff_existsUnique]
    simpa only [mem_filter, mem_univ, true_and, mem_singleton, sum_singleton]
      using natural_h1_weight_unique hf i
  · rw [if_neg hcard, card_eq_zero, filter_eq_empty_iff]
    intro j _ hj
    have hI := (fin_subsetWeight_modEq_singleton_iff hf j I).mp hj.2
    apply hcard
    rw [hI]
    simp

/-- Exact number of permitted degree-two natural-factor weight coordinates:
zero in degree two and one in every larger degree. -/
theorem natural_h2_weight_card {f : ℕ} (hf : 2 ≤ f) (i : Fin f) :
    ((univ : Finset (Fin f × Fin f)).filter fun jk =>
      jk.1 ≠ i ∧ jk.2 ≠ i ∧
        Nat.ModEq (2 ^ f - 1) (2 ^ i.val)
          (2 ^ (jk.1.val + 1) + 2 ^ (jk.2.val + 1))).card =
      if f = 2 then 0 else 1 := by
  by_cases hf2 : f = 2
  · subst f
    rw [if_pos rfl, card_eq_zero, filter_eq_empty_iff]
    intro jk _ hjk
    exact natural_h2_no_weight_at_two i jk.1 jk.2 hjk.1 hjk.2.1 hjk.2.2
  · rw [if_neg hf2, card_eq_one_iff_existsUnique]
    simpa only [mem_filter, mem_univ, true_and] using
      natural_h2_weight_unique (by omega : 3 ≤ f) i

end Kourovka2135.BinaryWeights
