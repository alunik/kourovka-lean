import Kourovka2135.BinaryCyclicIntervals

/-! Even differences of Frobenius powers are ordinary, nonwrapping binary
blocks.  The residue modulo16 of such a block controls the exceptional
Suzuki pair-weight difference graph uniformly in the field exponent. -/

set_option autoImplicit false
namespace Kourovka2135.BinaryEvenIntervals

open BinaryWeights BinaryCyclicIntervals

/-- A positive integer whose ones form one ordinary binary interval. -/
def IsBlock (d : ℕ) : Prop := ∃ a b : ℕ, b < a ∧ d + 2 ^ b = 2 ^ a

private theorem power_mod_two {a : ℕ} (ha : 0 < a) : 2 ^ a % 2 = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simp [pow_succ]

private theorem modEq_below_twice {N x y : ℕ} (hN : 0 < N)
    (hx : x < 2 * N) (hy : y < N) (h : Nat.ModEq N x y) :
    x = y ∨ x = y + N := by
  have hq : x / N < 2 := (Nat.div_lt_iff_lt_mul hN).mpr (by omega)
  have hm : x % N = y := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hy] using h
  have hd := Nat.mod_add_div x N
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq)) with hzero | hone
  · rw [hm, hzero] at hd
    exact Or.inl (by simpa using hd.symm)
  · rw [hm, hone] at hd
    exact Or.inr (by simpa using hd.symm)

/-- A positive even residue of a difference of binary powers is an ordinary
binary block.  The possible cyclic wrap ends exactly at exponent `f`. -/
theorem isBlock_of_even_difference {f a b d : ℕ} (hf : 3 ≤ f)
    (ha : a < f) (hb : b < f) (hd : 0 < d) (hdN : d < 2 ^ f - 1)
    (heven : d % 2 = 0)
    (h : (d : ZMod (2 ^ f - 1)) = 2 ^ a - 2 ^ b) : IsBlock d := by
  have hpa := two_pow_lt_modulus (by omega : 2 ≤ f) ha
  have hpb := two_pow_lt_modulus (by omega : 2 ≤ f) hb
  have hN : 0 < 2 ^ f - 1 := lt_trans hd hdN
  have hcast : ((d + 2 ^ b : ℕ) : ZMod (2 ^ f - 1)) = (2 ^ a : ℕ) := by
    push_cast
    linear_combination h
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  rcases modEq_below_twice hN (by omega) hpa hmod with he | he
  · refine ⟨a, b, ?_, he⟩
    by_contra hba
    have hle : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hbpos : 0 < b := by
      by_contra hh
      have hb0 : b = 0 := by omega
      rw [hb0, pow_zero] at he
      have hapos : 0 < 2 ^ a := by positivity
      omega
    have hpb2 := power_mod_two hbpos
    have hpf2 := power_mod_two (by omega : 0 < f)
    have ha0 : a = 0 := by
      by_contra hne
      have hpa2 := power_mod_two (by omega : 0 < a)
      omega
    refine ⟨f, b, hb, ?_⟩
    rw [ha0, pow_zero] at he
    have hpf : 0 < 2 ^ f := by positivity
    omega

/-- Every binary power is either one of the four small powers or divisible
by16. This is an exponent argument, not a bounded search in `a`. -/
theorem power_mod_sixteen (a : ℕ) :
    2 ^ a = 1 ∨ 2 ^ a = 2 ∨ 2 ^ a = 4 ∨ 2 ^ a = 8 ∨ 2 ^ a % 16 = 0 := by
  by_cases ha : a < 4
  · interval_cases a <;> norm_num
  · right; right; right; right
    have he : 2 ^ a = 16 * 2 ^ (a - 4) := by
      calc
        2 ^ a = 2 ^ (4 + (a - 4)) := by congr 1; omega
        _ = 16 * 2 ^ (a - 4) := by rw [pow_add]; norm_num
    rw [he]
    omega

/-- Residue constraints for a non-small even binary block. The last two
clauses retain the exact power identities needed to rule out `6·2^m`. -/
theorem block_constraints {d : ℕ} (hd : 8 ≤ d) (heven : d % 2 = 0)
    (hblock : IsBlock d) :
    (d % 16 = 0 ∨ d % 16 = 8 ∨ d % 16 = 12 ∨ d % 16 = 14) ∧
      (d % 16 = 12 → ∃ a : ℕ, d + 4 = 2 ^ a) ∧
      (d % 16 = 14 → ∃ a : ℕ, d + 2 = 2 ^ a) := by
  obtain ⟨a, b, _, he⟩ := hblock
  have hbpos : 0 < 2 ^ b := by positivity
  have ha16 : 2 ^ a % 16 = 0 := by
    rcases power_mod_sixteen a with h | h | h | h | h
    all_goals omega
  rcases power_mod_sixteen b with hb | hb | hb | hb | hb
  · omega
  · refine ⟨Or.inr (Or.inr (Or.inr (by omega))), ?_, ?_⟩
    · intro hh; omega
    · intro _; exact ⟨a, by omega⟩
  · refine ⟨Or.inr (Or.inr (Or.inl (by omega))), ?_, ?_⟩
    · intro _; exact ⟨a, by omega⟩
    · intro hh; omega
  · refine ⟨Or.inr (Or.inl (by omega)), ?_, ?_⟩
    · intro hh; omega
    · intro hh; omega
  · refine ⟨Or.inl (by omega), ?_, ?_⟩
    · intro hh; omega
    · intro hh; omega

/-- The coefficient six cannot be absorbed into a binary power. -/
theorem six_mul_power_ne_power (m a : ℕ) : 6 * 2 ^ m ≠ 2 ^ a := by
  intro h
  have hr : 0 < 2 ^ m := by positivity
  have hlo : 2 ^ (m + 2) < 2 ^ a := by
    rw [← h, pow_add]
    norm_num
    omega
  have hhi : 2 ^ a < 2 ^ (m + 3) := by
    rw [← h, pow_add]
    norm_num
    omega
  have helo := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlo
  have hehi := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hhi
  omega

end Kourovka2135.BinaryEvenIntervals
