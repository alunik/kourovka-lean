import Kourovka2135.BinaryFourier
import Mathlib.FieldTheory.Finiteness

/-! The parity obstruction behind vector-valued binary bent-map surjectivity. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open scoped BigOperators
open Classical

/-- An even square together with an odd number of signed square roots cannot sum to zero. -/
theorem square_root_sum_ne_zero {I : Type*} [Fintype I] [Zero I]
    (f : I → ℤ) (a : ℤ) (ha : a ≠ 0) (ha2 : (a : ZMod 2) = 0)
    (hcard : (Fintype.card I : ZMod 2) = 0)
    (hzero : f 0 = a ^ 2) (hsq : ∀ i : I, i ≠ 0 → f i ^ 2 = a ^ 2) :
    ∑ i, f i ≠ 0 := by
  intro hsum
  let eps : I → ℤ := fun i => if f i = a then 1 else -1
  have heps (i : I) : (eps i : ZMod 2) = 1 := by
    dsimp [eps]
    split_ifs <;> decide
  have hf (i : I) (hi : i ≠ 0) : f i = a * eps i := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i hi) with hh | hh
    · simp [eps, hh]
    · have hn : f i ≠ a := by intro h; rw [h] at hh; omega
      simp [eps, hn, hh]
  have hsum' : a * (a + ∑ i ∈ Finset.univ.erase (0 : I), eps i) = 0 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ (0 : I))
    rw [hsum, hzero] at hh
    have hr : ∑ i ∈ Finset.univ.erase (0 : I), f i =
        a * ∑ i ∈ Finset.univ.erase (0 : I), eps i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => hf i (Finset.mem_erase.mp hi).1
    rw [hr] at hh
    nlinarith
  have hc := (mul_eq_zero.mp hsum').resolve_left ha
  have hz := congrArg (fun n : ℤ => (n : ZMod 2)) hc
  have hz' : ((Finset.univ.erase (0 : I)).card : ZMod 2) = 0 := by
    simpa only [Int.cast_add, Int.cast_sum, Int.cast_zero, ha2, zero_add, heps,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hz
  have hcount := Finset.card_erase_add_one (s := Finset.univ) (Finset.mem_univ (0 : I))
  have hcount' := congrArg (fun n : ℕ => (n : ZMod 2)) hcount
  simp only [Nat.cast_add, Nat.cast_one, Finset.card_univ, hz', hcard, zero_add] at hcount'
  exact one_ne_zero hcount'

theorem card_cast_two_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [Nontrivial V] : (Fintype.card V : ZMod 2) = 0 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hp : Module.finrank (ZMod 2) V ≠ 0 := ne_of_gt (Module.finrank_pos (R := ZMod 2))
  rw [Nat.cast_pow]
  have ht : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [ht, zero_pow hp]

end Kourovka2135.BinaryFourier
