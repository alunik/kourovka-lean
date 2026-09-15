import Mathlib.NumberTheory.Height.NumberField
import Mathlib.GroupTheory.OrderOfElement

/-!
# Deep roots in a number field

Northcott finiteness implies that a nonzero element admitting roots of arbitrarily
large powers of a fixed integer has finite multiplicative order.
-/

namespace Kourovka.P21_40

open Height

/-- Deep roots in a fixed number field force an element to be a root of unity. -/
theorem exists_pow_eq_one_of_deep_roots {K : Type*} [Field K] [NumberField K]
    {p : ℕ} (hp : 2 ≤ p) {x : K} (hx : x ≠ 0)
    (hroots : ∀ k : ℕ, ∃ y : K, y ^ (p ^ k) = x) :
    ∃ m : ℕ, 0 < m ∧ x ^ m = 1 := by
  classical
  choose y hy using hroots
  have hy_bound (k : ℕ) : logHeight₁ (y k) ≤ logHeight₁ x := by
    have he : (1 : ℝ) ≤ (p ^ k : ℕ) := by
      exact_mod_cast Nat.one_le_pow k p (by omega)
    calc
      logHeight₁ (y k) ≤ (p ^ k : ℕ) * logHeight₁ (y k) :=
        le_mul_of_one_le_left (zero_le_logHeight₁ _) he
      _ = logHeight₁ x := by rw [← logHeight₁_pow, hy]
  obtain ⟨i, j, hij, hyij⟩ :=
    (NumberField.finite_setOfPred_logHeight₁_le K (logHeight₁ x)).exists_lt_map_eq_of_forall_mem
      hy_bound
  have hyi : y i ≠ 0 := by
    intro h
    have he : p ^ i ≠ 0 := pow_ne_zero _ (by omega)
    have hie := hy i
    rw [h, zero_pow he] at hie
    exact hx hie.symm
  have he : p ^ i < p ^ j := Nat.pow_lt_pow_right (by omega) hij
  have hroot : y i ^ (p ^ j - p ^ i) = 1 := by
    apply mul_right_cancel₀ (pow_ne_zero (p ^ i) hyi)
    rw [← pow_add, Nat.sub_add_cancel he.le, one_mul]
    calc
      y i ^ (p ^ j) = y j ^ (p ^ j) := congrArg (fun z : K => z ^ (p ^ j)) hyij
      _ = x := hy j
      _ = y i ^ (p ^ i) := (hy i).symm
  have hfin : IsOfFinOrder (y i) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨_, Nat.sub_pos_of_lt he, hroot⟩
  have hxfin : IsOfFinOrder x := by
    rw [← hy i]
    exact hfin.pow
  exact hxfin.exists_pow_eq_one

/-- The finite-order formulation of the deep-root lemma. -/
theorem isOfFinOrder_of_deep_roots {K : Type*} [Field K] [NumberField K]
    {p : ℕ} (hp : 2 ≤ p) {x : K} (hx : x ≠ 0)
    (hroots : ∀ k : ℕ, ∃ y : K, y ^ (p ^ k) = x) : IsOfFinOrder x :=
  isOfFinOrder_iff_pow_eq_one.mpr (exists_pow_eq_one_of_deep_roots hp hx hroots)

end Kourovka.P21_40
