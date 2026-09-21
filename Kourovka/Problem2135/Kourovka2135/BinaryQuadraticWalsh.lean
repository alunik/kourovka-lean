import Kourovka2135.BinaryFourier
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The exact integer character-sum identity for a binary quadratic form. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open scoped BigOperators
open Classical
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

noncomputable def walsh (q : V → ZMod 2) : ℤ := ∑ x, sign (q x)

theorem quadratic_sign_shift (q : QuadraticForm (ZMod 2) V) (x h : V) :
    sign (q x) * sign (q (x + h)) = sign (q h) * sign (q.polarBilin h x) := by
  have hq : q (x + h) = q x + q h + q.polarBilin h x := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [add_comm h x]
    ring
  rw [hq, sign_add, sign_add]
  calc
    _ = sign (q x) ^ 2 * (sign (q h) * sign (q.polarBilin h x)) := by ring
    _ = _ := by rw [sign_sq, one_mul]

theorem walsh_sq_sum_radical (q : QuadraticForm (ZMod 2) V) :
    walsh q ^ 2 = (Fintype.card V : ℤ) *
      ∑ h : V, if q.polarBilin h = 0 then sign (q h) else 0 := by
  classical
  calc
    walsh q ^ 2 = ∑ x : V, ∑ y : V, sign (q x) * sign (q y) := by
      simp only [walsh, pow_two, Finset.sum_mul_sum]
    _ = ∑ x : V, ∑ h : V, sign (q x) * sign (q (x + h)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun h => rfl)).symm
    _ = ∑ h : V, ∑ x : V, sign (q h) * sign (q.polarBilin h x) := by
      simp_rw [quadratic_sign_shift]
      exact Finset.sum_comm
    _ = ∑ h : V, sign (q h) *
        (if q.polarBilin h = 0 then (Fintype.card V : ℤ) else 0) := by
      simp_rw [← Finset.mul_sum, sum_sign_linear]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> ring

/-- Nondegeneracy gives the exact square, including in characteristic two. -/
theorem walsh_sq_of_nondegenerate (q : QuadraticForm (ZMod 2) V)
    (hnd : ∀ h : V, (∀ x : V, q.polarBilin h x = 0) → h = 0) :
    walsh q ^ 2 = Fintype.card V := by
  classical
  have he (h : V) : q.polarBilin h = 0 ↔ h = 0 := by
    constructor
    · intro hh
      exact hnd h (fun x => LinearMap.congr_fun hh x)
    · rintro rfl
      exact map_zero _
  rw [walsh_sq_sum_radical]
  simp [he]

end Kourovka2135.BinaryFourier
