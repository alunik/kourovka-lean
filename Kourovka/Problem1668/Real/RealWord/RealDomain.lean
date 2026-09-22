import RealWord.Trace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace RealWord

open scoped MatrixGroups

private theorem additive_comm_nonneg (a b c d e f g h : ℝ)
    (hdet : a * d - b * c = 1) (htrace : (a + d) ^ 2 ≤ 4) :
    0 ≤ (b * g - c * f) ^ 2 +
      ((a - d) * f - b * (e - h)) * (c * (e - h) - (a - d) * g) := by
  let δ := a - d
  let k := b * g - c * f
  let m := δ * f - b * (e - h)
  let l := c * (e - h) - δ * g
  change 0 ≤ k ^ 2 + m * l
  have hlin : δ * k + b * l + c * m = 0 := by dsimp [δ, k, m, l]; ring
  have hdis : δ ^ 2 + 4 * b * c = (a + d) ^ 2 - 4 := by
    dsimp [δ]
    linear_combination -4 * hdet
  by_cases hb : b = 0
  · have hd : δ = 0 := by
      rw [hb] at hdis
      nlinarith [sq_nonneg δ]
    have hm : m = 0 := by simp [m, hb, hd]
    simpa [hm] using sq_nonneg k
  · have hid : 4 * b ^ 2 * (k ^ 2 + m * l) =
        (2 * b * k - δ * m) ^ 2 - ((a + d) ^ 2 - 4) * m ^ 2 := by
      linear_combination 4 * b * m * hlin - m ^ 2 * hdis
    have hneg : ((a + d) ^ 2 - 4) * m ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htrace) (sq_nonneg m)
    have hprod : 0 ≤ 4 * b ^ 2 * (k ^ 2 + m * l) := by
      rw [hid]
      exact sub_nonneg.mpr (le_trans hneg (sq_nonneg _))
    have hbpos : 0 < 4 * b ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hb)
    by_contra hn
    have hh := mul_neg_of_pos_of_neg hbpos (lt_of_not_ge hn)
    exact (not_lt_of_ge hprod) hh

/-- The commutator parameter is nonnegative when the first trace has square at most four.
The proof includes parabolic and central matrices without division by an entry. -/
theorem comm_trace_nonneg_of_sq_le_four (A B : SL(2, ℝ))
    (htrace : tr A ^ 2 ≤ 4) : 0 ≤ tr (comm A B) - 2 := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.prop
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.prop
  have hq : tr (comm A B) - 2 =
      (A 0 1 * B 1 0 - A 1 0 * B 0 1) ^ 2 +
      ((A 0 0 - A 1 1) * B 0 1 - A 0 1 * (B 0 0 - B 1 1)) *
        (A 1 0 * (B 0 0 - B 1 1) - (A 0 0 - A 1 1) * B 1 0) := by
    rw [tr_fricke]
    simp only [tr_entries, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination
      (4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) - (B 0 0 + B 1 1) ^ 2) * hA +
      (4 - (A 0 0 + A 1 1) ^ 2) * hB
  rw [hq]
  exact additive_comm_nonneg _ _ _ _ _ _ _ _ hA (by simpa [tr_entries] using htrace)

/-- The product trace of the conjugate pair, in terms of the original commutator. -/
theorem tr_conjugate_product (A B : SL(2, ℝ)) :
    tr (A * (B * A * B⁻¹)) = tr A ^ 2 - (tr (comm A B) - 2) - 2 := by
  have ht := tr_skein A (B * A * B⁻¹)
  have hc : A * (B * A * B⁻¹)⁻¹ = comm A B := by simp [comm, mul_assoc]
  rw [hc, tr_conj] at ht
  linear_combination ht

/-- Every actual real pair lies in the domain of the trace-polynomial inequality. -/
theorem real_domain (A B : SL(2, ℝ)) :
    tr (A * (B * A * B⁻¹)) ≤ tr A ^ 2 - 2 ∨ 4 < tr A ^ 2 := by
  by_cases h : tr A ^ 2 ≤ 4
  · left
    rw [tr_conjugate_product]
    linarith [comm_trace_nonneg_of_sq_le_four A B h]
  · exact Or.inr (lt_of_not_ge h)

end RealWord
