import RealWord.RealDomain
import RealWord.Inequality

set_option autoImplicit false

namespace RealWord

open scoped MatrixGroups

/-- The actual real word values satisfy the strict universal trace bound. -/
theorem tr_value_gt_seven_fourths (A B : SL(2, ℝ)) :
    (7 : ℝ) / 4 < tr (value A B) := by
  rw [tr_value]
  exact tracePoly_gt_seven_fourths _ _ (sq_nonneg _) (real_domain A B)

private def witnessA : SL(2, ℝ) := ⟨!![1, 1; 0, 1], by norm_num⟩
private def witnessB : SL(2, ℝ) := ⟨!![1, 0; 2, 1], by norm_num⟩

private theorem witness_trace : tr (value witnessA witnessB) = 6045698 := by
  have hx : tr witnessA = 2 := by
    rw [tr_entries]
    norm_num [witnessA]
  have hy : tr witnessB = 2 := by
    rw [tr_entries]
    norm_num [witnessB]
  have hz : tr (witnessA * witnessB) = 4 := by
    change Matrix.trace (!![(1 : ℝ), 1; 0, 1] * !![1, 0; 2, 1]) = 4
    norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hq : tr (comm witnessA witnessB) - 2 = 4 := by
    rw [tr_fricke, hx, hy, hz]
    norm_num
  have hp : tr (witnessA * (witnessB * witnessA * witnessB⁻¹)) = -2 := by
    rw [tr_conjugate_product, hx, hq]
    norm_num
  rw [tr_value, hx, hp]
  norm_num [tracePoly, hpoly]

/-- The displayed element of the standard free group is nontrivial. -/
theorem word_ne_one : word ≠ 1 := by
  intro hw
  have he := congrArg (FreeGroup.lift ![witnessA, witnessB]) hw
  have hv : value witnessA witnessB = 1 := by
    simpa only [eval_word, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, map_one] using he
  have ht := witness_trace
  rw [hv, tr_one] at ht
  norm_num at ht

/-- The standard quotient map to mathlib's projective special linear group. -/
def project : SL(2, ℝ) →* PSL(2, ℝ) := QuotientGroup.mk' _

/-- Surjectivity of the actual quotient map, with no lifting premise. -/
theorem project_surjective : Function.Surjective project := Quotient.mk_surjective

/-- A lift of the projective element omitted by the word. -/
def targetSL : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by norm_num⟩

@[simp] theorem tr_targetSL : tr targetSL = 0 := by
  rw [tr_entries]
  norm_num [targetSL]

/-- Any lift of the target projective class has zero trace. We only need
scalarity of the quotient kernel, so no classification or choice of sign is used. -/
theorem tr_eq_zero_of_project_eq_target (A : SL(2, ℝ))
    (hA : project A = project targetSL) : tr A = 0 := by
  have hquot : project (A * targetSL⁻¹) = 1 := by
    rw [map_mul, map_inv, hA, mul_inv_cancel]
  have hcenter : A * targetSL⁻¹ ∈ Subgroup.center SL(2, ℝ) :=
    (QuotientGroup.eq_one_iff _).mp hquot
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  calc
    tr A = tr ((A * targetSL⁻¹) * targetSL) := by simp
    _ = 0 := by
      change Matrix.trace
        (((A * targetSL⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
          (targetSL : Matrix (Fin 2) (Fin 2) ℝ)) = 0
      rw [← hr]
      simp [targetSL, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The omitted projective target is not the identity. -/
theorem project_target_ne_one : project targetSL ≠ 1 := by
  intro h
  have hz := tr_eq_zero_of_project_eq_target (1 : SL(2, ℝ)) (by simpa using h.symm)
  norm_num at hz

/-- The omitted projective target is an involution. -/
theorem project_target_sq : project targetSL ^ 2 = 1 := by
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(-1 : ℝ), by norm_num, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [targetSL, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every projective evaluation omits the specified class. -/
theorem word_omits_target (g : Fin 2 → PSL(2, ℝ)) :
    FreeGroup.lift g word ≠ project targetSL := by
  intro hg
  obtain ⟨A, hA⟩ := project_surjective (g 0)
  obtain ⟨B, hB⟩ := project_surjective (g 1)
  have hp : project (value A B) = project targetSL := by
    rw [map_value, hA, hB, ← eval_word]
    exact hg
  have hz := tr_eq_zero_of_project_eq_target (value A B) hp
  have hpos := tr_value_gt_seven_fourths A B
  linarith

/-- The concrete two-variable word map on the standard PSL(2,R) is not surjective. -/
theorem word_not_surjective :
    ¬ Function.Surjective
      (fun g : Fin 2 → PSL(2, ℝ) => FreeGroup.lift g word) := by
  intro hs
  obtain ⟨g, hg⟩ := hs (project targetSL)
  exact word_omits_target g hg

/-- A nontrivial word with nonsurjective word map on PSL(2,R). -/
theorem exists_nontrivial_nonsurjective_word :
    ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
      ¬ Function.Surjective
        (fun g : Fin 2 → PSL(2, ℝ) => FreeGroup.lift g w) :=
  ⟨word, word_ne_one, word_not_surjective⟩

end RealWord
