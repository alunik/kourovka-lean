import WordMaps.WordReduction
import WordMaps.WordMatrices

namespace WordMaps

open Matrix

variable {K : Type*} [Field K]

theorem wordBlockProduct_evaluation (bs : List (ℤ × ℤ)) :
    (FreeGroup.lift (wordPolynomialGenerators K)
      (syllableProduct (pairedSyllables bs))).val = (bs.map (wordBlockMatrix K)).prod := by
  induction bs with
  | nil => simp
  | cons p bs ih =>
    simp only [pairedSyllables_cons, syllableProduct_cons, map_mul, map_zpow,
      FreeGroup.lift_apply_of, SpecialLinearGroup.coe_mul, List.map_cons,
      List.prod_cons, wordBlockMatrix_eq, SpecialLinearGroup.coe_mul, ih]
    exact (Matrix.mul_assoc _ _ _).symm

/-- Every nonidentity word is either conjugate to a generator power, or its
evaluation on the two elementary polynomial matrices has nonconstant
trace. -/
theorem word_power_or_nonconstant_trace [CharZero K] (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    (∃ i : Fin 2, ∃ m : ℤ, m ≠ 0 ∧ IsConj w (FreeGroup.of i ^ m)) ∨
      (wordTrace K w).natDegree ≠ 0 := by
  rcases word_conjugate_power_or_blocks w hw with hpow | ⟨bs, hbs, hnz, hc⟩
  · exact Or.inl hpow
  · right
    rw [wordTrace_eq_of_isConj K hc, wordTrace, wordBlockProduct_evaluation]
    exact wordBlockProduct_trace_nonconstant hbs hnz

end WordMaps
