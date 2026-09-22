import WordMaps.Curve
import WordMaps.Conjugacy
import WordMaps.Evaluation

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

namespace WordMaps

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

omit [CharZero K] in
/-- The two noncentral trace-sign classes become one projective conjugacy class. -/
theorem psl2_isConj_of_trace_sign (A B : SL(2, K))
    (hA : A ∉ Subgroup.center SL(2, K)) (hB : B ∉ Subgroup.center SL(2, K))
    (htA : Matrix.trace A.val = 2 ∨ Matrix.trace A.val = -2)
    (htB : Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2) :
    IsConj (sl2Project A) (sl2Project B) := by
  have hAn := mt (sl2_mem_center_iff_scalar A).mpr hA
  have hBn := mt (sl2_mem_center_iff_scalar B).mpr hB
  rcases htA with htA | htA <;> rcases htB with htB | htB
  · exact (sl2Project (K := K)).map_isConj
      (sl2_isConj_of_trace_eq A B hAn hBn (htA.trans htB.symm))
  · have hc := (sl2Project (K := K)).map_isConj
      (sl2_isConj_of_trace_eq A (-B) hAn (sl2_nonscalar_neg B hBn)
        (by simp [htA, htB]))
    simpa using hc
  · have hc := (sl2Project (K := K)).map_isConj
      (sl2_isConj_of_trace_eq A (-B) hAn (sl2_nonscalar_neg B hBn)
        (by simp [htA, htB]))
    simpa using hc
  · exact (sl2Project (K := K)).map_isConj
      (sl2_isConj_of_trace_eq A B hAn hBn (htA.trans htB.symm))

/-- A nonconstant-trace polynomial curve inside a word image forces surjectivity. -/
theorem word_surjective_of_curve {α : Type*} (w : FreeGroup α)
    (M : SL(2, K[X])) (hM : (Matrix.trace M.val).natDegree ≠ 0)
    (himage : ∀ t : K, ∃ g : α → PSL(2, K),
      FreeGroup.lift g w = sl2Project (evalSL t M)) :
    Function.Surjective (fun g : α → PSL(2, K) => FreeGroup.lift g w) := by
  intro b
  obtain ⟨A, rfl⟩ := sl2Project_surjective b
  by_cases hA : A ∈ Subgroup.center SL(2, K)
  · refine ⟨fun _ => 1, ?_⟩
    exact (word_one w).trans ((sl2Project_eq_one_iff A).mpr ((sl2_scalar_iff A).mp ((sl2_mem_center_iff_scalar A).mp hA))).symm
  · by_cases ht : Matrix.trace A.val = 2 ∨ Matrix.trace A.val = -2
    · obtain ⟨t, htM, hnM⟩ := exists_noncentral_trace_two M hM
      exact word_value_of_isConj w
        (psl2_isConj_of_trace_sign (evalSL t M) A hnM hA htM ht) (himage t)
    · push Not at ht
      obtain ⟨t, htr⟩ := IsAlgClosed.eval_surjective hM (Matrix.trace A.val)
      have heq : Matrix.trace (evalSL t M).val = Matrix.trace A.val := by
        simpa only [trace_evalSL] using htr
      have hc := sl2_isConj_of_trace_eq (evalSL t M) A
        (sl2_nonscalar_of_trace_ne _ (heq ▸ ht.1) (heq ▸ ht.2))
        (sl2_nonscalar_of_trace_ne _ ht.1 ht.2) heq
      exact word_value_of_isConj w ((sl2Project (K := K)).map_isConj hc) (himage t)

end WordMaps
