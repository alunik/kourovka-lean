import WordMaps.Assembly
import WordMaps.WordSpecialization
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

open scoped MatrixGroups

namespace WordMaps

/-- Every nonidentity two-variable word is surjective on `PSL₂` over an
algebraically closed field of characteristic zero. -/
theorem word_surjective {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    Function.Surjective (fun g : Fin 2 → PSL(2, K) => FreeGroup.lift g w) := by
  rcases word_power_or_nonconstant_trace (K := K) w hw with
    ⟨i, m, hm, hc⟩ | htrace
  · exact word_surjective_of_isConj hc
      (power_word_surjective i m (psl2_zpow_surjective hm))
  · apply word_surjective_of_curve w
      (FreeGroup.lift (wordPolynomialGenerators K) w) htrace
    intro t
    refine ⟨fun i => sl2Project (evalSL t (wordPolynomialGenerators K i)), ?_⟩
    exact (map_word ((sl2Project (K := K)).comp (evalSL t))
      (wordPolynomialGenerators K) w).symm

/-- The full two-variable word-map surjectivity theorem for `PSL₂(ℂ)`. -/
theorem complex_word_surjective (w : FreeGroup (Fin 2)) (hw : w ≠ 1) :
    Function.Surjective (fun g : Fin 2 → PSL(2, ℂ) => FreeGroup.lift g w) :=
  word_surjective w hw

end WordMaps
