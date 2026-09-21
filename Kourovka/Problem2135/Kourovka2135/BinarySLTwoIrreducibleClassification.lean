import Kourovka2135.SLTwoPrincipalSeriesClassification
import Kourovka2135.SLTwoZeroWeightClassification
import Kourovka2135.SLTwoFullTensorEvaluation

/-! Every irreducible binary SL2 representation is one of the actual
Frobenius tensor modules, over any characteristic-two field containing the
finite parameter field. This is derived from the explicit principal-series
embedding and socles, not supplied as a classification assumption.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.BinarySLTwoIrreducibleClassification

open SLTwoHomogeneousFunctions SLTwoPrincipalSeries
open SLTwoPrincipalSeriesClassification SLTwoZeroWeightClassification

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] [Fintype F] (σ : F →+* k)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V) [ρ.IsIrreducible]

/-- The concrete binary tensor modules exhaust all irreducible representations.
No finite-dimensionality, algebraic closedness, or classification premise occurs. -/
theorem exists_tensor_equiv (f : ℕ) (hcard : Fintype.card F = 2 ^ f) :
    ∃ I : Finset (Fin f), Nonempty (ρ.Equiv (BinaryTensorSLTwo.representation k σ I)) := by
  classical
  obtain ⟨n, hn, j, hj, _⟩ := exists_homogeneous_embedding k σ ρ
  by_cases hn0 : n = 0
  · subst n
    rcases scalar_equiv_or_range_eq_ker k σ ρ j hj with he | hker
    · obtain ⟨e⟩ := he
      exact ⟨∅, ⟨e.trans (SLTwoFullTensorEvaluation.emptyTrivialEquiv k σ f).symm⟩⟩
    · let I : Finset (Fin f) := Finset.univ
      let : (BinaryTensorSLTwo.representation k σ I).IsIrreducible :=
        BinaryTensorSLTwoSimplicity.isIrreducible k I σ hcard
      have hAj : affineIndicator k σ 0 ∈ j.range := by
        change affineIndicator k σ 0 ∈ j.range.toSubmodule
        rw [hker]
        exact augmentation_affineIndicator k σ
      have hAE : affineIndicator k σ 0 ∈
          (SLTwoFullTensorEvaluation.fullEvaluation k σ f hcard).range :=
        ⟨BinaryTensorCoefficient.basis k I Finset.univ,
          SLTwoFullTensorEvaluation.fullEvaluation_top_native k σ f hcard⟩
      exact ⟨I, IrreducibleImageComparison.nonempty_equiv_of_nonzero_common j
        (SLTwoFullTensorEvaluation.fullEvaluation k σ f hcard)
        (affineIndicator k σ 0) (affineIndicator_ne_zero k σ 0) hAj hAE⟩
  · have hnlt : n < 2 ^ f := by
      rw [← hcard]
      omega
    let I := (BinaryExteriorGroupAlgebra.subsetExponentEquiv f).symm ⟨n, hnlt⟩
    have hI : BinaryExteriorGroupAlgebra.subsetWeight f I = n :=
      BinaryExteriorGroupAlgebra.subsetWeight_equiv_symm f ⟨n, hnlt⟩
    exact ⟨I, ⟨equivOfPositiveWeightEq k σ ρ I hcard hI
      (Nat.pos_of_ne_zero hn0) hn j hj⟩⟩

end Kourovka2135.BinarySLTwoIrreducibleClassification
