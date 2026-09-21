import Kourovka2135.SLTwoPrincipalSeriesSocle
import Kourovka2135.SLTwoBorelCharacter
import Kourovka2135.SLTwoHomogeneousEmbedding
import Kourovka2135.IrreducibleImageComparison

/-! Classification of irreducible sources embedded at positive reduced weight.

The comparison returns an actual representation equivalence. The embedding
existence theorem separately constructs the homogeneous-function embedding
of every irreducible representation, including the weight-zero alternative.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SLTwoPrincipalSeriesClassification

open SLTwoHomogeneousFunctions SLTwoPrincipalSeries

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] [Fintype F] (σ : F →+* k)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V) [ρ.IsIrreducible]

/-- Every irreducible representation embeds in an actual homogeneous-function
module with reduced nonnegative weight. -/
theorem exists_homogeneous_embedding :
    ∃ n : ℕ, n < Fintype.card F - 1 ∧
      ∃ j : ρ.IntertwiningMap (representation k σ n), j ≠ 0 ∧ Function.Injective j := by
  have : CharP F 2 := σ.charP σ.injective 2
  let : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (SLTwo.SL2 F)) ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨n, hn, ell, hell, hU, hT⟩ := SLTwoBorelCharacter.exists_borel_character σ ρ
  refine ⟨n, hn, SLTwoHomogeneousEmbedding.embedding k ρ ell σ n hU hT, ?_, ?_⟩
  · exact SLTwoHomogeneousEmbedding.embedding_ne_zero k ρ ell σ n hU hT hell
  · exact SLTwoHomogeneousEmbedding.embedding_injective k ρ ell σ n hU hT hell

/-- A nonzero irreducible source at a positive reduced weight is the concrete
binary tensor module with that weight. -/
def equivOfPositiveWeight {f : ℕ} (I : Finset (Fin f))
    (hcard : Fintype.card F = 2 ^ f)
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I)
    (hnq : BinaryExteriorGroupAlgebra.subsetWeight f I < Fintype.card F - 1)
    (j : ρ.IntertwiningMap (representation k σ (BinaryExteriorGroupAlgebra.subsetWeight f I)))
    (hj : j ≠ 0) : ρ.Equiv (BinaryTensorSLTwo.representation k σ I) := by
  let : (BinaryTensorSLTwo.representation k σ I).IsIrreducible :=
    BinaryTensorSLTwoSimplicity.isIrreducible k I σ hcard
  have hW : j.range.toSubmodule ≠ ⊥ := by
    intro h
    apply hj
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : j v ∈ j.range.toSubmodule := ⟨v, rfl⟩
    rw [h] at hv
    exact hv
  have hle := evaluation_range_le_of_ne_bot k σ I hcard hn hnq
    j.range.toSubmodule hW (fun g _ hv => j.range.apply_mem_toSubmodule g hv)
  have hAE : affineIndicator k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) ∈
      (BinaryTensorSLTwoEvaluation.evaluation k σ I).range :=
    ⟨BinaryTensorCoefficient.basis k I Finset.univ,
      evaluation_top_eq_affineIndicator k σ I hn⟩
  exact IrreducibleImageComparison.equivOfNonzeroCommon j
    (BinaryTensorSLTwoEvaluation.evaluation k σ I)
    (affineIndicator k σ (BinaryExteriorGroupAlgebra.subsetWeight f I))
    (affineIndicator_ne_zero k σ _) (hle hAE) hAE

/-- The same comparison accepts a separately computed binary weight. -/
def equivOfPositiveWeightEq {f : ℕ} (I : Finset (Fin f))
    (hcard : Fintype.card F = 2 ^ f) {n : ℕ}
    (hI : BinaryExteriorGroupAlgebra.subsetWeight f I = n)
    (hn : 0 < n) (hnq : n < Fintype.card F - 1)
    (j : ρ.IntertwiningMap (representation k σ n)) (hj : j ≠ 0) :
    ρ.Equiv (BinaryTensorSLTwo.representation k σ I) := by
  subst n
  exact equivOfPositiveWeight k σ ρ I hcard hn hnq j hj

end Kourovka2135.SLTwoPrincipalSeriesClassification
