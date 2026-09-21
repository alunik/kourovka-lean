import Kourovka2135.SuzukiTensorWeightArithmetic
import Kourovka2135.SuzukiPrincipalSeriesSocle
import Kourovka2135.SuzukiPrincipalSeriesZero

/-! Classification by the actual natural Frobenius tensor modules.
An irreducible module embeds in a principal series at a reduced exponent.
At nonzero exponent, exact subset arithmetic supplies an actual proper
simple tensor image, and uniqueness of the socle identifies the module.
At exponent zero, the actual permutation module gives the scalar or the
ovoid augmentation module, realized by the empty or full tensor.

There is no module-classification, finite-dimensionality, or algebraic-
closedness premise. The coefficient field contains the actual Suzuki
parameter field through the displayed ring homomorphism. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiIrreducibleClassification

open SuzukiTorusMovingRank SuzukiTensorNatural
open scoped PiTensorProduct

variable (k : Type) [Field k] [CharP k 2] (m : ℕ) (σ : K m →+* k)

/-- With no tensor factors the genuine group action is the identity. -/
theorem emptyRepresentation (g : G m) :
    representation k m (∅ : Finset (Fin (2 * m + 1))) σ g = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change representation k m (∅ : Finset (Fin (2 * m + 1))) σ g
      (PiTensorProduct.tprod k x) = PiTensorProduct.tprod k x
  rw [representation_tprod]
  congr 1
  funext i
  exact isEmptyElim i

/-- The canonical empty tensor equivalence retains the actual group action. -/
def emptyTrivialEquiv :
    (representation k m (∅ : Finset (Fin (2 * m + 1))) σ).Equiv
      (Representation.trivial k (G m) k) :=
  Representation.Equiv.mk
    (PiTensorProduct.isEmptyEquiv (∅ : Finset (Fin (2 * m + 1)))) (by
      intro g
      apply LinearMap.ext
      intro v
      change (PiTensorProduct.isEmptyEquiv (∅ : Finset (Fin (2 * m + 1))))
          (representation k m ∅ σ g v) =
        (PiTensorProduct.isEmptyEquiv (∅ : Finset (Fin (2 * m + 1)))) v
      rw [emptyRepresentation]
      rfl)

variable {V : Type} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (G m) V) [ρ.IsIrreducible]

/-- Every irreducible representation is equivalent to one of the actual
natural Frobenius tensor modules. This includes the smallest parameter
`m = 0`; the nonzero reduced-character branch is then empty. -/
theorem exists_tensor_equiv :
    ∃ I : Finset (Fin (2 * m + 1)),
      Nonempty (ρ.Equiv (SuzukiTensorNatural.representation k m I σ)) := by
  classical
  obtain ⟨n, hn, j, hj, _⟩ :=
    SuzukiPrincipalSeries.exists_principal_series_embedding m σ ρ
  by_cases hn0 : n = 0
  · subst n
    rcases SuzukiPrincipalSeriesZero.scalar_or_augmentation m σ ρ j hj with hs | ha
    · obtain ⟨e⟩ := hs
      exact ⟨∅, ⟨e.trans (emptyTrivialEquiv k m σ).symm⟩⟩
    · obtain ⟨e⟩ := ha
      exact ⟨SuzukiTensorHighest.fullIndices m,
        ⟨e.trans (SuzukiTensorAugmentation.augmentationEquiv k m σ)⟩⟩
  · obtain ⟨I, hI⟩ := SuzukiTensorWeightArithmetic.exists_subset_weight m n
    let : (SuzukiTensorNatural.representation k m I σ).IsIrreducible :=
      SuzukiTensorFactors.isIrreducible k m I σ
    exact ⟨I, ⟨SuzukiPrincipalSeriesSocle.equivOfProperModel m σ n j hj
      (SuzukiTensorPrincipalSeriesMap.embedding k m σ I n hI)
      (SuzukiTensorPrincipalSeriesMap.embedding_ne_zero k m σ I n hI)
      (SuzukiTensorPrincipalSeriesMap.embedding_range_ne_top k m σ I n hI)
      (Nat.pos_of_ne_zero hn0) hn⟩⟩

include σ ρ in
/-- The same actual equivalence gives the exact tensor dimension. -/
theorem exists_finrank_eq :
    ∃ I : Finset (Fin (2 * m + 1)), Module.finrank k V = 4 ^ I.card := by
  obtain ⟨I, ⟨e⟩⟩ := exists_tensor_equiv k m σ ρ
  exact ⟨I, e.toLinearEquiv.finrank_eq.trans (finrank_tensor k m I)⟩

end Kourovka2135.SuzukiIrreducibleClassification
