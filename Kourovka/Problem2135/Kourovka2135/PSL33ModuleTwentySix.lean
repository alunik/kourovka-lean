import Kourovka2135.PSL33CycleData
import Kourovka2135.SubrepresentationCertificate
import Kourovka2135.QuotientRepresentationCertificate
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! An actual26-dimensional representation of PSL3(3), constructed as a
quotient of an explicitly injected27-dimensional subrepresentation of the
actual52-flag module. Every structural map is certified by finite matrix
identities; no group recognition or module-classification premise occurs. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PSL33ModuleTwentySix
open SL33ProjectiveData PSL33CycleData
open scoped Matrix
abbrev V := Fin 26 → k

private def matrixEquiv {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (hAB : A * B = 1) (hBA : B * A = 1) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one])

private theorem embedding_injective : Function.Injective embedding.mulVecLin := by
  apply Function.LeftInverse.injective (g := leftInverse.mulVecLin)
  intro v
  change leftInverse *ᵥ (embedding *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, leftInverse_embedding, Matrix.one_mulVec]

private theorem embedding_action_a (v : Fin 27 → k) :
    SL33FlagData.representation k (PSL33GoodSets.q a) (embedding.mulVecLin v) =
      embedding.mulVecLin (cycleA.mulVecLin v) := by
  ext i
  rw [SL33FlagData.representation_a]
  change (embedding *ᵥ v) (SL33FlagData.permA.symm i) =
    (embedding *ᵥ (cycleA *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]
  exact congrFun (congrArg (fun M : Matrix (Fin 52) (Fin 27) k => M *ᵥ v) embedding_a) i

private theorem embedding_action_b (v : Fin 27 → k) :
    SL33FlagData.representation k (PSL33GoodSets.q b) (embedding.mulVecLin v) =
      embedding.mulVecLin (cycleB.mulVecLin v) := by
  ext i
  rw [SL33FlagData.representation_b]
  change (embedding *ᵥ v) (SL33FlagData.permB.symm i) =
    (embedding *ᵥ (cycleB *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]
  exact congrFun (congrArg (fun M : Matrix (Fin 52) (Fin 27) k => M *ᵥ v) embedding_b) i

private theorem embedding_generators (g : Q)
    (hg : g ∈ ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q)) :
    ∃ A : (Fin 27 → k) ≃ₗ[k] (Fin 27 → k), ∀ v,
      SL33FlagData.representation k g (embedding.mulVecLin v) = embedding.mulVecLin (A v) := by
  rcases (show g = PSL33GoodSets.q a ∨ g = PSL33GoodSets.q b by simpa using hg) with rfl | rfl
  · exact ⟨matrixEquiv cycleA cycleA cycleA_inverse cycleA_inverse, embedding_action_a⟩
  · exact ⟨matrixEquiv cycleB cycleBInv cycleB_inverse.1 cycleB_inverse.2, embedding_action_b⟩

def cycleRepresentation : Representation k Q (Fin 27 → k) :=
  SubrepresentationCertificate.representation (SL33FlagData.representation k)
    embedding.mulVecLin embedding_injective
    {PSL33GoodSets.q a, PSL33GoodSets.q b} generating_projective embedding_generators

theorem cycleRepresentation_a : cycleRepresentation (PSL33GoodSets.q a) = cycleA.mulVecLin :=
  SubrepresentationCertificate.representation_eq_of_intertwines _ _ embedding_injective _
    generating_projective embedding_generators _ _ embedding_action_a

theorem cycleRepresentation_b : cycleRepresentation (PSL33GoodSets.q b) = cycleB.mulVecLin :=
  SubrepresentationCertificate.representation_eq_of_intertwines _ _ embedding_injective _
    generating_projective embedding_generators _ _ embedding_action_b

private theorem quotient_surjective : Function.Surjective quotient.mulVecLin := by
  intro v
  refine ⟨sectionMatrix.mulVecLin v, ?_⟩
  change quotient *ᵥ (sectionMatrix *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, quotient_section, Matrix.one_mulVec]

private theorem quotient_action_a (v : Fin 27 → k) :
    quotient.mulVecLin (cycleRepresentation (PSL33GoodSets.q a) v) =
      targetA.mulVecLin (quotient.mulVecLin v) := by
  rw [cycleRepresentation_a]
  change quotient *ᵥ (cycleA *ᵥ v) = targetA *ᵥ (quotient *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, quotient_a]

private theorem quotient_action_b (v : Fin 27 → k) :
    quotient.mulVecLin (cycleRepresentation (PSL33GoodSets.q b) v) =
      targetB.mulVecLin (quotient.mulVecLin v) := by
  rw [cycleRepresentation_b]
  change quotient *ᵥ (cycleB *ᵥ v) = targetB *ᵥ (quotient *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, quotient_b]

private theorem quotient_generators (g : Q)
    (hg : g ∈ ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q)) :
    ∃ A : V ≃ₗ[k] V, ∀ v, quotient.mulVecLin (cycleRepresentation g v) = A (quotient.mulVecLin v) := by
  rcases (show g = PSL33GoodSets.q a ∨ g = PSL33GoodSets.q b by simpa using hg) with rfl | rfl
  · exact ⟨matrixEquiv targetA targetA targetA_inverse targetA_inverse, quotient_action_a⟩
  · exact ⟨matrixEquiv targetB targetBInv targetB_inverse.1 targetB_inverse.2, quotient_action_b⟩

/-- Genuine actual-group representation in the certified26 coordinates. -/
def representation : Representation k Q V :=
  QuotientRepresentationCertificate.representation cycleRepresentation quotient.mulVecLin
    quotient_surjective {PSL33GoodSets.q a, PSL33GoodSets.q b}
    generating_projective quotient_generators

theorem toMatrix_a : LinearMap.toMatrix' (representation (PSL33GoodSets.q a)) = targetA := by
  have h : representation (PSL33GoodSets.q a) = targetA.mulVecLin :=
    QuotientRepresentationCertificate.representation_eq_of_intertwines _ _ quotient_surjective _
      generating_projective quotient_generators _ _ quotient_action_a
  rw [h]
  exact LinearMap.toMatrix'_toLin' targetA

theorem toMatrix_b : LinearMap.toMatrix' (representation (PSL33GoodSets.q b)) = targetB := by
  have h : representation (PSL33GoodSets.q b) = targetB.mulVecLin :=
    QuotientRepresentationCertificate.representation_eq_of_intertwines _ _ quotient_surjective _
      generating_projective quotient_generators _ _ quotient_action_b
  rw [h]
  exact LinearMap.toMatrix'_toLin' targetB

theorem finrank_eq_twentySix : Module.finrank k V = 26 := by simp [V]

end Kourovka2135.PSL33ModuleTwentySix
