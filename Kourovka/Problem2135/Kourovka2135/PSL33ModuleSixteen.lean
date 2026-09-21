import Kourovka2135.PSL33SingerSixteenData
import Kourovka2135.QuotientRepresentationCertificate
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual sixteen-dimensional PSL3(3) representation over the concrete
field F16, constructed as a quotient of the genuine144-point permutation
module. All quotient and generator identities are finite certificates;
there is no assumed ATLAS representation or group-presentation theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace Kourovka2135.PSL33ModuleSixteen
open SL33ProjectiveData PSL33SingerSixteenData
open scoped Matrix
abbrev V := Fin 16 → k

private def matrixEquiv {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (hAB : A * B = 1) (hBA : B * A = 1) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one])

private def selectColumns : Matrix (Fin 144) (Fin 16) k :=
  fun i j => if i = minorColumns j then 1 else 0

private theorem quotient_select : quotient * selectColumns = minor := by
  ext i j
  simp [Matrix.mul_apply, selectColumns, minor]

private theorem quotient_surjective : Function.Surjective quotient.mulVecLin := by
  intro v
  refine ⟨(selectColumns * minorInverse).mulVecLin v, ?_⟩
  change quotient *ᵥ ((selectColumns * minorInverse) *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, quotient_select, minor_inverse,
    Matrix.one_mulVec]

private theorem permutation_single (g : Q) (j : Fin 144) :
    PSL33SingerCosetData.representation k g (Pi.single j 1) =
      Pi.single (PSL33SingerCosetData.permutation g j) 1 := by
  funext i
  change (Pi.single j (1 : k) : Fin 144 → k) ((PSL33SingerCosetData.permutation g).symm i) =
    (Pi.single (PSL33SingerCosetData.permutation g j) (1 : k) : Fin 144 → k) i
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

private theorem quotient_action_a (v : Fin 144 → k) :
    quotient.mulVecLin (PSL33SingerCosetData.representation k (PSL33GoodSets.q a) v) =
      leftA.mulVecLin (quotient.mulVecLin v) := by
  have h : quotient.mulVecLin.comp
      (PSL33SingerCosetData.representation k (PSL33GoodSets.q a)) =
      leftA.mulVecLin.comp quotient.mulVecLin := by
    apply (Pi.basisFun k (Fin 144)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    rw [permutation_single, PSL33SingerCosetData.permutation_a]
    funext i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply'] using congrFun (column_a j) i
  exact LinearMap.congr_fun h v

private theorem quotient_action_b (v : Fin 144 → k) :
    quotient.mulVecLin (PSL33SingerCosetData.representation k (PSL33GoodSets.q b) v) =
      leftB.mulVecLin (quotient.mulVecLin v) := by
  have h : quotient.mulVecLin.comp
      (PSL33SingerCosetData.representation k (PSL33GoodSets.q b)) =
      leftB.mulVecLin.comp quotient.mulVecLin := by
    apply (Pi.basisFun k (Fin 144)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply]
    rw [permutation_single, PSL33SingerCosetData.permutation_b]
    funext i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply'] using congrFun (column_b j) i
  exact LinearMap.congr_fun h v

private theorem quotient_generators (g : Q)
    (hg : g ∈ ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q)) :
    ∃ A : V ≃ₗ[k] V, ∀ v,
      quotient.mulVecLin (PSL33SingerCosetData.representation k g v) = A (quotient.mulVecLin v) := by
  rcases (show g = PSL33GoodSets.q a ∨ g = PSL33GoodSets.q b by simpa using hg) with rfl | rfl
  · exact ⟨matrixEquiv leftA leftA leftA_inverse leftA_inverse, quotient_action_a⟩
  · exact ⟨matrixEquiv leftB leftBInv leftB_inverse.1 leftB_inverse.2, quotient_action_b⟩

/-- The quotient action of the actual projective special linear group. -/
def representation : Representation k Q V :=
  QuotientRepresentationCertificate.representation (PSL33SingerCosetData.representation k)
    quotient.mulVecLin quotient_surjective {PSL33GoodSets.q a, PSL33GoodSets.q b}
    generating_projective quotient_generators

theorem toMatrix_a : LinearMap.toMatrix' (representation (PSL33GoodSets.q a)) = leftA := by
  have h : representation (PSL33GoodSets.q a) = leftA.mulVecLin :=
    QuotientRepresentationCertificate.representation_eq_of_intertwines _ _ quotient_surjective _
      generating_projective quotient_generators _ _ quotient_action_a
  rw [h]
  exact LinearMap.toMatrix'_toLin' leftA

theorem toMatrix_b : LinearMap.toMatrix' (representation (PSL33GoodSets.q b)) = leftB := by
  have h : representation (PSL33GoodSets.q b) = leftB.mulVecLin :=
    QuotientRepresentationCertificate.representation_eq_of_intertwines _ _ quotient_surjective _
      generating_projective quotient_generators _ _ quotient_action_b
  rw [h]
  exact LinearMap.toMatrix'_toLin' leftB

theorem finrank_eq_sixteen : Module.finrank k V = 16 := by simp [V]

end Kourovka2135.PSL33ModuleSixteen
