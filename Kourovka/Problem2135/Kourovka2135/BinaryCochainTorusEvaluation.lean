import Kourovka2135.BinaryCochainTorusGraded

/-! Value-level evaluation of the actual homogeneous diagonal action.
This expresses each cochain value by the coefficient diagonal and the inverse
exponent character, as required for comparison with a semilinear Hom action.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCochainTorusEvaluation

open PeriodicResolution BinaryTensorSubsetBasis BinaryCochainGraded
open scoped IsMulCommutative

variable (k : Type*) [CommRing k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- The coefficient diagonal is divided by the source exponent character. -/
theorem diagonal_apply_value (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (v : DegreeCochains k I n) (a : DegreeIndex (Fin f) n) :
    BinaryCochainTorusGraded.diagonal k I ell c n v a =
      (((BinaryCochainTorus.exponentWeight k c a.val)⁻¹ : kˣ) : k) •
        BinaryTensorTorus.diagonal k I ell c (v a) := by
  have hmap : (Finsupp.lapply a : DegreeCochains k I n →ₗ[k]
        BinaryTensorCoefficient.Carrier k I).comp
        (BinaryCochainTorusGraded.diagonal k I ell c n) =
      (((BinaryCochainTorus.exponentWeight k c a.val)⁻¹ : kˣ) : k) •
        ((BinaryTensorTorus.diagonal k I ell c).toLinearMap.comp (Finsupp.lapply a)) := by
    apply (BinaryCochainTorusGraded.groundBasis k I n).ext
    rintro ⟨b, J⟩
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      BinaryCochainTorusGraded.groundBasis_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe]
    rw [BinaryCochainTorusGraded.diagonal_single_basis, Finsupp.smul_apply]
    by_cases hba : b = a
    · subst b
      simp only [Finsupp.single_eq_same, BinaryTensorTorus.diagonal_basis, smul_smul]
      congr 1
      rw [BinaryCochainTorus.cochainWeight, div_eq_mul_inv, Units.val_mul]
      exact mul_comm _ _
    · simp [Ne.symm hba]
  exact LinearMap.congr_fun hmap v

end Kourovka2135.BinaryCochainTorusEvaluation
