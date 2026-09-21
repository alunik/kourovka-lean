import Kourovka2135.DerivedCorrectionSurjective
import Kourovka2135.NonabelianCorrectionForms
import Kourovka2135.MinimalSymplecticForm
import Kourovka2135.BinaryCorrectionRank
import Kourovka2135.BilinearEmbeddingRank
import Kourovka2135.BinaryQuadraticRank

/-! A full commutator-correction criterion allowing a larger center.
The rank threshold pays the exact extra codimension modulo N'. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N] [Finite N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (N ⧸ commutator N)]
variable [IsElementaryAbelian 2 (commutator N)]

theorem scalarCommutatorForm_invariant_of_center_fixed
    (hC : commutator N ≤ Subgroup.center N)
    (ell : Module.Dual (ZMod 2) (Additive (commutator N)))
    (D : MulAut N) (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (x y : Additive (N ⧸ Subgroup.center N)) :
    scalarCommutatorForm hC 2 ell (centerActionLinearEquiv D x) (centerActionLinearEquiv D y) =
      scalarCommutatorForm hC 2 ell x y := by
  apply congrArg ell
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) y.toMul
  have hxa : x = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) a) := ha.symm
  have hyb : y = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) b) := hb.symm
  rw [hxa, hyb]
  apply Subtype.ext
  change paperCommutator (D a) (D b) = paperCommutator a b
  have hm : paperCommutator (D a) (D b) = D (paperCommutator a b) := by
    simp only [paperCommutator, map_mul, map_inv]
  rw [hm]
  exact hD _ (hC (paperCommutator_mem_commutator a b))

theorem derivedCorrection_kernel_codimension
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hA : Function.Surjective (derivedCorrectionLinear hC D E hD hE)) :
    Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) -
        Module.finrank (ZMod 2) (derivedCorrectionLinear hC D E hD hE).ker =
      Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) := by
  have h := (derivedCorrectionLinear hC D E hD hE).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, Module.finrank_prod] at h
  omega

theorem derivedAffineCorrectionQuadratic_surjective_of_rank
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hA : Function.Surjective (derivedCorrectionLinear hC D E hD hE))
    (hB : ∀ ell : Module.Dual (ZMod 2) (Additive (commutator N)), ell ≠ 0 →
      ∀ x, (∀ y, scalarCommutatorForm hC 2 ell x y = 0) → x = 0)
    (hrank : 2 * Module.finrank (ZMod 2) (Additive (commutator N)) +
      2 * (Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N))) ≤
      Module.finrank (ZMod 2) (BinaryCorrection.operatorCommutator
        (centerActionLinearEquiv D) (centerActionLinearEquiv E)).range)
    (b : CorrectionSpace N) :
    Function.Surjective (derivedAffineCorrectionQuadratic hC D E hD hE b) := by
  classical
  let : Fintype (derivedCorrectionLinear hC D E hD hE).ker := Fintype.ofFinite _
  let : Fintype (Additive (commutator N)) := Fintype.ofFinite _
  have hL : Function.Surjective (correctionLinearMap 2 D E) := by
    rw [← centerProjection_derivedCorrectionLinear hC D E hD hE]
    exact (abelianizationCenterProjection_surjective hC).comp hA
  let d := centerActionLinearEquiv D
  let e := centerActionLinearEquiv E
  let i := Submodule.inclusion (derivedCorrectionLinear_ker_le_center_kernel hC D E hD hE)
  have hi : Function.Injective i := Submodule.inclusion_injective _
  apply BinaryFourier.quadratic_surjective_of_polar_rank
  intro ell hell
  let β := scalarCommutatorForm hC 2 ell
  have hAlt := scalarCommutatorForm_alternating hC 2 ell
  have hβ := hB ell hell
  have hd := scalarCommutatorForm_invariant_of_center_fixed hC ell D hD
  have he := scalarCommutatorForm_invariant_of_center_fixed hC ell E hE
  have hthreshold : 2 * Module.finrank (ZMod 2) (Additive (commutator N)) +
      2 * (Module.finrank (ZMod 2) (BinaryCorrection.linearPart d e).ker -
        Module.finrank (ZMod 2) (derivedCorrectionLinear hC D E hD hE).ker) ≤
        Module.finrank (ZMod 2) (BinaryCorrection.kernelPolarForm β d e).range := by
    rw [BinaryCorrection.linearPart_kernel_finrank d e hL,
      BinaryCorrection.kernelPolarForm_finrank_range_eq β hAlt hβ d e hd he hL,
      derivedCorrection_kernel_codimension hC D E hD hE hA]
    exact hrank
  have hbound := bilinear_embedding_finrank_ge_twice (BinaryCorrection.kernelPolarForm β d e)
    i hi (Module.finrank (ZMod 2) (Additive (commutator N))) hthreshold
  have hpolar : (ell.compQuadraticMap (derivedAffineCorrectionQuadratic hC D E hD hE b)).polarBilin =
      (BinaryCorrection.kernelPolarForm β d e).compl₁₂ i i := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.compQuadraticMap_apply, ← map_sub]
    change ell ((derivedAffineCorrectionQuadratic hC D E hD hE b).polarBilin u v) = _
    rw [derivedAffineCorrectionQuadratic_polar]
    exact map_add ell _ _
  rw [hpolar]
  exact hbound

theorem quotientCorrection_surjective_of_derived_rank
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hA : Function.Surjective (derivedCorrectionLinear hC D E hD hE))
    (hB : ∀ ell : Module.Dual (ZMod 2) (Additive (commutator N)), ell ≠ 0 →
      ∀ x, (∀ y, scalarCommutatorForm hC 2 ell x y = 0) → x = 0)
    (hrank : 2 * Module.finrank (ZMod 2) (Additive (commutator N)) +
      2 * (Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N))) ≤
      Module.finrank (ZMod 2) (BinaryCorrection.operatorCommutator
        (centerActionLinearEquiv D) (centerActionLinearEquiv E)).range) :
    Function.Surjective (quotientCorrection D E hD hE) :=
  quotientCorrection_surjective_of_derivedAffine_surjective hC D E hD hE hA
    (derivedAffineCorrectionQuadratic_surjective_of_rank hC D E hD hE hA hB hrank)

end Kourovka2135
