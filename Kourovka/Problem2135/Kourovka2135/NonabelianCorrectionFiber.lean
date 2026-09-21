import Kourovka2135.NonabelianCorrectionAffine
import Kourovka2135.NonabelianCorrectionForms
import Kourovka2135.BinaryCorrectionRadical
import Kourovka2135.BinaryCommonRadical

/-! Full correction fibers for a class-two binary group with nondegenerate
scalar central pairings. Every affine fiber is treated by its actual quadratic map. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N] [Finite N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (commutator N)]
variable [IsElementaryAbelian 2 (Subgroup.center N)]

theorem affineCorrectionQuadratic_surjective
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hL : Function.Surjective (correctionLinearMap 2 D E))
    (hDE : (centerActionLinear 2 D).comp (centerActionLinear 2 E) ≠
      (centerActionLinear 2 E).comp (centerActionLinear 2 D))
    (hB : ∀ ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N)), ell ≠ 0 →
      ∀ x, (∀ y, centerScalarCommutatorForm hC ell x y = 0) → x = 0)
    (b : CorrectionSpace N) :
    Function.Surjective (affineCorrectionQuadratic hC D E hD hE b) := by
  classical
  letI : Fintype (correctionLinearMap 2 D E).ker := Fintype.ofFinite _
  letI : Fintype (Additive (Subgroup.center N)) := Fintype.ofFinite _
  let d := centerActionLinearEquiv D
  let e := centerActionLinearEquiv E
  apply BinaryFourier.quadratic_surjective_of_common_polar_radical
    (affineCorrectionQuadratic hC D E hD hE b) (BinaryCorrection.kernelRadical d e)
    (BinaryCorrection.kernelRadical_ne_top d e hL hDE)
  intro ell hell a
  have hh := BinaryCorrection.radical_iff_mem_kernelRadical
    (centerScalarCommutatorForm hC ell) (centerScalarCommutatorForm_self hC ell)
    (hB ell hell) d e (centerScalarCommutatorForm_invariant hC ell D hD)
    (centerScalarCommutatorForm_invariant hC ell E hE) hL a
  have hb (u v : (correctionLinearMap 2 D E).ker) :
      ell ((affineCorrectionQuadratic hC D E hD hE b).polarBilin u v) =
        BinaryCorrection.polarForm (centerScalarCommutatorForm hC ell) d e u v := by
    rw [affineCorrectionQuadratic_polar]
    change ell (centerCommutatorBilinear hC u.val.1 (centerActionLinear 2 D v.val.2) +
      centerCommutatorBilinear hC (centerActionLinear 2 E v.val.1) u.val.2) = _
    exact map_add ell _ _
  simp_rw [hb]
  exact hh

theorem quotientCorrection_surjective_of_nondegenerate_pairings
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hL : Function.Surjective (correctionLinearMap 2 D E))
    (hDE : (centerActionLinear 2 D).comp (centerActionLinear 2 E) ≠
      (centerActionLinear 2 E).comp (centerActionLinear 2 D))
    (hB : ∀ ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N)), ell ≠ 0 →
      ∀ x, (∀ y, centerScalarCommutatorForm hC ell x y = 0) → x = 0) :
    Function.Surjective (quotientCorrection D E hD hE) := by
  exact quotientCorrection_surjective_of_affine_surjective hC D E hD hE hL
    (affineCorrectionQuadratic_surjective hC D E hD hE hL hDE hB)

theorem automorphismCorrection_full_fiber
    (hC : commutator N ≤ Subgroup.center N) (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (hL : Function.Surjective (correctionLinearMap 2 D E))
    (hDE : (centerActionLinear 2 D).comp (centerActionLinear 2 E) ≠
      (centerActionLinear 2 E).comp (centerActionLinear 2 D))
    (hB : ∀ ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N)), ell ≠ 0 →
      ∀ x, (∀ y, centerScalarCommutatorForm hC ell x y = 0) → x = 0) (n : N) :
    ∃ x y : N, automorphismCorrection D E x y = n := by
  exact automorphismCorrection_surjective_of_quotient D E hD hE
    (quotientCorrection_surjective_of_nondegenerate_pairings hC D E hD hE hL hDE hB) n

end Kourovka2135
