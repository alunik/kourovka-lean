import Kourovka2135.NonabelianCorrectionQuadratic

/-! Invariance and alternation of the actual scalar central commutator forms. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (commutator N)]
variable [IsElementaryAbelian 2 (Subgroup.center N)]

def centerActionLinearEquiv (D : MulAut N) :
    Additive (N ⧸ Subgroup.center N) ≃ₗ[ZMod 2] Additive (N ⧸ Subgroup.center N) :=
  { centerActionLinear 2 D with
    invFun := fun x => Additive.ofMul
      (((characteristicQuotientAut (Subgroup.center N)) D).symm x.toMul)
    left_inv := fun x => ((characteristicQuotientAut (Subgroup.center N)) D).symm_apply_apply x
    right_inv := fun x => ((characteristicQuotientAut (Subgroup.center N)) D).apply_symm_apply x }

theorem centerCommutatorBilinear_self (hC : commutator N ≤ Subgroup.center N)
    (x : Additive (N ⧸ Subgroup.center N)) : centerCommutatorBilinear hC x x = 0 := by
  change ((Subgroup.inclusion hC).toAdditive.toZModLinearMap 2)
    (centralCommutatorBilinearMap hC 2 x x) = 0
  rw [centralCommutatorBilinearMap_self, map_zero]

theorem centerCommutatorBilinear_invariant (hC : commutator N ≤ Subgroup.center N)
    (D : MulAut N) (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (x y : Additive (N ⧸ Subgroup.center N)) :
    centerCommutatorBilinear hC (centerActionLinearEquiv D x) (centerActionLinearEquiv D y) =
      centerCommutatorBilinear hC x y := by
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

def centerScalarCommutatorForm (hC : commutator N ≤ Subgroup.center N)
    (ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N))) :
    Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2]
      Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2] ZMod 2 :=
  (centerCommutatorBilinear hC).compr₂ ell

theorem centerScalarCommutatorForm_self (hC : commutator N ≤ Subgroup.center N)
    (ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N)))
    (x : Additive (N ⧸ Subgroup.center N)) :
    centerScalarCommutatorForm hC ell x x = 0 := by
  change ell (centerCommutatorBilinear hC x x) = 0
  rw [centerCommutatorBilinear_self, map_zero]

theorem centerScalarCommutatorForm_invariant (hC : commutator N ≤ Subgroup.center N)
    (ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N)))
    (D : MulAut N) (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (x y : Additive (N ⧸ Subgroup.center N)) :
    centerScalarCommutatorForm hC ell (centerActionLinearEquiv D x) (centerActionLinearEquiv D y) =
      centerScalarCommutatorForm hC ell x y := by
  exact congrArg ell (centerCommutatorBilinear_invariant hC D hD x y)

end Kourovka2135
