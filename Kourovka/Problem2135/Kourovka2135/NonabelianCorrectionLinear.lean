import Kourovka2135.NonabelianCorrection
import Kourovka2135.NormalQuotientRepresentation

/-! The actual linear part of the nonabelian correction map on N/Z(N). -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {N : Type*} [Group N]
variable (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ Subgroup.center N)]

abbrev centerActionLinear (D : MulAut N) :
    Module.End (ZMod p) (Additive (N ⧸ Subgroup.center N)) :=
  (((characteristicQuotientAut (Subgroup.center N)) D).toMonoidHom.toAdditive).toZModLinearMap p

def correctionLinearMap (D E : MulAut N) :
    (Additive (N ⧸ Subgroup.center N) × Additive (N ⧸ Subgroup.center N)) →ₗ[ZMod p]
      Additive (N ⧸ Subgroup.center N) :=
  (centerActionLinear p E - LinearMap.id).comp (LinearMap.fst _ _ _) +
    (LinearMap.id - centerActionLinear p D).comp (LinearMap.snd _ _ _)

theorem quotient_automorphismCorrection (D E : MulAut N) (x y : N) :
    Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (automorphismCorrection D E x y)) =
      correctionLinearMap p D E
        (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x),
         Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y)) := by
  simp only [automorphismCorrection, map_mul, map_inv, ofMul_mul, ofMul_inv]
  change -Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x) +
      -Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (D y)) +
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (E x)) +
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y) =
    (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (E x)) -
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x)) +
    (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) y) -
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (D y)))
  abel

theorem quotient_centerQuotientCorrection (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (x y : Additive (N ⧸ Subgroup.center N)) :
    Additive.ofMul (QuotientGroup.mk' (Subgroup.center N)
      (centerQuotientCorrection D E hD hE x.toMul y.toMul)) =
      correctionLinearMap p D E (x, y) := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) y.toMul
  have hxa : x = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) a) := ha.symm
  have hyb : y = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) b) := hb.symm
  rw [hxa, hyb]
  exact quotient_automorphismCorrection p D E a b

end Kourovka2135
