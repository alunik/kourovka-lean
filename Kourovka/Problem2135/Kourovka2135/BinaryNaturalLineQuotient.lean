import Kourovka2135.BinaryNaturalInvariantLine
import Mathlib.GroupTheory.Index

/-! The actual quotient by a native field-line preimage is the additive
parameter field. This proves normality and the exact index without a
cardinality estimate or an abstract identification premise.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryNaturalLineQuotient

open BinaryNaturalInvariantLine
open scoped IsMulCommutative

variable (F : Type) [Field F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable (M : Type*) [Group M]
variable [IsElementaryAbelian 2 (M ⧸ Subgroup.center M)]
variable (e : (Fin 2 → F) ≃ₗ[ZMod 2] Additive (M ⧸ Subgroup.center M))

/-- The actual second native coordinate of the center-quotient image. -/
def secondCoordinate : M →* Multiplicative F where
  toFun m := Multiplicative.ofAdd
    (e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) m)) 1)
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, ofMul_mul, map_add, Pi.add_apply, ofAdd_add]

/-- The line preimage is exactly the actual coordinate kernel. -/
theorem secondCoordinate_ker : (secondCoordinate F M e).ker = centerLinePreimage F M e := by
  ext m
  rfl

/-- Consequently the line preimage is normal in the original kernel group. -/
instance centerLinePreimage_normal : (centerLinePreimage F M e).Normal := by
  rw [← secondCoordinate_ker F M e]
  infer_instance

/-- Every parameter-field coordinate has an actual representative in M. -/
theorem secondCoordinate_surjective : Function.Surjective (secondCoordinate F M e) := by
  intro y
  let v : Fin 2 → F := ![0, Multiplicative.toAdd y]
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (Subgroup.center M) (e v).toMul
  refine ⟨m, ?_⟩
  change Multiplicative.ofAdd
    (e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) m)) 1) = y
  rw [hm]
  change Multiplicative.ofAdd (e.symm (e v) 1) = y
  rw [e.symm_apply_apply]
  rfl

/-- The concrete line-preimage quotient is the additive parameter field. -/
def quotientEquiv : (M ⧸ centerLinePreimage F M e) ≃* Multiplicative F :=
  (QuotientGroup.quotientMulEquivOfEq (secondCoordinate_ker F M e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (secondCoordinate F M e)
      (secondCoordinate_surjective F M e))

@[simp] theorem quotientEquiv_mk (m : M) :
    quotientEquiv F M e (QuotientGroup.mk' (centerLinePreimage F M e) m) =
      secondCoordinate F M e m := rfl

theorem quotient_card : Nat.card (M ⧸ centerLinePreimage F M e) = Nat.card F :=
  Nat.card_congr (quotientEquiv F M e).toEquiv

/-- The index equals the field cardinality, including without a finite-M premise. -/
theorem index_eq_card : (centerLinePreimage F M e).index = Nat.card F := by
  rw [Subgroup.index_eq_card]
  exact quotient_card F M e

end Kourovka2135.BinaryNaturalLineQuotient
