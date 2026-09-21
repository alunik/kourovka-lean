import Kourovka2135.CentralCommutatorPairing
import Mathlib.Algebra.Module.ZMod

/-! The central commutator pairing as a bilinear map over the prime field. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]
variable (hD : commutator G ≤ Subgroup.center G)

def centralCommutatorRightAt (x : G ⧸ Subgroup.center G) :
    (G ⧸ Subgroup.center G) →* commutator G :=
  MonoidHom.mk' (centralCommutatorPairingHom hD x)
    (centralCommutatorPairingHom_mul_right hD x)

variable (p : ℕ) [Fact p.Prime]
variable [IsElementaryAbelian p (G ⧸ Subgroup.center G)]
variable [IsElementaryAbelian p (commutator G)]

def centralCommutatorRightLinear (x : Additive (G ⧸ Subgroup.center G)) :
    Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p] Additive (commutator G) :=
  ((centralCommutatorRightAt hD x.toMul).toAdditive).toZModLinearMap p

def centralCommutatorBilinearMap : Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
    Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p] Additive (commutator G) :=
  AddMonoidHom.toZModLinearMap p {
    toFun := centralCommutatorRightLinear hD p
    map_zero' := by
      apply LinearMap.ext
      intro y
      change centralCommutatorPairingHom hD 1 y.toMul = 1
      exact congrArg (fun f => f y.toMul) (map_one (centralCommutatorPairingHom hD))
    map_add' := by
      intro x z
      apply LinearMap.ext
      intro y
      change centralCommutatorPairingHom hD (x.toMul * z.toMul) y.toMul =
        centralCommutatorPairingHom hD x.toMul y.toMul *
          centralCommutatorPairingHom hD z.toMul y.toMul
      exact congrArg (fun f => f y.toMul) ((centralCommutatorPairingHom hD).map_mul _ _) }

theorem centralCommutatorBilinearMap_self (x : Additive (G ⧸ Subgroup.center G)) :
    centralCommutatorBilinearMap hD p x x = 0 :=
  centralCommutatorPairingHom_self hD x.toMul

theorem centralCommutatorBilinearMap_nondegenerate
    {x : Additive (G ⧸ Subgroup.center G)}
    (h : ∀ y, centralCommutatorBilinearMap hD p x y = 0) : x = 0 := by
  change x.toMul = 1
  apply centralCommutatorPairingHom_nondegenerate hD
  intro y
  exact h (Additive.ofMul y)

end Kourovka2135
