import Kourovka2135.Vendor.CFSG.ElementaryAbelian
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Module.ZMod

/-! The actual ambient conjugation representation on an elementary abelian
characteristic quotient of a normal subgroup. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

def characteristicQuotientAut (K : Subgroup G) [K.Characteristic] :
    MulAut G →* MulAut (G ⧸ K) where
  toFun a := QuotientGroup.congr K K a
    (Subgroup.characteristic_iff_map_eq.mp inferInstance a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K x
    rfl

def normalQuotientAut (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.Characteristic] : G →* MulAut (N ⧸ K) :=
  (characteristicQuotientAut K).comp MulAut.conjNormal

@[simp]
theorem normalQuotientAut_apply_mk (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.Characteristic] (g : G) (x : N) :
    normalQuotientAut N K g (QuotientGroup.mk' K x) =
      QuotientGroup.mk' K (MulAut.conjNormal g x) := rfl

def normalQuotientRepresentation (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.Characteristic] (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ K)] :
    Representation (ZMod p) G (Additive (N ⧸ K)) where
  toFun g := ((normalQuotientAut N K g).toMonoidHom.toAdditive).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change normalQuotientAut N K 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change normalQuotientAut N K (a * b) x.toMul =
      normalQuotientAut N K a (normalQuotientAut N K b x.toMul)
    rw [map_mul]
    rfl

@[simp]
theorem normalQuotientRepresentation_apply_mk (N : Subgroup G) [N.Normal]
    (K : Subgroup N) [K.Characteristic] (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ K)] (g : G) (x : N) :
    normalQuotientRepresentation N K p g (Additive.ofMul (QuotientGroup.mk' K x)) =
      Additive.ofMul (QuotientGroup.mk' K (MulAut.conjNormal g x)) := rfl

end Kourovka2135
