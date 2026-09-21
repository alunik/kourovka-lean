import Kourovka2135.BinaryCentralKernelElementary
import Kourovka2135.BinaryFourTrivialH2
import Kourovka2135.CentralExtensionDimension
import Kourovka2135.RepresentationGroupEquiv
import Mathlib.FieldTheory.Finiteness

/-! Perfect central binary covers of SL2(4) have kernel of order at most two.
Transfer first proves the kernel elementary abelian; only then does actual
scalar H2 bound its size. No multiplier or cover classification is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryFourCentralKernelBound

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable (hc : R ≤ Subgroup.center G)
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable (e : SLTwo.SL2 F ≃* G ⧸ R) (hcard : Fintype.card F = 4)

omit [Finite G] [Group.IsPerfect G] in
include e hcard in
/-- Scalar H2 transport through the actual simple-quotient model. -/
theorem finrank_H2_le_one :
    Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (G ⧸ R) (ZMod 2))) 2)
      ≤ 1 := by
  let ρ := Representation.trivial (ZMod 2) (G ⧸ R) (ZMod 2)
  have hpull : ρ.comp e.toMonoidHom =
      Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2) := by
    ext g
    rfl
  have h := BinaryFourTrivialH2.finrank_H2_le_one F hcard
  rw [← hpull, RepresentationGroupEquiv.finrank_cohomology_comp ρ e] at h
  exact h

include hR hc e hcard in
/-- The actual central kernel has at most two elements. -/
theorem card_le_two : Nat.card R ≤ 2 := by
  let : IsElementaryAbelian 2 R :=
    BinaryCentralKernelElementary.isElementaryAbelian_of_quotient_equiv R hR hc e
  have hd : Module.finrank (ZMod 2) (Additive R) ≤ 1 :=
    (CentralExtensionDimension.normal_finrank_le_H2 2 R hc).trans
      (finrank_H2_le_one R e hcard)
  let : Fintype (Additive R) := Fintype.ofFinite _
  change Nat.card (Additive R) ≤ 2
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hd

include hR hc e hcard in
/-- Every such kernel is trivial or has exactly two elements. -/
theorem eq_bot_or_card_two : R = ⊥ ∨ Nat.card R = 2 := by
  by_cases hz : R = ⊥
  · exact Or.inl hz
  · have hpos := (Subgroup.one_lt_card_iff_ne_bot R).mpr hz
    have hle := card_le_two R hR hc e hcard
    exact Or.inr (by omega)

end Kourovka2135.BinaryFourCentralKernelBound
