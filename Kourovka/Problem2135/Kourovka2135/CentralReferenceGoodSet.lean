import Kourovka2135.CentralDoubleCoverUniqueness
import Kourovka2135.GoodSetImage
import Kourovka2135.BinaryFrattiniFullFiberInduction

/-! A reference perfect central double cover with an actual odd generating
good set supplies the central base for every binary Frattini induction, once
the at-most-two kernel bound has been proved for the quotient. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135

theorem HasOddGeneratingGoodSetOver.quotient_image
    {E Q : Type*} [Group E] [Group Q] (π : E →* Q)
    (hπ : Function.Surjective π) {B : Set Q}
    (h : HasOddGeneratingGoodSetOver π B) :
    HasOddGeneratingGoodSetOver (MonoidHom.id Q) B := by
  obtain ⟨Y, hY, hsub, y, hy, hodd⟩ := h
  refine ⟨π '' Y, hY.image_of_surjective π hπ, ?_, π y, ⟨y, hy, rfl⟩, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hsub hz
  · exact hodd.of_dvd_nat (orderOf_map_dvd π y)

namespace CentralReferenceGoodSet
open CentralDoubleCoverUniqueness BinaryFrattiniFullFiberInduction

theorem centralBase {Q E : Type} [Group Q] [Group E] [Finite E] [Group.IsPerfect E]
    (hbound : KernelBound Q) (π₀ : E →* Q) (hπ₀ : Function.Surjective π₀)
    (hc₀ : π₀.ker ≤ Subgroup.center E) (hcard₀ : Nat.card π₀.ker = 2)
    (B : Set Q) (hgood : HasOddGeneratingGoodSetOver π₀ B) : CentralBase Q B := by
  intro A _ _ _ π hπ hR hc
  have hb := hbound A π hπ hc hR
  by_cases hbot : π.ker = ⊥
  · let e : A ≃* Q := MulEquiv.ofBijective π
      ⟨(MonoidHom.ker_eq_bot_iff π).mp hbot, hπ⟩
    exact (hgood.quotient_image π₀ hπ₀).of_equiv e
  · have hcard : Nat.card π.ker = 2 := by
      have hpos := (Subgroup.one_lt_card_iff_ne_bot π.ker).mpr hbot
      omega
    obtain ⟨e, he⟩ := exists_equiv_over hbound π π₀ hπ hπ₀ hc hc₀ hcard hcard₀
    have hhom : π₀.comp e.toMonoidHom = π := MonoidHom.ext he
    have h := hgood.of_equiv e
    rwa [hhom] at h

end CentralReferenceGoodSet
end Kourovka2135
