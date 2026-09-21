import Kourovka2135.CoprimeFiber
import Kourovka2135.GoodSetEquiv

/-! The flexible invariant for binary Frattini induction: one generating good
set over an allowed quotient set, containing at least one odd-order element.
The set can contain even-order elements after a full inverse-image step.
-/

set_option autoImplicit false

namespace Kourovka2135

universe u v w
variable {G : Type u} {S : Type v} {H : Type w}
variable [Group G] [Group S] [Group H]

def HasOddGeneratingGoodSetOver (q : G →* S) (B : Set S) : Prop :=
  ∃ Y : Set G, IsGeneratingGoodSet Y ∧ Y ⊆ q ⁻¹' B ∧
    ∃ y ∈ Y, Odd (orderOf y)

/-- The invariant supplies an actual odd-order single value of every outer word. -/
theorem HasOddGeneratingGoodSetOver.exists_value
    {q : G →* S} {B : Set S} (h : HasOddGeneratingGoodSetOver q B)
    (w : OuterWord) : ∃ y ∈ w.values G, q y ∈ B ∧ Odd (orderOf y) := by
  obtain ⟨Y, hY, hsub, y, hy, hodd⟩ := h
  exact ⟨y, hY.subset_values w hy, hsub hy, hodd⟩

/-- A full inverse image that is generating-good preserves the invariant.
The odd element is selected inside that whole inverse image by the proved
coprime-order lift; no closure of word values under powers is used. -/
theorem HasOddGeneratingGoodSetOver.lift [Finite H]
    (pi : H →* G) (hpi : Function.Surjective pi)
    {q : G →* S} {B : Set S} (h : HasOddGeneratingGoodSetOver q B)
    (hfull : ∀ Y : Set G, IsGeneratingGoodSet Y → Y ⊆ q ⁻¹' B →
      IsGeneratingGoodSet (pi ⁻¹' Y)) :
    HasOddGeneratingGoodSetOver (q.comp pi) B := by
  obtain ⟨Y, hY, hsub, y, hy, hodd⟩ := h
  obtain ⟨x, hx, hxodd⟩ := exists_coprime_order_lift_of_surjective
    Nat.prime_two pi hpi y hodd.not_two_dvd_nat
  refine ⟨pi ⁻¹' Y, hfull Y hY hsub, ?_, x, ?_, ?_⟩
  · intro z hz
    exact hsub hz
  · change pi x ∈ Y
    rw [hx]
    exact hy
  · exact Nat.not_even_iff_odd.mp (fun heven => hxodd (even_iff_two_dvd.mp heven))

/-- Transport of the whole invariant along an actual group equivalence. -/
theorem HasOddGeneratingGoodSetOver.of_equiv
    (e : H ≃* G) {q : G →* S} {B : Set S}
    (h : HasOddGeneratingGoodSetOver q B) :
    HasOddGeneratingGoodSetOver (q.comp e.toMonoidHom) B := by
  obtain ⟨Y, hY, hsub, y, hy, hodd⟩ := h
  refine ⟨e ⁻¹' Y, hY.preimage_of_bijective e.toMonoidHom e.bijective, ?_,
    e.symm y, ?_, ?_⟩
  · intro x hx
    exact hsub hx
  · simpa only [Set.mem_preimage, e.apply_symm_apply] using hy
  · simpa only [e.symm.orderOf_eq] using hodd

end Kourovka2135
