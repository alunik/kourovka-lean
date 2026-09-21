import Kourovka2135.MinimalException

/-! Any finite counterexample supplies an order-minimal one in the same universe. -/

set_option autoImplicit false
universe u
namespace Kourovka2135

theorem exists_orderMinimalException {G : Type u} [Group G] [Finite G]
    {w : OuterWord} {p : ℕ} (hc : ProductOrderCondition w p G)
    (hf : ¬ HasNormalPComplement p (w.verbalSubgroup G)) :
    ∃ (H : Type u) (groupH : Group H) (finiteH : Finite H),
      @OrderMinimalException w p H groupH finiteH := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hs : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
        ProductOrderCondition w p H → HasNormalPComplement p (w.verbalSubgroup H)
    · exact ⟨G, inferInstance, inferInstance, hc, hf, hs⟩
    · push Not at hs
      obtain ⟨H, groupH, finiteH, hlt, hcH, hfH⟩ := hs
      let : Group H := groupH
      let : Finite H := finiteH
      exact ih (Nat.card H) (hn ▸ hlt) hcH hfH rfl

end Kourovka2135
