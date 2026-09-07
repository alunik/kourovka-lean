import Kourovka.Problems.P21_03.Proof.NaturalWreath
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact support size in the natural wreath action

The support of a natural wreath-product element splits over top coordinates.
A moved top coordinate contributes the whole fibre; a fixed coordinate contributes
the support of its base section.
-/

open scoped BigOperators

namespace Kourovka213

universe u v

private def PermWreath.supportSigmaEquiv
    (X Q : Type v) (ι Δ : Type u)
    [Group X] [Group Q] [Fintype ι] [Fintype Δ]
    [DecidableEq ι] [DecidableEq Δ] [MulAction Q ι] [MulAction X Δ]
    (g : PermWreath X Q ι) :
    {p : ι × Δ // p ∈ (PermWreath.naturalToPerm X Q ι Δ g).support} ≃
      Σ i : ι, {d : Δ //
        g.right • i ≠ i ∨ g.left (g.right • i) • d ≠ d} where
  toFun p := ⟨p.1.1, ⟨p.1.2,
    (PermWreath.mem_support_naturalToPerm_iff X Q ι Δ g p.1.1 p.1.2).mp p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1),
    (PermWreath.mem_support_naturalToPerm_iff X Q ι Δ g p.1 p.2.1).mpr p.2.2⟩
  left_inv p := rfl
  right_inv p := rfl

/-- Exact fibrewise formula for support size in the natural wreath action. -/
theorem PermWreath.card_support_naturalToPerm_eq_sum
    (X Q : Type v) (ι Δ : Type u)
    [Group X] [Group Q] [Fintype ι] [Fintype Δ]
    [DecidableEq ι] [DecidableEq Δ] [MulAction Q ι] [MulAction X Δ]
    (g : PermWreath X Q ι) :
    (PermWreath.naturalToPerm X Q ι Δ g).support.card =
      ∑ i : ι, if g.right • i ≠ i then Fintype.card Δ
        else (MulAction.toPermHom X Δ (g.left i)).support.card := by
  classical
  calc
    (PermWreath.naturalToPerm X Q ι Δ g).support.card =
        Fintype.card
          {p : ι × Δ // p ∈ (PermWreath.naturalToPerm X Q ι Δ g).support} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (Σ i : ι, {d : Δ //
          g.right • i ≠ i ∨ g.left (g.right • i) • d ≠ d}) :=
      Fintype.card_congr (PermWreath.supportSigmaEquiv X Q ι Δ g)
    _ = ∑ i : ι, Fintype.card
        {d : Δ // g.right • i ≠ i ∨
          g.left (g.right • i) • d ≠ d} := Fintype.card_sigma
    _ = ∑ i : ι, if g.right • i ≠ i then Fintype.card Δ
        else (MulAction.toPermHom X Δ (g.left i)).support.card := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hmove : g.right • i ≠ i
      · simp [hmove]
      · have hfix : g.right • i = i := not_ne_iff.mp hmove
        rw [if_neg hmove]
        simp only [hfix, false_or]
        rw [Fintype.card_subtype]
        apply congrArg Finset.card
        ext d
        simp [Equiv.Perm.mem_support]

end Kourovka213
