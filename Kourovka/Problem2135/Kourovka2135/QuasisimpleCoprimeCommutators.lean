import Kourovka2135.CentralWordValues
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple

/-!
The additional, explicit mathematical hypothesis used here says that every
center-coprime element of every finite quasisimple group is one commutator.
It is a proposition supplied to the theorems, not an axiom declaration.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135

/-- The quasisimple coprime commutator hypothesis, with the actual central
quotient and the actual center cardinality. -/
def QuasisimpleCoprimeCommutators : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Group.IsPerfect G]
    [IsSimpleGroup (G ⧸ Subgroup.center G)],
    ¬ IsMulCommutative (G ⧸ Subgroup.center G) →
    ∀ x : G, Nat.Coprime (orderOf x) (Nat.card (Subgroup.center G)) →
      ∃ a b : G, paperCommutator a b = x

namespace QuasisimpleCoprimeCommutators

variable {G Q : Type u} [Group G] [Group Q]

/-- Elementary perfectness of a nonabelian simple group. -/
theorem isPerfect_of_simple [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) :
    Group.IsPerfect G := by
  apply Group.isPerfect_def.mpr
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with h | h
  · exact (hna ((commutator_eq_bot_iff G).mp h)).elim
  · exact h

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
  · exact h
  · exact (hna (Subgroup.center_eq_top_iff.mp h)).elim

/-- In particular the hypothesis includes Ore's theorem for finite nonabelian
simple groups. -/
theorem commutatorSurjective_of_simple (h : QuasisimpleCoprimeCommutators.{u})
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) :
    CommutatorSurjective G := by
  let : Group.IsPerfect G := isPerfect_of_simple hna
  have hc := center_eq_bot_of_simple hna
  let e : (G ⧸ Subgroup.center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := e.isSimpleGroup
  intro x
  apply h G (Group.IsPerfect.not_isMulCommutative _) x
  rw [hc, Subgroup.card_bot]
  exact Nat.coprime_one_right _

/-- A central surjection onto a nonabelian simple group has precisely the
center as its kernel. -/
theorem ker_eq_center_of_simple [IsSimpleGroup Q]
    (hna : ¬ IsMulCommutative Q) (f : G →* Q) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center G) : f.ker = Subgroup.center G := by
  apply le_antisymm hc
  intro z hz
  have hzQ : f z ∈ Subgroup.center Q :=
    Subgroup.map_center_le_center hf ⟨z, hz, rfl⟩
  rw [center_eq_bot_of_simple hna] at hzQ
  exact hzQ

/-- Every element of order prime to p in a perfect central p-extension of a
finite nonabelian simple group is a single value of every outer word. -/
theorem mem_values_of_central_p_extension
    (h : QuasisimpleCoprimeCommutators.{u}) [Finite G] [Finite Q]
    [Group.IsPerfect G] [IsSimpleGroup Q]
    (hna : ¬ IsMulCommutative Q) (f : G →* Q) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime)
    (hker : IsPGroup p f.ker) (w : OuterWord) {x : G}
    (hx : ¬ p ∣ orderOf x) : x ∈ w.values G := by
  let : Fact p.Prime := ⟨hp⟩
  have hk := ker_eq_center_of_simple hna f hf hc
  let e : (G ⧸ Subgroup.center G) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := e.isSimpleGroup
  have hcop : Nat.Coprime (orderOf x) (Nat.card (Subgroup.center G)) := by
    rw [← hk]
    obtain ⟨k, heq⟩ := hker.exists_card_eq
    rw [heq]
    exact (hp.coprime_iff_not_dvd.mpr hx).symm.pow_right k
  obtain ⟨a, b, hab⟩ := h G (Group.IsPerfect.not_isMulCommutative _) x hcop
  cases w with
  | leaf => exact ⟨x, rfl⟩
  | bracket left right =>
    rw [OuterWord.values_bracket_eq_commutator_of_central_surjection f hf hc
      (h.commutatorSurjective_of_simple hna)]
    exact (OuterWord.mem_values_bracket .leaf .leaf x).mpr
      ⟨a, ⟨a, rfl⟩, b, ⟨b, rfl⟩, hab⟩

end QuasisimpleCoprimeCommutators
end Kourovka2135
