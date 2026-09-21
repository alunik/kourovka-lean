import Kourovka2135.CentralWordValues
import Kourovka2135.GoodSetObstruction

/-! Transfer of persistent word values through a central extension. The
quotient inputs need only be persistent; the lifted inputs themselves need
not be values. This is the bridge used by the exceptional binary-kernel route. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

theorem OuterWord.commutator_mem_values_of_central_surjection
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) {B : Set Q}
    (hB : ∀ w : OuterWord, B ⊆ w.values Q)
    {a b : G} (ha : f a ∈ B) (hb : f b ∈ B) (w : OuterWord) :
    paperCommutator a b ∈ w.values G := by
  cases w with
  | leaf => simp
  | bracket left right =>
    have hleft : f a ∈ f '' left.values G := by
      rw [left.image_values_eq f hf]
      exact hB left ha
    have hright : f b ∈ f '' right.values G := by
      rw [right.image_values_eq f hf]
      exact hB right hb
    obtain ⟨a', ha', haa⟩ := hleft
    obtain ⟨b', hb', hbb⟩ := hright
    exact (mem_values_bracket left right _).mpr
      ⟨a', ha', b', hb', paperCommutator_eq_of_central_kernel f hker haa hbb⟩

theorem OrderMinimalException.no_coprime_persistent_central_commutator
    [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) {B : Set Q}
    (hB : ∀ v : OuterWord, B ⊆ v.values Q)
    {a b : G} (ha : f a ∈ B) (hb : f b ∈ B)
    (hne : paperCommutator a b ≠ 1)
    (hyp : ¬ p ∣ orderOf (paperCommutator a b)) : False := by
  apply hne
  exact h.derivedValue_eq_one_of_coprime hp hnoncentral le_rfl
    (OuterWord.commutator_mem_values_of_central_surjection f hf hker hB ha hb
      (OuterWord.derivedWord w.height)) hyp

end Kourovka2135
