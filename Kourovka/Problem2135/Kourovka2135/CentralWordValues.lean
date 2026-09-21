import Kourovka2135.RelativeCongruence
import Kourovka2135.Statement

/-!
The elementary word-value bridge for central extensions. Commutator
surjectivity of the quotient is an explicit premise; this file does not prove
Ore's theorem, nor treat it as part of the classification assumption.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- Every element is one ordinary commutator, with the paper convention. -/
def CommutatorSurjective (G : Type u) [Group G] : Prop :=
  ∀ t : G, ∃ a b : G, paperCommutator a b = t

theorem OuterWord.values_eq_univ_of_commutatorSurjective
    (h : CommutatorSurjective G) (w : OuterWord) : w.values G = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  apply OuterWord.subset_values_of_commutator_closed
  intro t _
  obtain ⟨a, b, hab⟩ := h t
  exact ⟨a, Set.mem_univ _, b, Set.mem_univ _, hab⟩

theorem paperCommutator_eq_of_central_kernel (f : G →* Q)
    (hker : f.ker ≤ Subgroup.center G) {a a' b b' : G}
    (ha : f a' = f a) (hb : f b' = f b) :
    paperCommutator a' b' = paperCommutator a b := by
  have hc : a' * a⁻¹ ∈ Subgroup.center G := hker (by
    change f (a' * a⁻¹) = 1
    rw [map_mul, map_inv, ha, mul_inv_cancel])
  have hd : b' * b⁻¹ ∈ Subgroup.center G := hker (by
    change f (b' * b⁻¹) = 1
    rw [map_mul, map_inv, hb, mul_inv_cancel])
  have heq := paperCommutator_mul_of_cross_commute a b (a' * a⁻¹) (b' * b⁻¹)
    (Subgroup.mem_center_iff.mp hc b).symm
    (Subgroup.mem_center_iff.mp hc (b' * b⁻¹)).symm
    (Subgroup.mem_center_iff.mp hd a)
  simpa only [inv_mul_cancel_right] using heq

/-- In a central extension of a group with surjective commutator map, every
nonleaf outer word has exactly the same single values as the ordinary word. -/
theorem OuterWord.values_bracket_eq_commutator_of_central_surjection
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) (hQ : CommutatorSurjective Q)
    (left right : OuterWord) :
    (bracket left right).values G = (bracket leaf leaf).values G := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨a, _, b, _, hab⟩ := (mem_values_bracket left right t).mp ht
    exact (mem_values_bracket leaf leaf t).mpr ⟨a, ⟨a, rfl⟩, b, ⟨b, rfl⟩, hab⟩
  · intro t ht
    obtain ⟨a, _, b, _, hab⟩ := (mem_values_bracket leaf leaf t).mp ht
    have hleft : f a ∈ f '' left.values G := by
      rw [left.image_values_eq f hf, left.values_eq_univ_of_commutatorSurjective hQ]
      trivial
    have hright : f b ∈ f '' right.values G := by
      rw [right.image_values_eq f hf, right.values_eq_univ_of_commutatorSurjective hQ]
      trivial
    obtain ⟨a', ha', ha⟩ := hleft
    obtain ⟨b', hb', hb⟩ := hright
    apply (mem_values_bracket left right t).mpr
    refine ⟨a', ha', b', hb', ?_⟩
    exact (paperCommutator_eq_of_central_kernel f hker ha hb).trans hab

theorem productOrderCondition_bracket_iff_of_central_surjection
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) (hQ : CommutatorSurjective Q)
    (left right : OuterWord) (p : ℕ) :
    ProductOrderCondition (.bracket left right) p G ↔
      ProductOrderCondition (.bracket .leaf .leaf) p G := by
  unfold ProductOrderCondition
  rw [OuterWord.values_bracket_eq_commutator_of_central_surjection f hf hker hQ]

end Kourovka2135
