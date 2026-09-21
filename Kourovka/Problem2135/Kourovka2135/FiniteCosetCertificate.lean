import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group

/-! A finite right-coset transition certificate bounds the cardinality of
an actual generated group. Only generator transitions and their inverses
are checked. No coset enumeration algorithm or claimed group order is trusted.
-/

set_option autoImplicit false
namespace Kourovka2135.FiniteCosetCertificate

variable {G I : Type*} [Group G]

theorem exists_normalForm (H : Subgroup G) (S : Set G)
    (hS : Subgroup.closure S = ⊤) (r : I → G) (i₀ : I) (hr : r i₀ = 1)
    (step : ∀ i s, s ∈ S → ∃ j, r i * s * (r j)⁻¹ ∈ H)
    (stepInv : ∀ i s, s ∈ S → ∃ j, r i * s⁻¹ * (r j)⁻¹ ∈ H)
    (g : G) : ∃ h : H, ∃ i, g = h.val * r i := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  refine Subgroup.closure_induction_right (p := fun x _ => ∃ h : H, ∃ i, x = h.val * r i)
    ?_ ?_ ?_ hg
  · exact ⟨1, i₀, by simp [hr]⟩
  · rintro x _ s hs ⟨h, i, rfl⟩
    obtain ⟨j, hj⟩ := step i s hs
    refine ⟨h * ⟨r i * s * (r j)⁻¹, hj⟩, j, ?_⟩
    change h.val * r i * s = (h.val * (r i * s * (r j)⁻¹)) * r j
    group
  · rintro x _ s hs ⟨h, i, rfl⟩
    obtain ⟨j, hj⟩ := stepInv i s hs
    refine ⟨h * ⟨r i * s⁻¹ * (r j)⁻¹, hj⟩, j, ?_⟩
    change h.val * r i * s⁻¹ = (h.val * (r i * s⁻¹ * (r j)⁻¹)) * r j
    group

theorem card_le (H : Subgroup G) [Finite H] [Finite I] (S : Set G)
    (hS : Subgroup.closure S = ⊤) (r : I → G) (i₀ : I) (hr : r i₀ = 1)
    (step : ∀ i s, s ∈ S → ∃ j, r i * s * (r j)⁻¹ ∈ H)
    (stepInv : ∀ i s, s ∈ S → ∃ j, r i * s⁻¹ * (r j)⁻¹ ∈ H) :
    Nat.card G ≤ Nat.card H * Nat.card I := by
  let f : H × I → G := fun z => z.1.val * r z.2
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨h, i, hi⟩ := exists_normalForm H S hS r i₀ hr step stepInv g
    exact ⟨(h, i), hi.symm⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

end Kourovka2135.FiniteCosetCertificate
