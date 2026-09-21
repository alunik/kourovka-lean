import Kourovka2135.RepresentationMovingConjugacy
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! The sufficient cohomology and moving-rank alternative is invariant
under an actual representation equivalence. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationCohomologyAlternative

variable {K G V W : Type u} [Field K] [Group G]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def Alternative (ρ : Representation K G V) (g : G) : Prop :=
  Module.finrank K (groupCohomology (Rep.of ρ) 1) = 0 ∨
    (Module.finrank K (groupCohomology (Rep.of ρ) 1) ≤ 1 ∧
      4 ≤ Module.finrank K (LinearMap.range (ρ g - LinearMap.id)))

theorem finrank_cohomology_eq (ρ : Representation K G V) (τ : Representation K G W)
    (e : ρ.Equiv τ) (n : ℕ) :
    Module.finrank K (groupCohomology (Rep.of ρ) n) =
      Module.finrank K (groupCohomology (Rep.of τ) n) :=
  (groupCohomology.mapIso (MulEquiv.refl G) e.toLinearEquiv
    (fun g => e.isIntertwining' g) n).toLinearEquiv.finrank_eq

theorem alternative_iff [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (τ : Representation K G W)
    (e : ρ.Equiv τ) (g : G) : Alternative ρ g ↔ Alternative τ g := by
  unfold Alternative
  rw [finrank_cohomology_eq ρ τ e 1,
    RepresentationMovingConjugacy.finrank_moving_eq_of_equiv ρ τ e g]

end Kourovka2135.RepresentationCohomologyAlternative
