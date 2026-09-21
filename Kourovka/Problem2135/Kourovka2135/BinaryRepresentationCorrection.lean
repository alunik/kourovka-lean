import Kourovka2135.IrreducibleCorrectionAlternative
import Kourovka2135.RepresentationCohomologyAlternative
import Kourovka2135.RepresentationGroupEquiv

/-! The finite binary correction bound and its transport along an actual
group equivalence. The dual-cohomology equality is an explicit input here;
the minimal-kernel application supplies it from its commutator pairing. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryRepresentationCorrection
open IrreducibleEndCohomology RepresentationCohomologyAlternative

variable {G H V : Type} [Group G] [Group H]
variable [AddCommGroup V] [Module (ZMod 2) V]

def Bound (ρ : Representation (ZMod 2) G V) (g : G) : Prop :=
  Subsingleton (groupCohomology (Rep.of ρ.dual) 1) ∨
    2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) +
      2 * Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) ≤
        Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id))

theorem dual_comp_equiv (ρ : Representation (ZMod 2) G V) (e : H ≃* G) :
    Representation.dual (ρ.comp e.toMonoidHom) = ρ.dual.comp e.toMonoidHom := by
  ext g ell v
  change ell (ρ (e g⁻¹) v) = ell (ρ ((e g)⁻¹) v)
  rw [map_inv]

theorem dual_finrank_eq_of_comp (ρ : Representation (ZMod 2) G V) (e : H ≃* G)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) :
    Module.finrank (ZMod 2) (groupCohomology (Rep.of (Representation.dual (ρ.comp e.toMonoidHom))) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) := by
  rw [dual_comp_equiv, RepresentationGroupEquiv.finrank_cohomology_comp,
    RepresentationGroupEquiv.finrank_cohomology_comp, hdual]

theorem of_comp (ρ : Representation (ZMod 2) G V) (e : H ≃* G) (g : G)
    (h : Bound (ρ.comp e.toMonoidHom) (e.symm g)) : Bound ρ g := by
  obtain ⟨g, rfl⟩ := e.surjective g
  rw [e.symm_apply_apply] at h
  rcases h with hz | hr
  · left
    rw [dual_comp_equiv] at hz
    let := hz
    exact (RepresentationGroupEquiv.cohomologyIso ρ.dual e 1).toLinearEquiv.symm.injective.subsingleton
  · right
    rw [dual_comp_equiv, RepresentationGroupEquiv.finrank_endomorphism_comp,
      RepresentationGroupEquiv.finrank_cohomology_comp] at hr
    exact hr

theorem of_closed [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (g : G)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1))
    (hclosed : Alternative (extended ρ) g) : Bound ρ g :=
  IrreducibleCorrectionAlternative.descend ρ g hdual hclosed

end Kourovka2135.BinaryRepresentationCorrection
