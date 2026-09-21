import Kourovka2135.MinimalCenterDimension
import Kourovka2135.MinimalEndomorphismBound
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Explicit identification of the double quotient with N/Z(N), including
its quotient-group action and the induced dual first-cohomology isomorphism. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
open CategoryTheory

section Linear
variable {G : Type*} [Group G]

noncomputable def abelianizationCenterQuotientLinearEquiv
    (N : Subgroup G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    (hC : commutator N ≤ Subgroup.center N) :
    (Additive (N ⧸ commutator N) ⧸ centerImageSubmodule N (commutator N) 2) ≃ₗ[ZMod 2]
      Additive (N ⧸ Subgroup.center N) :=
  (Submodule.quotEquivOfEq _ _
    (abelianizationCenterProjection_ker_eq_centerImageSubmodule N hC).symm).trans
      ((abelianizationCenterProjection hC).quotKerEquivOfSurjective
        (abelianizationCenterProjection_surjective hC))

@[simp] theorem abelianizationCenterQuotientLinearEquiv_mk
    (N : Subgroup G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    (hC : commutator N ≤ Subgroup.center N) (m : Additive (N ⧸ commutator N)) :
    abelianizationCenterQuotientLinearEquiv N hC
      ((centerImageSubmodule N (commutator N) 2).mkQ m) =
        abelianizationCenterProjection hC m := rfl

end Linear

/-- An explicit representation equivalence induces the contravariant dual equivalence. -/
def representationDualEquiv
    {k S V W : Type*} [CommRing k] [Group S]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k S V} {σ : Representation k S W} (e : ρ.Equiv σ) :
    σ.dual.Equiv ρ.dual :=
  Representation.Equiv.mk e.toLinearEquiv.dualMap (by
    intro g
    apply LinearMap.ext
    intro ell
    apply LinearMap.ext
    intro x
    change ell (σ g⁻¹ (e x)) = ell (e (ρ g⁻¹ x))
    exact congrArg ell (LinearMap.congr_fun (e.isIntertwining' g⁻¹) x).symm)

section Actual
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
variable [IsElementaryAbelian 2 (N ⧸ commutator N)]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

/-- The quotient of N/N' by the image of Z(N) is the actual N/Z(N) representation. -/
noncomputable def minimalCenterRepresentationEquiv :
    (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).Equiv
      (minimalCenterRepresentation N hN hmin R hR) := by
  let : Group.IsNilpotent N := hN.isNilpotent
  let hC := minimal_noncentral_commutator_le_internal_center N hmin
  let e := abelianizationCenterQuotientLinearEquiv N hC
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R g
  obtain ⟨m, rfl⟩ := (centerImageSubmodule N (commutator N) 2).mkQ_surjective z
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator N) m.toMul
  have hm : m = Additive.ofMul (QuotientGroup.mk' (commutator N) n) := hn.symm
  rw [hm]
  rfl

/-- The dual cohomology transport is induced by the actual equivariant quotient map. -/
noncomputable def minimalCenterRepresentationDualH1Iso :
    groupCohomology (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1 ≅
      groupCohomology
        (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1 := by
  let e := representationDualEquiv
    (minimalCenterRepresentationEquiv N hN hnonabelian hmin R hR hRΦ)
  refine groupCohomology.mapIso (MulEquiv.refl (G ⧸ R)) e.toLinearEquiv ?_ 1
  exact e.isIntertwining'

theorem minimalCenterQuotientRepresentation_dual_h1_finrank_eq :
    Module.finrank (ZMod 2) (groupCohomology
      (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1) =
    Module.finrank (ZMod 2) (groupCohomology
      (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1) :=
  (minimalCenterRepresentationDualH1Iso N hN hnonabelian hmin R hR hRΦ).toLinearEquiv.finrank_eq.symm

include hnonabelian hRΦ in
/-- The center-excess bound, now stated on the dual of the actual N/Z(N) module. -/
theorem minimal_abelianization_center_finrank_difference_le_actual_h1 :
    Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≤
      Module.finrank (ZMod 2) (groupCohomology
        (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1) := by
  have h := minimal_abelianization_center_finrank_difference_le_h1
    N hN hnonabelian hmin R hR hRΦ
  rwa [minimalCenterQuotientRepresentation_dual_h1_finrank_eq N hN hnonabelian hmin R hR hRΦ] at h

end Actual
end Kourovka2135
