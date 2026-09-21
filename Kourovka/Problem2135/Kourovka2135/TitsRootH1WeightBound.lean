import Kourovka2135.TitsRootAdditiveMaps
import Kourovka2135.CohomologyNormalizer

/-! Actual H1 restrictions into scalar-weight additive maps on Tits roots.
All root/action data are genuine group maps and explicit identities. The
cohomology injection follows from the checked odd-index restriction theorem;
no Borel H1 value, abelianization identification or splitting is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.TitsRootH1WeightBound

open CategoryTheory groupCohomology
variable {k G : Type u} [Field k] [CharP k 2] [Group G]
variable (S : Subgroup G) (A : Rep k G) [(Rep.res S.subtype A).ρ.IsTrivial]

/-- Actual restriction followed by the trivial-coefficient H1 identification. -/
def restrictionHom : groupCohomology A 1 →ₗ[k] (Additive S →+ A) :=
  (H1IsoOfIsTrivial (Rep.res S.subtype A)).hom.hom.comp
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 1).hom

omit [CharP k 2] in
/-- On a genuine cocycle this map is its ordinary restriction to S. -/
theorem restrictionHom_pi_apply (z : cocycles₁ A) (x : S) :
    restrictionHom S A (H1π A z) (Additive.ofMul x) = z x := by
  change (H1IsoOfIsTrivial (Rep.res S.subtype A)).hom
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 1 (H1π A z))
      (Additive.ofMul x) = _
  rw [H1π_comp_map_apply, H1IsoOfIsTrivial_H1π_apply_apply]
  rfl

theorem restrictionHom_injective [S.FiniteIndex] (hindex : Odd S.index) :
    Function.Injective (restrictionHom S A) :=
  (H1IsoOfIsTrivial (Rep.res S.subtype A)).toLinearEquiv.injective.comp
    (GroupCohomology.restriction_injective_of_odd_index S A 1 hindex)

omit [CharP k 2] in
/-- Forward conjugation on roots has the forward coefficient action. -/
theorem restrictionHom_conjugation (α : S →* S) (g : G)
    (hα : ∀ x : S, (α x : G) = g * (x : G) * g⁻¹)
    (c : groupCohomology A 1) (x : S) :
    restrictionHom S A c (Additive.ofMul (α x)) =
      A.ρ g (restrictionHom S A c (Additive.ofMul x)) := by
  induction c using H1_induction_on with | h z =>
  rw [restrictionHom_pi_apply, restrictionHom_pi_apply]
  have hfix : A.ρ (α x : G) (z g) = z g :=
    Representation.isTrivial_apply (Rep.res S.subtype A).ρ (α x) (z g)
  have harg : g⁻¹ * (α x : G) * g = (x : G) := by
    rw [hα]
    simp [mul_assoc]
  have h := GroupCohomology.cocycle_one_inverse_conjugation A z g (α x : G)
  rw [hfix, sub_self, harg] at h
  exact (sub_eq_zero.mp h).symm

section ScalarRoots

variable {F : Type u} [Field F] [CharP F 2]
variable (ρ : Representation k G k)
variable [(Rep.res S.subtype (Rep.of ρ)).ρ.IsTrivial]
variable (θ : F ≃+* F) (hθ : ∀ x, θ (θ x) = x ^ 2)
variable (r : F → F → S)
variable (hmul : ∀ a b c d, r a b * r c d = r (a + c) (b + d + a * θ c))
variable (χ : Fˣ →* kˣ) (α : Fˣ → MulAut S) (t : Fˣ → G)
variable (hα : ∀ s x, (α s x : G) = t s * (x : G) * (t s)⁻¹)
variable (hroot : ∀ s a b, α s (r a b) =
  r ((s : F) * a) ((s : F) * θ (s : F) * b))
variable (hscalar : ∀ s v, ρ (t s) v = (χ s : k) * v)

/-- The actual linear map from Borel H1 to its scalar root-weight space. -/
def weightRestriction : groupCohomology (Rep.of ρ) 1 →ₗ[k]
    ScalarWeightAdditiveMaps.weightSpace χ :=
  ((TitsRootAdditiveMaps.firstCoordinateLinear θ hθ r hmul).comp
    (restrictionHom S (Rep.of ρ))).codRestrict _ (by
      intro c
      apply TitsRootAdditiveMaps.firstCoordinate_mem_weightSpace θ hθ r hmul
        χ α hroot
      intro s x
      exact (restrictionHom_conjugation S (Rep.of ρ) (α s).toMonoidHom (t s)
        (hα s) c x).trans (hscalar s _))

theorem weightRestriction_injective [S.FiniteIndex] (hindex : Odd S.index)
    (hcover : ∀ x : S, ∃ a b, x = r a b) :
    Function.Injective (weightRestriction S ρ θ hθ r hmul χ α t hα hroot hscalar) := by
  intro c d h
  apply restrictionHom_injective S (Rep.of ρ) hindex
  apply TitsRootAdditiveMaps.firstCoordinateLinear_injective θ hθ r hmul hcover
  exact congrArg Subtype.val h

include θ hθ hmul χ α t hα hroot hscalar

/-- This also supplies genuine finite dimensionality, not merely a finrank bound. -/
theorem finiteDimensional_H1 [S.FiniteIndex] (hindex : Odd S.index)
    (hcover : ∀ x : S, ∃ a b, x = r a b) :
    FiniteDimensional k (groupCohomology (Rep.of ρ) 1) := by
  let := ScalarWeightAdditiveMaps.finiteDimensional_weightSpace χ
  exact FiniteDimensional.of_injective (V₂ := ScalarWeightAdditiveMaps.weightSpace χ)
    (weightRestriction S ρ θ hθ r hmul χ α t hα hroot hscalar)
    (weightRestriction_injective S ρ θ hθ r hmul χ α t hα hroot hscalar hindex hcover)

theorem finrank_H1_le_one [S.FiniteIndex] (hindex : Odd S.index)
    (hcover : ∀ x : S, ∃ a b, x = r a b) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ 1 := by
  let := ScalarWeightAdditiveMaps.finiteDimensional_weightSpace χ
  exact (LinearMap.finrank_le_finrank_of_injective
    (weightRestriction_injective S ρ θ hθ r hmul χ α t hα hroot hscalar hindex hcover)).trans
    (ScalarWeightAdditiveMaps.finrank_weightSpace_le_one χ)

/-- A proved nonadditivity witness gives actual H1 vanishing. -/
theorem subsingleton_H1_of_not_additive [S.FiniteIndex] (hindex : Odd S.index)
    (hcover : ∀ x : S, ∃ a b, x = r a b)
    (w : F → k) (hw0 : w 0 = 0) (hw : ∀ s : Fˣ, w (s : F) = (χ s : k))
    (hbad : ¬ ∀ x y, w (x + y) = w x + w y) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have hz := ScalarWeightAdditiveMaps.weightSpace_eq_bot_of_not_additive χ w hw0 hw hbad
  let : Subsingleton (ScalarWeightAdditiveMaps.weightSpace χ) := by rw [hz]; infer_instance
  exact (weightRestriction_injective S ρ θ hθ r hmul χ α t hα hroot hscalar
    hindex hcover).subsingleton

end ScalarRoots
end Kourovka2135.TitsRootH1WeightBound
