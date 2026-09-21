/-
Copyright (c) 2026 The Tau Ceti contributors and Kourovka 21.35 contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The degree-two algebraic homotopy proof is adapted from
TauCeti/RepresentationTheory/Homological/ContCohomology/Conjugation.lean,
commit 7a4e28011b29a4e8c8365fe87f2144022cf1377f. Here it is applied to
mathlib's actual group cohomology, with no topological or continuous-cohomology imports.
-/
import Kourovka2135.CohomologyRestriction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Restricted cohomology classes in degrees one and two are fixed by
normalizer conjugation with its coefficient action. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.GroupCohomology
open CategoryTheory groupCohomology
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem cocycle_one_inverse_conjugation (A : Rep k G)
    (c : cocycles₁ A) (g x : G) :
    A.ρ g (c (g⁻¹ * x * g)) - c x = A.ρ x (c g) - c g := by
  have h₁ := (mem_cocycles₁_iff c).mp c.property g (g⁻¹ * x * g)
  have h₂ := (mem_cocycles₁_iff c).mp c.property x g
  simp only [mul_assoc, mul_inv_cancel_left] at h₁
  have he : A.ρ g (c (g⁻¹ * x * g)) + c g = A.ρ x (c g) + c x :=
    by simpa only [mul_assoc] using h₁.symm.trans h₂
  exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using he)

/-- The degree-two conjugation homotopy is an actual one-cochain. -/
def conjugationHomotopy₂ (A : Rep k G) (g : G) (c : G × G → A) : G → A :=
  fun x => c (g, g⁻¹ * x * g) - c (x, g)

theorem cocycle_two_inverse_conjugation (A : Rep k G)
    (c : cocycles₂ A) (g x y : G) :
    A.ρ g (c (g⁻¹ * x * g, g⁻¹ * y * g)) - c (x, y) =
      A.ρ x (conjugationHomotopy₂ A g c y) -
        conjugationHomotopy₂ A g c (x * y) + conjugationHomotopy₂ A g c x := by
  have hmul : g * (g⁻¹ * x * g) = x * g := by simp [mul_assoc]
  have hmul' : g * (g⁻¹ * y * g) = y * g := by simp [mul_assoc]
  have hconjmul : (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by
    simp [mul_assoc]
  have h₁ := (mem_cocycles₂_iff c).mp c.property g (g⁻¹ * x * g) (g⁻¹ * y * g)
  have h₂ := (mem_cocycles₂_iff c).mp c.property x g (g⁻¹ * y * g)
  have h₃ := (mem_cocycles₂_iff c).mp c.property x y g
  simp only [hmul, hmul', hconjmul] at h₁ h₂ h₃
  have h₁' : A.ρ g (c (g⁻¹ * x * g, g⁻¹ * y * g)) =
      c (x * g, g⁻¹ * y * g) + c (g, g⁻¹ * x * g) -
        c (g, g⁻¹ * (x * y) * g) := by
    apply (eq_sub_iff_add_eq).mpr
    exact h₁.symm
  have h₂' : A.ρ x (c (g, g⁻¹ * y * g)) =
      c (x * g, g⁻¹ * y * g) + c (x, g) - c (x, y * g) := by
    apply (eq_sub_iff_add_eq).mpr
    exact h₂.symm
  have h₃' : A.ρ x (c (y, g)) = c (x * y, g) + c (x, y) - c (x, y * g) := by
    apply (eq_sub_iff_add_eq).mpr
    exact h₃.symm
  rw [h₁']
  simp only [conjugationHomotopy₂, map_sub]
  rw [h₂', h₃']
  abel

/-- Coefficient action compatible with inverse conjugation along any group homomorphism. -/
def conjugationCoefficient (A : Rep k G) (i : H →* G) (f : H →* H)
    (g : G) (hf : ∀ x, i (f x) = g⁻¹ * i x * g) :
    Rep.res f (Rep.res i A) ⟶ Rep.res i A :=
  Rep.ofHom ⟨A.ρ g, fun x => by
    ext m
    change A.ρ g (A.ρ (i (f x)) m) = A.ρ (i x) (A.ρ g m)
    rw [hf]
    simp only [← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

theorem restriction_fixed_one (A : Rep k G) (i : H →* G) (f : H →* H)
    (g : G) (hf : ∀ x, i (f x) = g⁻¹ * i x * g)
    (x : groupCohomology A 1) :
    groupCohomology.map f (conjugationCoefficient A i f g hf) 1
        (groupCohomology.map i (𝟙 (Rep.res i A)) 1 x) =
      groupCohomology.map i (𝟙 (Rep.res i A)) 1 x := by
  induction x using H1_induction_on with | h c =>
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  apply (H1π_eq_iff _ _).mpr
  refine ⟨c g, ?_⟩
  funext h
  change A.ρ (i h) (c g) - c g = A.ρ g (c (i (f h))) - c (i h)
  rw [hf, cocycle_one_inverse_conjugation]

theorem restriction_fixed_two (A : Rep k G) (i : H →* G) (f : H →* H)
    (g : G) (hf : ∀ x, i (f x) = g⁻¹ * i x * g)
    (x : groupCohomology A 2) :
    groupCohomology.map f (conjugationCoefficient A i f g hf) 2
        (groupCohomology.map i (𝟙 (Rep.res i A)) 2 x) =
      groupCohomology.map i (𝟙 (Rep.res i A)) 2 x := by
  induction x using H2_induction_on with | h c =>
  rw [H2π_comp_map_apply, H2π_comp_map_apply]
  apply (H2π_eq_iff _ _).mpr
  refine ⟨fun h => conjugationHomotopy₂ A g c (i h), ?_⟩
  funext h
  change A.ρ (i h.1) (conjugationHomotopy₂ A g c (i h.2)) -
      conjugationHomotopy₂ A g c (i (h.1 * h.2)) +
      conjugationHomotopy₂ A g c (i h.1) =
    A.ρ g (c (i (f h.1), i (f h.2))) - c (i h.1, i h.2)
  rw [hf, hf, map_mul, cocycle_two_inverse_conjugation]

/-- Inverse conjugation by a normalizer element, with no ambient normality assumption. -/
def normalizerInverseConjugation (S : Subgroup G) (g : (Subgroup.normalizer (S : Set G))) : S →* S where
  toFun x := ⟨g.val⁻¹ * x.val * g.val,
    (Subgroup.mem_normalizer_iff''.mp g.property x.val).mp x.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

def normalizerConjugation (S : Subgroup G) (A : Rep k G)
    (g : (Subgroup.normalizer (S : Set G))) (n : ℕ) :
    groupCohomology (Rep.res S.subtype A) n →ₗ[k]
      groupCohomology (Rep.res S.subtype A) n :=
  (groupCohomology.map (normalizerInverseConjugation S g)
    (conjugationCoefficient A S.subtype (normalizerInverseConjugation S g) g.val
      (fun _ => rfl)) n).hom

theorem normalizerConjugation_restriction (S : Subgroup G) (A : Rep k G)
    (g : (Subgroup.normalizer (S : Set G))) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (x : groupCohomology A n) :
    normalizerConjugation S A g n
        (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n x) =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n x := by
  rcases hn with rfl | rfl
  · exact restriction_fixed_one A S.subtype (normalizerInverseConjugation S g)
      g.val (fun _ => rfl) x
  · exact restriction_fixed_two A S.subtype (normalizerInverseConjugation S g)
      g.val (fun _ => rfl) x

/-- Fixed classes for any chosen subgroup of the normalizer. -/
def normalizerFixedSubmodule (S : Subgroup G) (A : Rep k G)
    (T : Subgroup (Subgroup.normalizer (S : Set G))) (n : ℕ) :
    Submodule k (groupCohomology (Rep.res S.subtype A) n) where
  carrier := {x | ∀ t : T, normalizerConjugation S A t.val n x = x}
  zero_mem' := fun _ => map_zero _
  add_mem' hx hy t := by rw [map_add, hx t, hy t]
  smul_mem' a x hx t := by rw [map_smul, hx t]

theorem restriction_range_le_normalizerFixedSubmodule
    (S : Subgroup G) (A : Rep k G) (T : Subgroup (Subgroup.normalizer (S : Set G)))
    (n : ℕ) (hn : n = 1 ∨ n = 2) :
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom.range ≤
      normalizerFixedSubmodule S A T n := by
  rintro _ ⟨x, rfl⟩ t
  exact normalizerConjugation_restriction S A t.val n hn x

/-- At odd index in characteristic two, normalizer-fixed classes give an
upper bound for the actual first or second cohomology dimension. -/
theorem finrank_le_normalizerFixed_of_odd_index
    {K : Type u} [Field K] [CharP K 2]
    (S : Subgroup G) [S.FiniteIndex] (A : Rep K G)
    (T : Subgroup (Subgroup.normalizer (S : Set G))) (n : ℕ) (hn : n = 1 ∨ n = 2)
    [Module.Finite K (groupCohomology (Rep.res S.subtype A) n)]
    (hindex : Odd S.index) :
    Module.finrank K (groupCohomology A n) ≤
      Module.finrank K (normalizerFixedSubmodule S A T n) := by
  let r := (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom
  let l : groupCohomology A n →ₗ[K] normalizerFixedSubmodule S A T n :=
    r.codRestrict _ (fun x t => normalizerConjugation_restriction S A t.val n hn x)
  have hr := restriction_injective_of_odd_index S A n hindex
  apply LinearMap.finrank_le_finrank_of_injective (f := l)
  intro x y hxy
  exact hr (congrArg Subtype.val hxy)

end Kourovka2135.GroupCohomology
