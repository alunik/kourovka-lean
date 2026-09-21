/-
Copyright (c) 2026 Kourovka 21.35 formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Kourovka2135.Vendor.TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Injective restriction when the subgroup index is invertible

The ported TauCeti theorem proves that corestriction after restriction is
multiplication by the finite subgroup index. Cancelling this invertible scalar
gives an injective restriction map in every cohomological degree, for arbitrary
coefficients. In particular, restriction on `H¹` is injective for an odd-index
subgroup in characteristic two. No cohomology-vanishing conclusion is asserted.
-/

set_option autoImplicit false

public section

open CategoryTheory

universe u

namespace Kourovka2135.GroupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Restriction is injective in every degree when the subgroup index is a unit
in the coefficient ring. The coefficients need not have trivial group action. -/
theorem restriction_injective_of_isUnit_index
    (S : Subgroup G) [S.FiniteIndex] (A : Rep.{u} k G) (n : ℕ)
    (hindex : IsUnit (S.index : k)) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom := by
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  have hcomp :
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n ≫
        TauCeti.groupCohomology.corestriction S A n).hom) x =
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n ≫
        TauCeti.groupCohomology.corestriction S A n).hom) y :=
    congrArg (TauCeti.groupCohomology.corestriction S A n).hom hxy
  rw [TauCeti.groupCohomology.map_subtype_id_comp_corestriction] at hcomp
  simpa [Nat.cast_smul_eq_nsmul] using hcomp

/-- Typeclass form of restriction injectivity for an invertible index. -/
theorem restriction_injective_of_invertible_index
    (S : Subgroup G) [S.FiniteIndex] (A : Rep.{u} k G) (n : ℕ)
    [Invertible (S.index : k)] :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom :=
  restriction_injective_of_isUnit_index S A n (isUnit_of_invertible _)

/-- Coprimality of the index with the characteristic makes its scalar action
invertible, and hence restriction injective. No primality assumption is needed. -/
theorem restriction_injective_of_coprime_index
    (S : Subgroup G) [S.FiniteIndex] (A : Rep.{u} k G) (n : ℕ)
    (p : ℕ) [CharP k p] (hindex : S.index.Coprime p) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom := by
  letI : Invertible (S.index : k) := invertibleOfCoprime hindex
  exact restriction_injective_of_invertible_index S A n

/-- The odd-index, characteristic-two case used for restriction to a Borel
subgroup. It applies to arbitrary coefficient representations in every degree. -/
theorem restriction_injective_of_odd_index
    [CharP k 2] (S : Subgroup G) [S.FiniteIndex] (A : Rep.{u} k G) (n : ℕ)
    (hindex : Odd S.index) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom :=
  restriction_injective_of_coprime_index S A n 2 hindex.coprime_two_right

/-- The exact degree-one specialization needed by the elementary Borel
calculation for `SL₂` in characteristic two. -/
theorem h1_restriction_injective_of_odd_index
    [CharP k 2] (S : Subgroup G) [S.FiniteIndex] (A : Rep.{u} k G)
    (hindex : Odd S.index) :
    Function.Injective
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 1).hom :=
  restriction_injective_of_odd_index S A 1 hindex

end Kourovka2135.GroupCohomology
