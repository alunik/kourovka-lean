import Kourovka2135.MinimalEndomorphismBound
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Self-duality of the actual minimal-center representation of G/R.

A nonzero scalar commutator form already gives self-duality for the G-action.
Quotient surjectivity descends the same linear equivalence to G/R and hence
identifies its ordinary cohomology with that of its contragredient.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open CategoryTheory
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian p (commutator N)]

/-- The actual scalar commutator equivalence descends to the quotient-group action. -/
def minimalCenterScalarCommutatorEquiv
    (ell : Module.Dual (ZMod p) (Additive (commutator N))) (hell : ell ≠ 0) :
    (minimalCenterRepresentation N hN hmin R hR).Equiv
      (minimalCenterRepresentation N hN hmin R hR).dual := by
  let : Group.IsNilpotent N := hN.isNilpotent
  let e := minimalScalarCommutatorEquiv N hmin p ell hell
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R g
  exact e.isIntertwining' a

/-- Nonabelianness supplies a nonzero functional and an actual self-duality. -/
def minimalCenterSelfDual (hnonabelian : ¬ IsMulCommutative N) :
    (minimalCenterRepresentation N hN hmin R hR).Equiv
      (minimalCenterRepresentation N hN hmin R hR).dual := by
  refine Classical.choice ?_
  have hDne : commutator N ≠ ⊥ := by
    intro hbot
    exact hnonabelian ((commutator_eq_bot_iff N).mp hbot)
  let : Nontrivial (commutator N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
  obtain ⟨t, ht⟩ := exists_ne (1 : commutator N)
  obtain ⟨ell, hellt⟩ := exists_linear_functional_ne_zero (K := ZMod p)
    (show Additive.ofMul t ≠ 0 from ht)
  have hell : ell ≠ 0 := by
    intro h
    exact hellt (congrArg (fun f : Module.Dual (ZMod p) (Additive (commutator N)) =>
      f (Additive.ofMul t)) h)
  exact ⟨minimalCenterScalarCommutatorEquiv N hN hmin R hR ell hell⟩

/-- The self-duality acts on ordinary group cohomology by the actual equivariant map. -/
def minimalCenterSelfDualCohomologyIso (hnonabelian : ¬ IsMulCommutative N) (n : ℕ) :
    groupCohomology (Rep.of (minimalCenterRepresentation N hN hmin R hR)) n ≅
      groupCohomology (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) n := by
  let e := minimalCenterSelfDual N hN hmin R hR hnonabelian
  exact groupCohomology.mapIso (MulEquiv.refl (G ⧸ R)) e.toLinearEquiv e.isIntertwining' n

theorem minimalCenterDualCohomology_finrank_eq
    (hnonabelian : ¬ IsMulCommutative N) (n : ℕ) :
    Module.finrank (ZMod p)
      (groupCohomology (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) n) =
      Module.finrank (ZMod p)
        (groupCohomology (Rep.of (minimalCenterRepresentation N hN hmin R hR)) n) :=
  (minimalCenterSelfDualCohomologyIso N hN hmin R hR hnonabelian n).toLinearEquiv.finrank_eq.symm

end Kourovka2135
