import Kourovka2135.PermutationHeartCohomology
import Kourovka2135.PermutationCharacterMultiplicity
import Kourovka2135.AbelianCharacterLine

/-! A first-cohomology bound from a transitive permutation heart and one
character projector. The abelian coprime subgroup fixes no heart vector and
is transitive off one point. Its nontrivial character projectors have rank
at most one, which bounds every simple-target Hom space. No irreducible
classification or explicit Fourier basis is assumed. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PermutationHeartCohomologyBound
open groupCohomology PermutationHeartCohomology
open scoped MonoidAlgebra

variable {k G X V : Type u} [Field k] [IsAlgClosed k] [Group G]
variable [Fintype X] [MulAction G X] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]
variable (hcard : (Fintype.card X : k) = 0)
variable (U : Subgroup G) [Fintype U] [IsMulCommutative U]
variable (x₀ x₁ : X)

/-- One nonzero quotient map detects a nontrivial character line in the target. -/
theorem heartMaps_finrank_le_one
    (horder : (Fintype.card U : k) ≠ 0)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y)
    (hheart : Representation.invariants
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype) = ⊥) :
    Module.finrank k (HeartMaps (X := X) ρ hcard) ≤ 1 := by
  classical
  by_cases hz : ∀ f : HeartMaps (X := X) ρ hcard, f = 0
  · let : Subsingleton (HeartMaps (X := X) ρ hcard) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  push Not at hz
  obtain ⟨f, hf⟩ := hz
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  have hsurj : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  let fu : Representation.IntertwiningMap
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype)
      (ρ.comp U.subtype) := ⟨f.toLinearMap, fun g => f.isIntertwining' g⟩
  have htarget : Representation.invariants (ρ.comp U.subtype) = ⊥ :=
    CoprimeInvariantLifting.invariants_eq_bot_of_surjective
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype)
      (ρ.comp U.subtype) horder fu hsurj hheart
  obtain ⟨χ, v, hv, heigen, g, hg⟩ :=
    AbelianCharacterLine.exists_nontrivial_character_line (ρ.comp U.subtype) htarget
  have hχ : χ ≠ 1 := by
    intro he
    rw [he] at hg
    exact hg rfl
  let a : k[G] := WeightedCharacterProjector.element χ U.subtype
  have hQ : ρ.asAlgebraHom a ≠ 0 := by
    change ρ.asAlgebraHom (WeightedCharacterProjector.element χ U.subtype) ≠ 0
    rw [WeightedCharacterProjector.asAlgebraHom_element]
    exact WeightedCharacterProjector.projector_ne_zero (ρ.comp U.subtype) χ horder v hv heigen
  have hP := PermutationCharacterMultiplicity.heart_element_finrank_le_one
    k G X U χ hcard x₀ x₁ hχ hfix hx₁ htrans
  exact MultiplicityOneIntertwining.finrank_le_one_of_groupAlgebra
    (FinitePermutationHeart.representation k G X hcard) ρ a hQ hP

/-- The actual normalized-H1 equivalence transfers the Hom-space bound. -/
theorem finrank_H1_le_one
    (hglobal : ρ.invariants = ⊥)
    (horder : (Fintype.card U : k) ≠ 0)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y)
    (hGtrans : ∀ x : X, ∃ g : G, g • x₀ = x)
    (hheart : Representation.invariants
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype) = ⊥)
    (hB : Subsingleton (groupCohomology
      (Rep.of (ρ.comp (MulAction.stabilizer G x₀).subtype)) 1)) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ 1 := by
  have hb := PermutationHeartCohomology.stabilizer_invariants_eq_bot
    ρ hcard x₀ hGtrans hglobal U hfix horder hheart
  let e := PermutationHeartCohomology.cohomologyHeartEquiv
    ρ hcard x₀ hGtrans hglobal hb hB
  exact e.finrank_eq.trans_le
    (heartMaps_finrank_le_one ρ hcard U x₀ x₁ horder hfix hx₁ htrans hheart)

end Kourovka2135.PermutationHeartCohomologyBound
