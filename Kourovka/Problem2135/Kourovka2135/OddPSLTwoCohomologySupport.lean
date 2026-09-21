import Kourovka2135.OddPSLTwoFirstCohomology

/-! Genuine odd-PSL2 heart maps detected by ordinary first cohomology.

Actual Borel invariant and cohomology vanishings identify H1 with the Hom
space out of the actual projective permutation heart. Nonzero H1 therefore
produces a nonzero surjection from that heart to a simple coefficient.
No algebraic closure, module classification or supplied cohomology value
is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.OddPSLTwoCohomologySupport
open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart

variable (F k : Type u) [Field F] [Fintype F] [Field k] [CharP k 2]
variable (hodd : Odd (Fintype.card F))
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (Q F) V) [ρ.IsIrreducible] [FiniteDimensional k V]

/-- The actual ordinary H1/heart-Hom equivalence over any binary coefficient field. -/
def cohomologyHeartEquiv (hglobal : ρ.invariants = ⊥) :
    groupCohomology (Rep.of ρ) 1 ≃ₗ[k]
      (heartRepresentation F k hodd).IntertwiningMap ρ :=
  PermutationHeartCohomology.cohomologyHeartEquiv ρ (card_points_cast_zero F k hodd)
    (none : Option F) (fun x => MulAction.exists_smul_eq (Q F) none x) hglobal
    (OddPSLTwoFirstCohomology.borel_invariants_eq_bot F k hodd ρ hglobal)
    (OddPSLTwoFirstCohomology.subsingleton_borel_H1 F k hodd ρ hglobal)

/-- A nonzero actual H1 class gives a nonzero intertwiner from the actual heart. -/
theorem exists_nonzero_heart_intertwiner (hglobal : ρ.invariants = ⊥)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    ∃ f : (heartRepresentation F k hodd).IntertwiningMap ρ, f ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ne (0 : groupCohomology (Rep.of ρ) 1)
  refine ⟨cohomologyHeartEquiv F k hodd ρ hglobal z, ?_⟩
  intro h
  apply hz
  apply (cohomologyHeartEquiv F k hodd ρ hglobal).injective
  simpa only [map_zero] using h

/-- Simplicity of the target turns the detected heart map into an actual surjection. -/
theorem exists_nonzero_surjective_heart_intertwiner (hglobal : ρ.invariants = ⊥)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    ∃ f : (heartRepresentation F k hodd).IntertwiningMap ρ,
      f ≠ 0 ∧ Function.Surjective f := by
  obtain ⟨f, hf⟩ := exists_nonzero_heart_intertwiner F k hodd ρ hglobal
  exact ⟨f, hf, (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩

end Kourovka2135.OddPSLTwoCohomologySupport
