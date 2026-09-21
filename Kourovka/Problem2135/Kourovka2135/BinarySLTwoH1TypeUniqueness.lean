import Kourovka2135.BinaryNaturalPrimeField
import Kourovka2135.RepresentationBaseChangeProjection
import Kourovka2135.RepresentationIntertwiningTransport
import Kourovka2135.BinarySLTwoEndCohomology
import Mathlib.Algebra.Algebra.ZMod

/-! The actual prime-field simple type with nonzero H1 is unique.

After extension over the actual commuting field, the checked classification
places a nonzero-H1 irreducible in a singleton Frobenius factor. The native
natural module embeds into that actual factor. Tensor coefficient projections
descend a nonzero map to the original module, and irreducibility makes it an
isomorphism. Neither a finite-field classification nor a Galois-descent theorem
is assumed, and the commuting field need not be identified with the parameter field.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinarySLTwoH1TypeUniqueness

open RepresentationIntertwiningTransport BinarySLTwoEndCohomology
open MinimalEndMovingRank

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (ρ : Representation (ZMod 2) (SLTwo.SL2 F) V) [ρ.IsIrreducible]

/-- Every binary irreducible with nonzero actual H1 is the actual native natural module. -/
theorem nonempty_natural_equiv (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Nonempty ((BinaryNaturalPrimeField.representation F).Equiv ρ) := by
  let : Algebra (ZMod 2) (EndField ρ) := Representation.IntertwiningMap.instAlgebra ρ
  let : Algebra (ZMod 2) (ClosedField ρ) := ZMod.algebra (ClosedField ρ) 2
  let : Module (EndField ρ) V := MinimalEndMovingRank.endModule ρ
  let : IsScalarTower (ZMod 2) (EndField ρ) V := MinimalEndMovingRank.endScalarTower ρ
  let : (BinaryNaturalPrimeField.representation F).IsIrreducible :=
    BinaryNaturalPrimeField.isIrreducible F
  obtain ⟨i, ⟨a⟩⟩ :=
    BinarySLTwoIrreducibleCohomology.exists_singleton_equiv_of_finrank_H1_ne_zero
      (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) f hcard hf
      (finrank_closed_H1_ne_zero ρ hH)
  let u := BinaryNaturalPrimeField.singletonIntertwiner F (ClosedField ρ) (parameterEmbedding ρ) i
  let b := restrictEquiv (ZMod 2) a.symm
  let ψ := b.toIntertwiningMap.comp u
  have hψinj : Function.Injective ψ := b.toLinearEquiv.injective.comp
    (BinaryNaturalPrimeField.singletonIntertwiner_injective
      F (ClosedField ρ) (parameterEmbedding ρ) i)
  have hψ : ψ ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := exists_ne (0 : Fin 2 → F)
    apply hx
    apply hψinj
    rw [hz]
    rfl
  have hex : ∃ φ : (BinaryNaturalPrimeField.representation F).IntertwiningMap ρ, φ ≠ 0 := by
    obtain ⟨φ₀, hφ₀⟩ :=
      @RepresentationBaseChangeProjection.exists_nonzero_intertwiner
        (ZMod 2) _ (EndField ρ) (ClosedField ρ) (SLTwo.SL2 F) V (Fin 2 → F)
        _ _ (Representation.IntertwiningMap.instAlgebra ρ) _ _
        (IsScalarTower.of_algebraMap_eq'
          (R := ZMod 2) (S := EndField ρ) (A := ClosedField ρ) (Subsingleton.elim _ _))
        _ _
        (MinimalEndMovingRank.endModule ρ) _
        (MinimalEndMovingRank.endScalarTower ρ)
        _ _ (overEnd ρ) (BinaryNaturalPrimeField.representation F) ψ hψ
    let φ : (BinaryNaturalPrimeField.representation F).IntertwiningMap ρ := {
      toLinearMap := φ₀.toLinearMap.toAddMonoidHom.toZModLinearMap 2
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun T => T v) (φ₀.isIntertwining' g) }
    refine ⟨φ, ?_⟩
    intro hφ
    apply hφ₀
    apply DFunLike.ext
    intro v
    exact congrArg (fun T : (BinaryNaturalPrimeField.representation F).IntertwiningMap ρ => T v) hφ
  obtain ⟨φ, hφ⟩ := hex
  exact ⟨φ.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero φ).resolve_right hφ)⟩

/-- Choose the actual equivalence proved by the coefficient-projection argument. -/
def naturalEquiv (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    (BinaryNaturalPrimeField.representation F).Equiv ρ :=
  Classical.choice (nonempty_natural_equiv ρ f hcard hf hH)

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
variable (τ : Representation (ZMod 2) (SLTwo.SL2 F) W) [τ.IsIrreducible]

/-- Any two actual irreducible binary modules with nonzero H1 are equivalent. -/
def equiv (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hρ : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) ≠ 0)
    (hτ : Module.finrank (ZMod 2) (groupCohomology (Rep.of τ) 1) ≠ 0) : ρ.Equiv τ :=
  (naturalEquiv ρ f hcard hf hρ).symm.trans (naturalEquiv τ f hcard hf hτ)

section GroupEquiv
variable {H : Type} [Group H]
variable (ρH : Representation (ZMod 2) H V) [ρH.IsIrreducible]
variable (τH : Representation (ZMod 2) H W) [τH.IsIrreducible]

/-- The uniqueness statement transfers to any actual isomorphic quotient group. -/
def groupEquiv (e : SLTwo.SL2 F ≃* H)
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hρ : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρH) 1) ≠ 0)
    (hτ : Module.finrank (ZMod 2) (groupCohomology (Rep.of τH) 1) ≠ 0) : ρH.Equiv τH := by
  let : Representation.IsIrreducible (ρH.comp e.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp ρH e
  let : Representation.IsIrreducible (τH.comp e.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp τH e
  have hρ' : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (ρH.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [RepresentationGroupEquiv.finrank_cohomology_comp ρH e 1]
  have hτ' : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (τH.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [RepresentationGroupEquiv.finrank_cohomology_comp τH e 1]
  exact equivOfComp e (equiv (ρH.comp e.toMonoidHom) (τH.comp e.toMonoidHom)
    f hcard hf hρ' hτ')
end GroupEquiv

end Kourovka2135.BinarySLTwoH1TypeUniqueness
