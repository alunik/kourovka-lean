import Kourovka2135.FinitePermutationHeart
import Kourovka2135.PermutationAugmentationCocycles
import Mathlib.RepresentationTheory.Irreducible

/-! Actual augmentation maps, permutation-heart maps, and normalized H1.

Maps into a representation with no global fixed vectors kill the constant
line and descend through the actual heart quotient. For a simple target, the
heart's lack of coprime-subgroup invariants forces stabilizer invariants to
vanish. No assertion about irreducible-module classification is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PermutationHeartCohomology

open groupCohomology CocycleGeneratorBounds
open FinitePermutationAugmentation

variable {k G X V : Type u} [Field k] [Group G] [Fintype X] [MulAction G X]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (hcard : (Fintype.card X : k) = 0)

abbrev AugMaps := Representation.IntertwiningMap (action k G X) ρ
abbrev HeartMaps := Representation.IntertwiningMap
  (FinitePermutationHeart.representation k G X hcard) ρ

/-- Constants map to global fixed vectors, and hence to zero under this hypothesis. -/
theorem constantLine_le_ker (hglobal : ρ.invariants = ⊥) (f : AugMaps (X := X) ρ) :
    FinitePermutationHeart.constantLine k X hcard ≤ LinearMap.ker f.toLinearMap := by
  rintro _ ⟨c, rfl⟩
  have hfix : f (FinitePermutationHeart.constants k X hcard c) ∈ ρ.invariants := by
    intro g
    have h := LinearMap.congr_fun (f.isIntertwining' g)
      (FinitePermutationHeart.constants k X hcard c)
    change f (action k G X g (FinitePermutationHeart.constants k X hcard c)) =
      ρ g (f (FinitePermutationHeart.constants k X hcard c)) at h
    rw [FinitePermutationHeart.action_constants] at h
    exact h.symm
  rw [hglobal] at hfix
  exact hfix

/-- Descent of an actual equivariant augmentation map through the constant line. -/
def descend (hglobal : ρ.invariants = ⊥) (f : AugMaps (X := X) ρ) : HeartMaps (X := X) ρ hcard :=
  ((FinitePermutationHeart.constantLine k X hcard).liftQ f.toLinearMap
    (constantLine_le_ker ρ hcard hglobal f)).intertwiningMap_of_isIntertwiningMap
      (FinitePermutationHeart.representation k G X hcard) ρ (by
        intro g x
        induction x using Submodule.Quotient.induction_on with
        | _ v =>
            change f (action k G X g v) = ρ g (f v)
            exact LinearMap.congr_fun (f.isIntertwining' g) v)

@[simp] theorem descend_apply_quotient (hglobal : ρ.invariants = ⊥)
    (f : AugMaps (X := X) ρ) (v : Space k X) :
    descend ρ hcard hglobal f (FinitePermutationHeart.quotientHom k G X hcard v) = f v := rfl

/-- Pull back an actual heart intertwiner along the quotient map. -/
def precompose : HeartMaps (X := X) ρ hcard →ₗ[k] AugMaps (X := X) ρ where
  toFun f := f.comp (FinitePermutationHeart.quotientHom k G X hcard)
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl

@[simp] theorem precompose_apply (f : HeartMaps (X := X) ρ hcard) (v : Space k X) :
    precompose ρ hcard f v = f (FinitePermutationHeart.quotientHom k G X hcard v) := rfl

theorem precompose_injective : Function.Injective (precompose ρ hcard) := by
  intro f g h
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := FinitePermutationHeart.quotientHom_surjective k G X hcard w
  exact congrArg (fun a : AugMaps (X := X) ρ => a v) h

theorem precompose_descend (hglobal : ρ.invariants = ⊥) (f : AugMaps (X := X) ρ) :
    precompose ρ hcard (descend ρ hcard hglobal f) = f := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  rfl

theorem precompose_surjective (hglobal : ρ.invariants = ⊥) :
    Function.Surjective (precompose ρ hcard) :=
  fun f => ⟨descend ρ hcard hglobal f, precompose_descend ρ hcard hglobal f⟩

/-- The actual augmentation and heart Hom spaces are linearly equivalent. -/
def heartHomEquiv (hglobal : ρ.invariants = ⊥) :
    AugMaps (X := X) ρ ≃ₗ[k] HeartMaps (X := X) ρ hcard :=
  (LinearEquiv.ofBijective (precompose ρ hcard)
    ⟨precompose_injective ρ hcard, precompose_surjective ρ hcard hglobal⟩).symm

theorem descend_surjective (hglobal : ρ.invariants = ⊥) (f : AugMaps (X := X) ρ)
    (hf : Function.Surjective f) : Function.Surjective (descend ρ hcard hglobal f) := by
  intro w
  obtain ⟨v, hv⟩ := hf w
  exact ⟨FinitePermutationHeart.quotientHom k G X hcard v,
    (descend_apply_quotient ρ hcard hglobal f v).trans hv⟩

variable (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)

/-- The normalized cocycle equivalence followed by genuine quotient descent. -/
def cohomologyHeartEquiv (hglobal : ρ.invariants = ⊥)
    (hfixed : Representation.invariants (ρ.comp (MulAction.stabilizer G x₀).subtype) = ⊥)
    (hvanish : Subsingleton
      (groupCohomology (Rep.of (ρ.comp (MulAction.stabilizer G x₀).subtype)) 1)) :
    groupCohomology (Rep.of ρ) 1 ≃ₗ[k] HeartMaps (X := X) ρ hcard :=
  (NormalizedCocycleSubspace.cohomologyEquiv ρ (MulAction.stabilizer G x₀)
    hfixed hvanish).symm.trans
      ((PermutationAugmentationCocycles.normalizedEquiv ρ x₀ htrans).trans
        (heartHomEquiv ρ hcard hglobal))

include htrans

/-- If the heart has no U-fixed vectors for a coprime-order subgroup of the
point stabilizer, no nonzero simple target without global invariants has
stabilizer-fixed vectors. The proof uses actual principal cocycles, not
Frobenius reciprocity or a module-classification premise. -/
theorem stabilizer_invariants_eq_bot [ρ.IsIrreducible]
    (hglobal : ρ.invariants = ⊥) (U : Subgroup G) [Fintype U]
    (hUB : U ≤ MulAction.stabilizer G x₀)
    (horder : (Fintype.card U : k) ≠ 0)
    (hheart : Representation.invariants
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype) = ⊥) :
    Representation.invariants (ρ.comp (MulAction.stabilizer G x₀).subtype) = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  by_contra hvzero
  let z : PermutationAugmentationCocycles.Normalized ρ x₀ := ⟨principal ρ v, by
    intro b
    change ρ b v - v = 0
    have hb : ρ (b : G) v = v := hv b
    rw [hb, sub_self]⟩
  have hz : z ≠ 0 := by
    intro he
    have hp : principal ρ v = 0 := congrArg Subtype.val he
    have hvinv : v ∈ ρ.invariants := by
      rw [← principal_ker]
      exact hp
    rw [hglobal] at hvinv
    exact hvzero hvinv
  let e := PermutationAugmentationCocycles.normalizedEquiv ρ x₀ htrans
  let f : AugMaps (X := X) ρ := e z
  have hfzero : f ≠ 0 := by
    intro he
    apply hz
    apply e.injective
    simpa only [map_zero] using he
  have hfsurj : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hfzero
  let d : HeartMaps (X := X) ρ hcard := descend ρ hcard hglobal f
  have hdsurj : Function.Surjective d := descend_surjective ρ hcard hglobal f hfsurj
  let du : Representation.IntertwiningMap
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype)
      (ρ.comp U.subtype) :=
    ⟨d.toLinearMap, fun g => d.isIntertwining' g⟩
  have htarget : Representation.invariants (ρ.comp U.subtype) = ⊥ :=
    CoprimeInvariantLifting.invariants_eq_bot_of_surjective
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype)
      (ρ.comp U.subtype) horder du hdsurj hheart
  have hvinv : v ∈ Representation.invariants (ρ.comp U.subtype) := by
    intro g
    exact hv ⟨g.val, hUB g.property⟩
  rw [htarget] at hvinv
  exact hvzero hvinv

end Kourovka2135.PermutationHeartCohomology
