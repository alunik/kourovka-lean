import Kourovka2135.BinaryTensorSLTwoAction
import Kourovka2135.BinaryAdditiveTorusAction

/-! Identify the restriction of the actual tensor SL2 representation with
its previously constructed additive-group coefficient representation.

The coefficient isomorphism is an actual representation isomorphism. Its
torus compatibility is proved from the natural-tensor action formula, so
the later normalizer/cohomology comparison has no action-identification
hypothesis to discharge.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryTensorSLTwoRestriction

open CategoryTheory BinaryAdditiveCohomology

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- The actual tensor SL2 module, in its proved exterior coefficient coordinates. -/
def ambient : Rep.{u} k (SLTwo.SL2 F) :=
  Rep.of (BinaryTensorSLTwo.representation k σ I)

/-- The inverse coefficient-coordinate map intertwines the actual unipotent restriction. -/
theorem coefficientLinearEquiv_symm_action (g : Multiplicative F)
    (v : BinaryTensorCoefficient.Carrier k I) :
    (coefficientLinearEquiv k I σ hcard).symm
        (BinaryTensorSLTwo.representation k σ I (SLTwo.uniHom F g) v) =
      (coefficientRepresentation k I σ hcard).ρ g
        ((coefficientLinearEquiv k I σ hcard).symm v) := by
  apply (coefficientLinearEquiv k I σ hcard).injective
  rw [LinearEquiv.apply_symm_apply, coefficient_action, LinearEquiv.apply_symm_apply]
  change BinaryTensorSLTwo.representation k σ I (SLTwo.uni g.toAdd) v = _
  rw [BinaryTensorSLTwo.representation_uni, BinaryTensorCoefficient.smul_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The actual restricted natural-tensor representation is the additive coefficient representation. -/
def coefficientIso :
    Rep.res (SLTwo.uniHom F) (ambient k I σ) ≅ coefficientRepresentation k I σ hcard :=
  Rep.mkIso (ρ := (Rep.res (SLTwo.uniHom F) (ambient k I σ)).ρ)
    (σ := (coefficientRepresentation k I σ hcard).ρ) <|
    Representation.Equiv.mk
      (ρ := (Rep.res (SLTwo.uniHom F) (ambient k I σ)).ρ)
      (σ := (coefficientRepresentation k I σ hcard).ρ)
      (coefficientLinearEquiv k I σ hcard).symm fun g => by
      apply LinearMap.ext
      intro v
      exact coefficientLinearEquiv_symm_action k I σ hcard g v

@[simp] theorem coefficientIso_hom_apply (v : BinaryTensorCoefficient.Carrier k I) :
    (coefficientIso k I σ hcard).hom.hom v =
      (coefficientLinearEquiv k I σ hcard).symm v := rfl

@[simp] theorem coefficientIso_inv_apply (v : coefficientRepresentation k I σ hcard) :
    (coefficientIso k I σ hcard).inv.hom v = coefficientLinearEquiv k I σ hcard v := rfl

/-- The coefficient isomorphism carries the actual SL2 torus action to the
forward coefficient map used in the ordinary cohomology normalizer action. -/
theorem coefficientIso_torus (r : Fˣ) (v : BinaryTensorCoefficient.Carrier k I) :
    (coefficientIso k I σ hcard).hom.hom ((ambient k I σ).ρ (SLTwo.tor r) v) =
      BinaryAdditiveTorusAction.coefficientLinear k I σ hcard r
        ((coefficientIso k I σ hcard).hom.hom v) := by
  change (coefficientLinearEquiv k I σ hcard).symm
      (BinaryTensorSLTwo.representation k σ I (SLTwo.tor r) v) =
    BinaryAdditiveTorusAction.coefficientLinear k I σ hcard r
      ((coefficientLinearEquiv k I σ hcard).symm v)
  apply (coefficientLinearEquiv k I σ hcard).injective
  rw [LinearEquiv.apply_symm_apply, BinaryAdditiveTorusAction.coefficientLinear_apply,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (BinaryTensorSLTwo.representation_tor k I σ r) v

end Kourovka2135.BinaryTensorSLTwoRestriction
