import Kourovka2135.OddPSLTwoBorel
import Kourovka2135.PermutationCharacterMultiplicity
import Kourovka2135.RepresentationMovingConjugacy

/-! Actual root-character spaces and their torus transport.

A nontrivial additive character distinguishes all scalar multiples of its
parameter. Conjugation by the actual diagonal torus transports a root-character
space by the inverse-square parameter. Weighted projectors identify the honest
character space with their range when the root-group order is invertible.
This also gives multiplicity at most one in the actual permutation heart,
without choosing a Fourier basis or classifying irreducible modules.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoCharacterOrbit

section CharacterSpace

variable {k U V : Type u} [Field k] [Group U] [AddCommGroup V] [Module k V]
variable (ρ : Representation k U V) (χ : U →* kˣ)

/-- The actual common character subspace in the supplied representation. -/
def weightSpace : Submodule k V where
  carrier := {v | ∀ g : U, ρ g v = (χ g : k) • v}
  zero_mem' := by intro g; rw [map_zero, smul_zero]
  add_mem' hv hw := by intro g; rw [map_add, hv g, hw g, smul_add]
  smul_mem' c v hv := by intro g; rw [map_smul, hv g, smul_comm]

@[simp] theorem mem_weightSpace (v : V) :
    v ∈ weightSpace ρ χ ↔ ∀ g : U, ρ g v = (χ g : k) • v := Iff.rfl

/-- Coprime weighted averaging has exactly the genuine character space as its range. -/
theorem weightSpace_eq_projector_range [Fintype U] (hcard : (Fintype.card U : k) ≠ 0) :
    weightSpace ρ χ = LinearMap.range (WeightedCharacterProjector.projector ρ χ) := by
  ext v
  constructor
  · intro hv
    exact ⟨v, WeightedCharacterProjector.projector_eq_self ρ χ hcard v hv⟩
  · rintro ⟨v, rfl⟩ g
    exact WeightedCharacterProjector.action_projector ρ χ g v

end CharacterSpace

section Parameter

variable {F k : Type u} [Field F] [Field k]

/-- Multiplication of the additive root parameter by an actual field scalar. -/
def scaleHom (a : F) : Multiplicative F →* Multiplicative F where
  toFun t := Multiplicative.ofAdd (a * t.toAdd)
  map_one' := by change Multiplicative.ofAdd (a * 0) = Multiplicative.ofAdd 0; rw [mul_zero]
  map_mul' t s := congrArg Multiplicative.ofAdd (mul_add a t.toAdd s.toAdd)

@[simp] theorem scaleHom_apply (a t : F) :
    scaleHom a (Multiplicative.ofAdd t) = Multiplicative.ofAdd (a * t) := rfl

def scaledCharacter (χ : Multiplicative F →* kˣ) (a : F) : Multiplicative F →* kˣ :=
  χ.comp (scaleHom a)

@[simp] theorem scaledCharacter_apply (χ : Multiplicative F →* kˣ) (a t : F) :
    scaledCharacter χ a (Multiplicative.ofAdd t) = χ (Multiplicative.ofAdd (a * t)) := rfl

@[simp] theorem scaledCharacter_one (χ : Multiplicative F →* kˣ) :
    scaledCharacter χ 1 = χ := by
  apply MonoidHom.ext
  intro t
  change χ (Multiplicative.ofAdd (1 * t.toAdd)) = χ t
  rw [one_mul]
  rfl

@[simp] theorem scaledCharacter_zero (χ : Multiplicative F →* kˣ) :
    scaledCharacter χ 0 = 1 := by
  apply MonoidHom.ext
  intro t
  change χ (Multiplicative.ofAdd (0 * t.toAdd)) = 1
  rw [zero_mul]
  exact map_one χ

theorem scaledCharacter_mul (χ : Multiplicative F →* kˣ) (a b : F) :
    scaledCharacter (scaledCharacter χ a) b = scaledCharacter χ (a * b) := by
  apply MonoidHom.ext
  intro t
  change χ (Multiplicative.ofAdd (a * (b * t.toAdd))) =
    χ (Multiplicative.ofAdd ((a * b) * t.toAdd))
  rw [mul_assoc]

/-- No trace-form description of additive characters is needed to distinguish scalars. -/
theorem scaledCharacter_injective (χ : Multiplicative F →* kˣ) (hχ : χ ≠ 1) :
    Function.Injective (scaledCharacter χ) := by
  intro a b hab
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  apply hχ
  apply MonoidHom.ext
  intro t
  let x : F := (a - b)⁻¹ * t.toAdd
  have he := congrArg (fun ψ : Multiplicative F →* kˣ => ψ (Multiplicative.ofAdd x)) hab
  change χ (Multiplicative.ofAdd (a * x)) = χ (Multiplicative.ofAdd (b * x)) at he
  have hzero : χ (Multiplicative.ofAdd ((a - b) * x)) = 1 := by
    rw [sub_mul, sub_eq_add_neg]
    change χ (Multiplicative.ofAdd (a * x) * (Multiplicative.ofAdd (b * x))⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hx : (a - b) * x = t.toAdd := by
    dsimp [x]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [hx] at hzero
  exact hzero

theorem scaledCharacter_eq_iff (χ : Multiplicative F →* kˣ) (hχ : χ ≠ 1) (a b : F) :
    scaledCharacter χ a = scaledCharacter χ b ↔ a = b :=
  (scaledCharacter_injective χ hχ).eq_iff

theorem scaledCharacter_ne_one (χ : Multiplicative F →* kˣ) (hχ : χ ≠ 1)
    (a : F) (ha : a ≠ 0) : scaledCharacter χ a ≠ 1 := by
  intro he
  apply ha
  apply scaledCharacter_injective χ hχ
  rw [he, scaledCharacter_zero]

end Parameter

section Torus

open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart

variable {F k V : Type u} [Field F] [Field k] [AddCommGroup V] [Module k V]
variable (ρ : Representation k (Q F) V) (χ : Multiplicative F →* kˣ)

theorem root_torus_commutation (r : Fˣ) (t : F) :
    quotient F (SLTwo.uni t) * quotient F (SLTwo.tor r) =
      quotient F (SLTwo.tor r) * quotient F (SLTwo.uni ((((r⁻¹ : Fˣ) : F) ^ 2) * t)) := by
  have hscale : (r : F) ^ 2 * ((r⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
  have he := congrArg (fun g : SLTwo.SL2 F => g * SLTwo.tor r)
    (SLTwo.tor_conj_uni r ((((r⁻¹ : Fˣ) : F) ^ 2) * t))
  rw [mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, hscale, one_mul] at he
  simpa only [map_mul] using (congrArg (quotient F) he).symm

/-- The direction is inverse square: u(t) T(r) = T(r) u(r^-2 t). -/
theorem torus_mem_weightSpace (r : Fˣ) (v : V)
    (hv : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ) :
    ρ (quotient F (SLTwo.tor r)) v ∈
      weightSpace (ρ.comp (unipotentHom F)) (scaledCharacter χ (((r⁻¹ : Fˣ) : F) ^ 2)) := by
  intro t
  change ρ (quotient F (SLTwo.uni t.toAdd)) (ρ (quotient F (SLTwo.tor r)) v) =
    (χ (Multiplicative.ofAdd (((r⁻¹ : Fˣ) : F) ^ 2 * t.toAdd)) : k) •
      ρ (quotient F (SLTwo.tor r)) v
  calc
    _ = ρ (quotient F (SLTwo.tor r))
        (ρ (quotient F (SLTwo.uni (((r⁻¹ : Fˣ) : F) ^ 2 * t.toAdd))) v) := by
      change (ρ _ * ρ _) v = (ρ _ * ρ _) v
      rw [← map_mul ρ, ← map_mul ρ, root_torus_commutation]
    _ = _ := by
      have he := hv (Multiplicative.ofAdd (((r⁻¹ : Fˣ) : F) ^ 2 * t.toAdd))
      change ρ (quotient F (SLTwo.uni (((r⁻¹ : Fˣ) : F) ^ 2 * t.toAdd))) v = _ at he
      rw [he, map_smul]

/-- Torus transport maps onto the entire inverse-square character space. -/
theorem torus_weightSpace_map (r : Fˣ) :
    (weightSpace (ρ.comp (unipotentHom F)) χ).map (ρ (quotient F (SLTwo.tor r))) =
      weightSpace (ρ.comp (unipotentHom F)) (scaledCharacter χ (((r⁻¹ : Fˣ) : F) ^ 2)) := by
  have hscale : ((r⁻¹ : Fˣ) : F) ^ 2 * (r : F) ^ 2 = 1 := by
    rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact torus_mem_weightSpace ρ χ r w hw
  · intro hv
    refine ⟨ρ (quotient F (SLTwo.tor r⁻¹)) v, ?_, ?_⟩
    · have he := torus_mem_weightSpace ρ (scaledCharacter χ (((r⁻¹ : Fˣ) : F) ^ 2))
        r⁻¹ v hv
      rw [inv_inv, scaledCharacter_mul, hscale, scaledCharacter_one] at he
      change ∀ g : Multiplicative F,
        ρ (unipotentHom F g) (ρ (quotient F (SLTwo.tor r⁻¹)) v) =
          (χ g : k) • ρ (quotient F (SLTwo.tor r⁻¹)) v
      intro g
      exact he g
    · change (ρ (quotient F (SLTwo.tor r)) * ρ (quotient F (SLTwo.tor r⁻¹))) v = v
      rw [← map_mul ρ, ← map_mul (quotient F), ← SLTwo.tor_inv, mul_inv_cancel,
        map_one, map_one]
      rfl

/-- Dimensions of honest character spaces are constant along the torus orbit. -/
theorem finrank_weightSpace_torus (r : Fˣ) :
    Module.finrank k (weightSpace (ρ.comp (unipotentHom F)) χ) =
      Module.finrank k (weightSpace (ρ.comp (unipotentHom F))
        (scaledCharacter χ (((r⁻¹ : Fˣ) : F) ^ 2))) := by
  have he := (RepresentationMovingConjugacy.actionEquiv ρ (quotient F (SLTwo.tor r))).finrank_map_eq
    (weightSpace (ρ.comp (unipotentHom F)) χ)
  rw [RepresentationMovingConjugacy.actionEquiv_toLinearMap, torus_weightSpace_map] at he
  exact he.symm

end Torus

section Heart

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]
variable (U : Subgroup G) [Fintype U] (χ : U →* kˣ)

/-- The actual heart has at most one dimension of any nontrivial root character. -/
theorem heart_weightSpace_finrank_le_one (hcard : (Fintype.card X : k) = 0)
    (horder : (Fintype.card U : k) ≠ 0) (x₀ x₁ : X) (hχ : χ ≠ 1)
    (hfix : U ≤ MulAction.stabilizer G x₀) (hx₁ : x₁ ≠ x₀)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Module.finrank k (weightSpace
      ((FinitePermutationHeart.representation k G X hcard).comp U.subtype) χ) ≤ 1 := by
  rw [weightSpace_eq_projector_range _ χ horder]
  exact PermutationCharacterMultiplicity.heart_projector_finrank_le_one
    k G X U χ hcard x₀ x₁ hχ hfix hx₁ htrans

end Heart

end Kourovka2135.OddPSLTwoCharacterOrbit
