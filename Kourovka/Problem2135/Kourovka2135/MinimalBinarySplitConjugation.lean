import Kourovka2135.BinarySLTwoH1TypeUniqueness
import Kourovka2135.MinimalBinaryNonNaturalFiber
import Kourovka2135.ConjugateCommutatorCorrection

/-! Actual forward conjugation differences for a nonspecial minimal binary kernel.
The natural-module identification is derived from the actual H1 type theorem.
A nonidentity split torus, and each of its conjugates, has no nonzero fixed vector.
No order assumption on a lift is needed. The multiplicative endpoint uses exactly
`conj_g(x) * x⁻¹`, not the inverse action or the opposite commutator convention.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalBinarySplitConjugation

open scoped IsMulCommutative

section Native
variable {F : Type} [Field F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual prime-field natural representation at a split-torus parameter. -/
theorem native_tor_apply (u : Fˣ) (x : Fin 2 → F) :
    BinaryNaturalPrimeField.representation F (SLTwo.tor u) x =
      ![(u : F) * x 0, ((u⁻¹ : Fˣ) : F) * x 1] := by
  simpa only [BinaryNaturalPrimeField.representation,
    GroupCohomologyScalarRestriction.restrict_apply,
    RingHom.id_apply, pow_zero, pow_one] using
    BinaryTensorSLTwo.naturalTwist_tor F (RingHom.id F) 0 u x

/-- Both actual eigenvalues differ from one for a nonidentity torus parameter. -/
theorem native_tor_fixed_eq_zero (u : Fˣ) (hu : u ≠ 1) (x : Fin 2 → F)
    (hx : BinaryNaturalPrimeField.representation F (SLTwo.tor u) x = x) : x = 0 := by
  have hu0 : (u : F) ≠ 1 := fun h => hu (Units.ext h)
  have hui : ((u⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    exact hu (inv_eq_one.mp (Units.ext h))
  rw [native_tor_apply] at hx
  have h0 : (u : F) * x 0 = x 0 := congrFun hx 0
  have h1 : ((u⁻¹ : Fˣ) : F) * x 1 = x 1 := congrFun hx 1
  have hx0 : x 0 = 0 := by
    have h : ((u : F) - 1) * x 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hu0)
  have hx1 : x 1 = 0 := by
    have h : (((u⁻¹ : Fˣ) : F) - 1) * x 1 = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hui)
  funext i
  fin_cases i <;> simp [hx0, hx1]

/-- On the finite native module, the forward difference is a bijection. -/
theorem native_tor_difference_bijective [Finite F] (u : Fˣ) (hu : u ≠ 1) :
    Function.Bijective (BinaryNaturalPrimeField.representation F (SLTwo.tor u) -
      (1 : Module.End (ZMod 2) (Fin 2 → F))) := by
  have hinj : Function.Injective
      (BinaryNaturalPrimeField.representation F (SLTwo.tor u) -
        (1 : Module.End (ZMod 2) (Fin 2 → F))) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply native_tor_fixed_eq_zero u hu x
    exact sub_eq_zero.mp hx
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩
end Native

section Transport
variable {k H V W : Type*} [Field k] [Group H]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Actual intertwining transports surjectivity of the forward difference. -/
theorem difference_surjective_of_equiv (ρ : Representation k H V)
    (σ : Representation k H W) (e : Representation.Equiv ρ σ) (g : H)
    (h : Function.Surjective (ρ g - (1 : Module.End k V))) : Function.Surjective (σ g - (1 : Module.End k W)) := by
  intro w
  obtain ⟨v, hv⟩ := h (e.toLinearEquiv.symm w)
  refine ⟨e v, ?_⟩
  have hi := LinearMap.congr_fun (e.isIntertwining' g) v
  change e (ρ g v) = σ g (e v) at hi
  change σ g (e v) - e v = w
  rw [← hi, ← map_sub]
  exact (congrArg e hv).trans (e.toLinearEquiv.apply_symm_apply w)

/-- Conjugating the acting element preserves surjectivity of its difference. -/
theorem difference_surjective_conjugate (ρ : Representation k H V) (g s : H)
    (h : Function.Surjective (ρ g - (1 : Module.End k V))) :
    Function.Surjective (ρ (s * g * s⁻¹) - (1 : Module.End k V)) := by
  have hcancel (v : V) : ρ s (ρ s⁻¹ v) = v := by
    change (ρ s * ρ s⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hcancel' (v : V) : ρ s⁻¹ (ρ s v) = v := by
    change (ρ s⁻¹ * ρ s) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  intro v
  obtain ⟨x, hx⟩ := h (ρ s⁻¹ v)
  refine ⟨ρ s x, ?_⟩
  change ρ (s * g * s⁻¹) (ρ s x) - ρ s x = v
  rw [map_mul, map_mul]
  change ρ s (ρ g (ρ s⁻¹ (ρ s x))) - ρ s x = v
  rw [hcancel', ← map_sub]
  change ρ s ((ρ g - 1) x) = v
  rw [hx, hcancel]
end Transport

section Minimal
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
variable (hnonspecial : Subgroup.center N ≠ commutator N)
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
local instance minimalPrimeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable (j : SLTwo.SL2 F ≃* (G ⧸ R))
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)

include hN hmin hnonabelian hR hRΦ hnonspecial j f hcard hf in
/-- Actual linear forward differences are onto at every lift of a conjugate split torus.
The elementary-abelian instance in this linear statement is derived internally by
`quotientDifference_surjective` below for the unbundled group endpoint. -/
theorem linear_difference_surjective
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    (u : Fˣ) (hu : u ≠ 1) (s : SLTwo.SL2 F) (g : G)
    (hg : QuotientGroup.mk' R g = j (s * SLTwo.tor u * s⁻¹)) :
    Function.Surjective (normalQuotientRepresentation N (Subgroup.center N) 2 g -
      (1 : Module.End (ZMod 2) (Additive (N ⧸ Subgroup.center N)))) := by
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let : Representation.IsIrreducible (ρ.comp j.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp ρ j
  have hH1 := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hmin R hR hnonabelian hRΦ hnonspecial
  have hH1' : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (ρ.comp j.toMonoidHom)) 1) ≠ 0 := by
    rwa [RepresentationGroupEquiv.finrank_cohomology_comp ρ j 1]
  let e := BinarySLTwoH1TypeUniqueness.naturalEquiv
    (ρ.comp j.toMonoidHom) f hcard hf hH1'
  have hs := difference_surjective_conjugate (BinaryNaturalPrimeField.representation F)
    (SLTwo.tor u) s (native_tor_difference_bijective u hu).2
  have he := difference_surjective_of_equiv (BinaryNaturalPrimeField.representation F)
    (ρ.comp j.toMonoidHom) e (s * SLTwo.tor u * s⁻¹) hs
  change Function.Surjective (ρ (j (s * SLTwo.tor u * s⁻¹)) -
    (1 : Module.End (ZMod 2) (Additive (N ⧸ Subgroup.center N)))) at he
  rw [← hg] at he
  exact he

include hN hmin hnonabelian hR hRΦ hnonspecial j f hcard hf in
/-- The actual quotient difference is surjective, with no chosen module structure
and no order assumption on the lift. Conjugates of split torus elements are allowed. -/
theorem quotientDifference_surjective
    (u : Fˣ) (hu : u ≠ 1) (s : SLTwo.SL2 F) (g : G)
    (hg : QuotientGroup.mk' R g = j (s * SLTwo.tor u * s⁻¹)) :
    Function.Surjective (ConjugateCommutatorCorrection.quotientDifference N g) := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  exact ConjugateCommutatorCorrection.surjective_quotientDifference_of_linear N 2 g
    (linear_difference_surjective N hN hmin hnonabelian R hR hRΦ hnonspecial
      j f hcard hf u hu s g hg)

include hN hmin hnonabelian hR hRΦ hnonspecial j f hcard hf in
/-- The same actual difference is a bijection of the finite quotient. -/
theorem quotientDifference_bijective
    (u : Fˣ) (hu : u ≠ 1) (s : SLTwo.SL2 F) (g : G)
    (hg : QuotientGroup.mk' R g = j (s * SLTwo.tor u * s⁻¹)) :
    Function.Bijective (ConjugateCommutatorCorrection.quotientDifference N g) := by
  have h := quotientDifference_surjective N hN hmin hnonabelian R hR hRΦ hnonspecial
    j f hcard hf u hu s g hg
  exact h.bijective_of_finite

include hN hmin hnonabelian hR hRΦ hnonspecial j f hcard hf in
/-- Direct-torus specialization in the inverse-quotient coordinates used by the trace theorem. -/
theorem quotientDifference_surjective_of_torus
    (u : Fˣ) (hu : u ≠ 1) (g : G)
    (hg : j.symm (QuotientGroup.mk' R g) = SLTwo.tor u) :
    Function.Surjective (ConjugateCommutatorCorrection.quotientDifference N g) := by
  apply quotientDifference_surjective N hN hmin hnonabelian R hR hRΦ hnonspecial
    j f hcard hf u hu 1 g
  simpa only [one_mul, inv_one, mul_one, j.apply_symm_apply] using congrArg j hg

include hmin hnonabelian in
omit [Finite G] [Group.IsPerfect G] in
/-- The internal center is genuinely central in the ambient group; no action premise is added. -/
theorem center_le_ambient_center :
    (Subgroup.center N).map N.subtype ≤ Subgroup.center G :=
  minimal_noncentral_center_le N hnonabelian hmin
end Minimal

end Kourovka2135.MinimalBinarySplitConjugation
