import Kourovka2135.OddPSLTwoCharacterOrbit
import Kourovka2135.CharacterWeightIndependence
import Kourovka2135.IndependentOrbitMovingRank
import Mathlib.Algebra.Group.TypeTags.Finite

/-! Independent actual torus translates and their moving ranks.

One nonzero nontrivial root-character vector supplies distinct character
vectors along the inverse-square torus orbit. The vectors live in the
supplied representation. No Fourier basis or irreducible classification is
used. A full orbit gives the expected dimension and moving-rank bounds.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoTorusMovingRank

open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart OddPSLTwoCharacterOrbit

variable (F : Type u) [Field F]

def projectiveTorusHom : Fˣ →* Q F := (quotient F).comp (SLTwo.torHom F)

@[simp] theorem projectiveTorusHom_apply (r : Fˣ) :
    projectiveTorusHom F r = quotient F (SLTwo.tor r) := rfl

/-- Equality of inverse-square parameters is exactly equality of unit squares. -/
theorem inverseSquare_eq_iff (r s : Fˣ) :
    ((r⁻¹ : Fˣ) : F) ^ 2 = ((s⁻¹ : Fˣ) : F) ^ 2 ↔ r ^ 2 = s ^ 2 := by
  constructor
  · intro h
    have he : (r⁻¹ : Fˣ) ^ 2 = (s⁻¹ : Fˣ) ^ 2 := Units.ext h
    have hi := congrArg (fun a : Fˣ => a⁻¹) he
    simpa only [← inv_pow, inv_inv] using hi
  · intro h
    have he : (r⁻¹ : Fˣ) ^ 2 = (s⁻¹ : Fˣ) ^ 2 := by
      simpa only [inv_pow] using congrArg (fun a : Fˣ => a⁻¹) h
    exact congrArg Units.val he

theorem power_squares_injective (r : Fˣ) :
    Function.Injective (fun i : Fin (orderOf (r ^ 2)) => (r ^ i.val) ^ 2) := by
  intro i j h
  apply Fin.ext
  change (r ^ i.val) ^ 2 = (r ^ j.val) ^ 2 at h
  rw [pow_right_comm r i.val 2, pow_right_comm r j.val 2] at h
  exact pow_injOn_Iio_orderOf i.isLt j.isLt h

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable (ρ : Representation k (Q F) V)

/-- The actual translate of one coefficient vector by a diagonal torus element. -/
def translate (v : V) (r : Fˣ) : V := ρ (projectiveTorusHom F r) v

theorem translate_ne_zero (v : V) (hv : v ≠ 0) (r : Fˣ) : translate F ρ v r ≠ 0 := by
  intro he
  apply hv
  apply (RepresentationMovingConjugacy.actionEquiv ρ (projectiveTorusHom F r)).injective
  simpa only [RepresentationMovingConjugacy.actionEquiv_apply, map_zero, translate] using he

theorem iterate_translate (v : V) (r s : Fˣ) (n : ℕ) :
    ((ρ (projectiveTorusHom F r)) ^ n) (translate F ρ v s) =
      translate F ρ v (s * r ^ n) := by
  change ((ρ (projectiveTorusHom F r)) ^ n * ρ (projectiveTorusHom F s)) v =
    ρ (projectiveTorusHom F (s * r ^ n)) v
  rw [← map_pow ρ, ← map_pow (projectiveTorusHom F), ← map_mul ρ,
    ← map_mul (projectiveTorusHom F), mul_comm (r ^ n) s]

variable [Fintype F]
variable (χ : Multiplicative F →* kˣ) (v : V)

/-- Distinct actual inverse-square parameters give independent torus translates. -/
theorem translates_linearIndependent {ι : Type*} [Fintype ι]
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ)
    (r : ι → Fˣ) (hr : Function.Injective (fun i => r i ^ 2)) :
    LinearIndependent k (fun i => translate F ρ v (r i)) := by
  let ψ (i : ι) := scaledCharacter χ ((((r i)⁻¹ : Fˣ) : F) ^ 2)
  have hψ : Function.Injective ψ := by
    intro i j he
    apply hr
    apply (inverseSquare_eq_iff F (r i) (r j)).mp
    exact scaledCharacter_injective χ hχ he
  apply CharacterWeightIndependence.linearIndependent_of_characters
    (ρ.comp (unipotentHom F))
    (by simpa only [Fintype.card_multiplicative] using hcard)
    ψ hψ (fun i => translate F ρ v (r i))
    (fun i => translate_ne_zero F ρ v hv (r i))
  intro i g
  exact torus_mem_weightSpace ρ χ (r i) v hweight g

/-- The full square-parameter orbit is an actual independent family. -/
theorem power_translates_linearIndependent
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ) (r : Fˣ) :
    LinearIndependent k (fun i : Fin (orderOf (r ^ 2)) => translate F ρ v (r ^ i.val)) :=
  translates_linearIndependent F ρ χ v hcard hχ hv hweight
    (fun i : Fin (orderOf (r ^ 2)) => r ^ i.val) (power_squares_injective F r)

variable [FiniteDimensional k V]

theorem square_order_le_finrank
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ) (r : Fˣ) :
    orderOf (r ^ 2) ≤ Module.finrank k V := by
  simpa only [Fintype.card_fin] using
    (power_translates_linearIndependent F ρ χ v hcard hχ hv hweight r).fintype_card_le_finrank

/-- All but one vector of the actual square-parameter orbit contribute to moving rank. -/
theorem square_order_sub_one_le_finrank_moving
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ) (r : Fˣ) :
    orderOf (r ^ 2) - 1 ≤ Module.finrank k
      (LinearMap.range (ρ (projectiveTorusHom F r) - LinearMap.id)) := by
  let i₀ : Fin (orderOf (r ^ 2)) := ⟨0, orderOf_pos _⟩
  have he := FinitePermutationMovingRank.card_sub_one_le_finrank_of_orbit
    (ρ (projectiveTorusHom F r))
    (fun i : Fin (orderOf (r ^ 2)) => translate F ρ v (r ^ i.val))
    (power_translates_linearIndependent F ρ χ v hcard hχ hv hweight r) i₀
    (fun i => ⟨i.val, by
      change ((ρ (projectiveTorusHom F r)) ^ i.val) (translate F ρ v (r ^ 0)) = _
      rw [pow_zero, iterate_translate, one_mul]⟩)
  simpa only [Fintype.card_fin] using he

theorem four_le_finrank_moving_of_square_order
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ)
    (r : Fˣ) (hr : 5 ≤ orderOf (r ^ 2)) :
    4 ≤ Module.finrank k (LinearMap.range (ρ (projectiveTorusHom F r) - LinearMap.id)) := by
  have he := square_order_sub_one_le_finrank_moving F ρ χ v hcard hχ hv hweight r
  omega

omit [AddCommGroup V] [Module k V] [FiniteDimensional k V] in
/-- Cyclicity of the actual finite-field unit group supplies a full square orbit. -/
theorem exists_full_square_order (hodd : Odd (Fintype.card F)) :
    ∃ r : Fˣ, orderOf (r ^ 2) = (Fintype.card F - 1) / 2 := by
  classical
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨r, ?_⟩
  have hord : orderOf r = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_eq_fintype_card, Fintype.card_units]
  have heven : 2 ∣ Fintype.card F - 1 := by
    obtain ⟨n, hn⟩ := hodd
    exact ⟨n, by omega⟩
  rw [orderOf_pow, hord, Nat.gcd_eq_right heven]

/-- A single genuine nontrivial root character forces the classical half-field dimension bound. -/
theorem half_field_le_finrank (hodd : Odd (Fintype.card F))
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ) :
    (Fintype.card F - 1) / 2 ≤ Module.finrank k V := by
  obtain ⟨r, hr⟩ := exists_full_square_order F hodd
  rw [← hr]
  exact square_order_le_finrank F ρ χ v hcard hχ hv hweight r

end Kourovka2135.OddPSLTwoTorusMovingRank
