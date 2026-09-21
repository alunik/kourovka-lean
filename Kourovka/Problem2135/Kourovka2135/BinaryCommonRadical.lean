import Kourovka2135.BinaryQuadraticSurjectivity
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! Vector-valued binary quadratic maps whose nonzero scalar polar forms
have one common proper radical are surjective. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open Classical
variable {V Z : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup Z] [Module (ZMod 2) Z]

/-- On a subspace annihilated by the polar map, a binary quadratic map is linear. -/
def radicalLinearMap (Q : QuadraticMap (ZMod 2) V Z) (T : Submodule (ZMod 2) V)
    (hT : ∀ h ∈ T, ∀ x, Q.polarBilin h x = 0) : T →ₗ[ZMod 2] Z where
  toFun h := Q h
  map_add' h k := by
    change Q ((h : V) + (k : V)) = Q h + Q k
    rw [QuadraticMap.map_add Q]
    change Q (h : V) + Q (k : V) + Q.polarBilin h k = _
    rw [hT h h.property, add_zero]
  map_smul' a h := by
    change Q (a • (h : V)) = a • Q h
    rw [Q.map_smul]
    have ha : a * a = a := by fin_cases a <;> rfl
    rw [ha]

/-- Common proper polar radical suffices; the map need not vanish on that radical. -/
theorem quadratic_surjective_of_common_polar_radical [Fintype V] [Fintype Z]
    (Q : QuadraticMap (ZMod 2) V Z) (T : Submodule (ZMod 2) V) (hTtop : T ≠ ⊤)
    (hcommon : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 → ∀ h : V,
      (∀ x : V, ell (Q.polarBilin h x) = 0) ↔ h ∈ T) :
    Function.Surjective Q := by
  classical
  have hT : ∀ h ∈ T, ∀ x, Q.polarBilin h x = 0 := by
    intro h hh x
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
    intro ell
    by_cases hell : ell = 0
    · simp [hell]
    · exact (hcommon ell hell h).mpr hh x
  let L := radicalLinearMap Q T hT
  let U := LinearMap.range L
  let Qbar : QuadraticMap (ZMod 2) V (Z ⧸ U) := U.mkQ.compQuadraticMap Q
  have hTrad : T ≤ Qbar.radical := by
    intro h hh
    constructor
    · change U.mkQ (Q h) = 0
      apply (Submodule.Quotient.mk_eq_zero U).mpr
      exact ⟨⟨h, hh⟩, rfl⟩
    · apply LinearMap.ext
      intro x
      change Qbar.polarBilin h x = 0
      simp only [Qbar, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        LinearMap.compQuadraticMap_apply, ← map_sub]
      change U.mkQ (Q.polarBilin h x) = 0
      rw [hT h hh x, map_zero]
  let P := Qbar.lift T hTrad
  have hP (h x : V) : P.polarBilin (T.mkQ h) (T.mkQ x) = U.mkQ (Q.polarBilin h x) := by
    simp only [P, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add, Submodule.mkQ_apply, QuadraticMap.lift_mk]
    change U.mkQ (Q (h + x)) - U.mkQ (Q h) - U.mkQ (Q x) = _
    simp only [← map_sub, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rfl
  letI : Finite (V ⧸ T) := Finite.of_surjective T.mkQ T.mkQ_surjective
  letI : Finite (Z ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  letI : Fintype (V ⧸ T) := Fintype.ofFinite _
  letI : Fintype (Z ⧸ U) := Fintype.ofFinite _
  letI : Nontrivial (V ⧸ T) := Submodule.Quotient.nontrivial_iff.mpr hTtop
  have hsurj : Function.Surjective P := by
    apply quadratic_surjective_of_nondegenerate_polar
    intro ell hell h hh
    obtain ⟨a, rfl⟩ := T.mkQ_surjective h
    let psi : Module.Dual (ZMod 2) Z := ell.comp U.mkQ
    have hpsi : psi ≠ 0 := by
      intro he
      apply hell
      apply LinearMap.ext
      intro z
      obtain ⟨b, rfl⟩ := U.mkQ_surjective z
      exact LinearMap.congr_fun he b
    apply (Submodule.Quotient.mk_eq_zero T).mpr
    apply (hcommon psi hpsi a).mp
    intro b
    have hb := hh (T.mkQ b)
    rw [hP] at hb
    exact hb
  intro z
  obtain ⟨v, hv⟩ := hsurj (U.mkQ z)
  obtain ⟨a, rfl⟩ := T.mkQ_surjective v
  have hQa : U.mkQ (Q a) = U.mkQ z := hv
  have hdiff : z - Q a ∈ U := by
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (z - Q a) = 0
    rw [map_sub, hQa, sub_self]
  obtain ⟨t, ht⟩ := hdiff
  refine ⟨(t : V) + a, ?_⟩
  rw [QuadraticMap.map_add Q]
  change Q (t : V) + Q a + Q.polarBilin t a = z
  rw [hT t t.property a, add_zero]
  change Q (t : V) = z - Q a at ht
  rw [ht]
  abel

end Kourovka2135.BinaryFourier
