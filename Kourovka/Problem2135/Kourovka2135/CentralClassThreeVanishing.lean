import Kourovka2135.CentralClassThreePairing
import Kourovka2135.Vendor.CFSG.ElementaryAbelian
import Mathlib.Algebra.Module.ZMod

/-! Convert the actual central class-three pairing to an F2-bilinear map
into central two-torsion. Invariant-form vanishing therefore forces class
at most two. Arbitrary central 2-kernels need not be pushed out to C2. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.CentralClassThreeVanishing

open CentralClassThreePairing
open scoped IsMulCommutative

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- The actual elements of order at most two in the center of G. -/
def centerTwoTorsion (G : Type u) [Group G] : Subgroup (Subgroup.center G) :=
  (powMonoidHom 2 : Subgroup.center G →* Subgroup.center G).ker

instance centerTwoTorsion_isElementaryAbelian :
    IsElementaryAbelian 2 (centerTwoTorsion G) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact x.property

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (pi : G →* Q) (hpi : Function.Surjective pi)
variable (hker : pi.ker ≤ Subgroup.center G)
variable (hQ : commutator Q ≤ Subgroup.center Q)

def pairingRightHom (d : commutator Q) : Abelianization Q →* Subgroup.center G :=
  MonoidHom.mk' (pairingHom pi hpi hker hQ d)
    (pairingHom_mul_right pi hpi hker hQ d)

variable [IsElementaryAbelian 2 (Abelianization Q)]

theorem pairing_square (d : commutator Q) (a : Abelianization Q) :
    pairingHom pi hpi hker hQ d a ^ 2 = 1 := by
  change (pairingRightHom pi hpi hker hQ d a) ^ 2 = 1
  rw [← map_pow]
  have ha : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (Abelianization Q)) a
  rw [ha, map_one]

def pairingTwoRightHom (d : commutator Q) :
    Abelianization Q →* centerTwoTorsion G :=
  (pairingRightHom pi hpi hker hQ d).codRestrict (centerTwoTorsion G) (by
    intro a
    change pairingHom pi hpi hker hQ d a ^ 2 = 1
    exact pairing_square pi hpi hker hQ d a)

def pairingTwoFunctionHom : commutator Q →* (Abelianization Q → centerTwoTorsion G) where
  toFun d := pairingTwoRightHom pi hpi hker hQ d
  map_one' := by
    funext a
    apply Subtype.ext
    exact congrFun (map_one (pairingHom pi hpi hker hQ)) a
  map_mul' d e := by
    funext a
    apply Subtype.ext
    exact congrFun ((pairingHom pi hpi hker hQ).map_mul d e) a

variable [IsElementaryAbelian 2 (commutator Q)]

def rightLinear (d : Additive (commutator Q)) :
    Additive (Abelianization Q) →ₗ[ZMod 2] Additive (centerTwoTorsion G) :=
  ((pairingTwoRightHom pi hpi hker hQ d.toMul).toAdditive).toZModLinearMap 2

/-- The actual triple-commutator pairing is bilinear over F2. Its target
uses only the elements of order at most two, not an exponent assumption on G's kernel. -/
def bilinear : Additive (commutator Q) →ₗ[ZMod 2]
    Additive (Abelianization Q) →ₗ[ZMod 2] Additive (centerTwoTorsion G) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := rightLinear pi hpi hker hQ
    map_zero' := by
      apply LinearMap.ext
      intro a
      change pairingTwoFunctionHom pi hpi hker hQ 1 a.toMul = 1
      exact congrFun (map_one (pairingTwoFunctionHom pi hpi hker hQ)) a.toMul
    map_add' := by
      intro d e
      apply LinearMap.ext
      intro a
      change pairingTwoFunctionHom pi hpi hker hQ (d.toMul * e.toMul) a.toMul =
        pairingTwoFunctionHom pi hpi hker hQ d.toMul a.toMul *
        pairingTwoFunctionHom pi hpi hker hQ e.toMul a.toMul
      exact congrFun ((pairingTwoFunctionHom pi hpi hker hQ).map_mul d.toMul e.toMul) a.toMul }

theorem bilinear_apply_lifts (c : commutator G) (x : G) :
    (((bilinear pi hpi hker hQ (Additive.ofMul (derivedMap pi hpi c))
      (Additive.ofMul (Abelianization.of (pi x)))).toMul : Subgroup.center G) : G) =
        paperCommutator (c : G) x :=
  pairingHom_apply_lifts pi hpi hker hQ c x

theorem bilinear_mem_kernel (d : Additive (commutator Q))
    (a : Additive (Abelianization Q)) :
    (((bilinear pi hpi hker hQ d a).toMul : Subgroup.center G) : G) ∈ pi.ker :=
  pairingHom_mem_kernel pi hpi hker hQ d.toMul a.toMul

def derivedAction (beta : Q ≃* Q) :
    Additive (commutator Q) →ₗ[ZMod 2] Additive (commutator Q) :=
  ((derivedMap beta.toMonoidHom beta.surjective).toAdditive).toZModLinearMap 2

def abelianAction (beta : Q ≃* Q) :
    Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q) :=
  ((Abelianization.map beta.toMonoidHom).toAdditive).toZModLinearMap 2

theorem bilinear_invariant (alpha : G ≃* G) (beta : Q ≃* Q)
    (hcompat : ∀ x, pi (alpha x) = beta (pi x))
    (hfix : ∀ x ∈ pi.ker, alpha x = x)
    (d : Additive (commutator Q)) (a : Additive (Abelianization Q)) :
    bilinear pi hpi hker hQ (derivedAction beta d) (abelianAction beta a) =
      bilinear pi hpi hker hQ d a := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact pairingHom_invariant pi hpi hker hQ alpha beta hcompat hfix d.toMul a.toMul

theorem commutator_le_center_of_bilinear_eq_zero
    (hB : bilinear pi hpi hker hQ = 0) : commutator G ≤ Subgroup.center G := by
  apply commutator_le_center_of_pairing_eq_one pi hpi hker hQ
  intro d a
  have h := congrArg
    (fun B : Additive (commutator Q) →ₗ[ZMod 2]
      Additive (Abelianization Q) →ₗ[ZMod 2] Additive (centerTwoTorsion G) =>
        B (Additive.ofMul d) (Additive.ofMul a)) hB
  exact congrArg (fun z : Additive (centerTwoTorsion G) =>
    (z.toMul : Subgroup.center G)) h

include pi hpi hker hQ in
/-- A generic invariant-bilinear-form exclusion applies to the actual
commutator pairing; it is not assumed as an extension or cohomology statement. -/
theorem commutator_le_center_of_invariant_bilinear_vanishing
    {T : Type w} (alpha : T → G ≃* G) (beta : T → Q ≃* Q)
    (hcompat : ∀ t x, pi (alpha t x) = beta t (pi x))
    (hfix : ∀ t x, x ∈ pi.ker → alpha t x = x)
    (hvanish : ∀ B : Additive (commutator Q) →ₗ[ZMod 2]
      Additive (Abelianization Q) →ₗ[ZMod 2] Additive (centerTwoTorsion G),
      (∀ t d a, B (derivedAction (beta t) d) (abelianAction (beta t) a) = B d a) → B = 0) :
    commutator G ≤ Subgroup.center G := by
  apply commutator_le_center_of_bilinear_eq_zero pi hpi hker hQ
  apply hvanish
  intro t d a
  exact bilinear_invariant pi hpi hker hQ (alpha t) (beta t) (hcompat t) (hfix t) d a

omit [IsElementaryAbelian 2 (commutator Q)] in
include pi hpi hker in
/-- After class two is proved, the elementary abelian quotient-ab forces
the actual derived subgroup upstairs to have exponent two. -/
theorem commutator_isElementaryAbelian_of_derived_central
    (hG : commutator G ≤ Subgroup.center G) : IsElementaryAbelian 2 (commutator G) := by
  apply commutator_isElementaryAbelian_of_powers_central 2 hG
  intro x
  have ha : (Abelianization.of (pi x)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Abelianization Q)) _
  have hq : pi (x ^ 2) ∈ commutator Q := by
    rw [← Abelianization.ker_of Q]
    change Abelianization.of (pi (x ^ 2)) = 1
    simpa only [map_pow] using ha
  rw [← map_commutator_of_surjective pi hpi] at hq
  obtain ⟨c, hc, hcq⟩ := hq
  have hr : c⁻¹ * x ^ 2 ∈ pi.ker := by
    change pi (c⁻¹ * x ^ 2) = 1
    rw [map_mul, map_inv, hcq, inv_mul_cancel]
  have hh := (Subgroup.center G).mul_mem (hG hc) (hker hr)
  simpa only [mul_inv_cancel_left] using hh

end Kourovka2135.CentralClassThreeVanishing
