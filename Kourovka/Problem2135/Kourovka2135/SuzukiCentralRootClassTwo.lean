import Kourovka2135.SuzukiRootDerivedTorus
import Kourovka2135.CentralClassThreeVanishing
import Kourovka2135.InvariantBiadditiveCoordinates

/-! A central extension of the full Suzuki root subgroup has class at most
two whenever the actual split torus lifts fixing its kernel and q >= 32.
The torus action is an explicit input here; the ambient-cover application
must construct it by lift-independent conjugation. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiCentralRootClassTwo

open SuzukiGeometry SuzukiRootDerivedCoordinates SuzukiRootDerivedTorus
open CentralClassThreeVanishing
open scoped IsMulCommutative

/-- The concrete root-count threshold for the two Suzuki root weights. -/
theorem inverse_weight_threshold (m : ℕ) (hm : 2 ≤ m) :
    2 * (1 + 2 ^ (m + 1)) + 2 < Nat.card (K m) := by
  rw [SuzukiTorusMovingRank.card_field]
  have hsmall : 8 ≤ 2 ^ (m + 1) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ m + 1 by omega)
    norm_num at h
    exact h
  have hlarge : 4 * 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) := by
    calc
      4 * 2 ^ (m + 1) = 2 ^ ((m + 1) + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The induced derived action is the actual restricted torus conjugation. -/
theorem derivedAction_eq (m : ℕ) (u : (K m)ˣ) (d : Additive (commutator (U m)))
    [IsElementaryAbelian 2 (commutator (U m))] :
    derivedAction (rootTorusAut m u) d = Additive.ofMul (derivedTorusAction m u d.toMul) := rfl

/-- The induced action on the actual abelianization agrees with the quotient action. -/
theorem abelianAction_eq (m : ℕ) (u : (K m)ˣ) (a : Additive (Abelianization (U m)))
    [IsElementaryAbelian 2 (Abelianization (U m))] :
    abelianAction (rootTorusAut m u) a =
      Additive.ofMul (abelianizationTorusAction m u a.toMul) := rfl

/-- No invariant biadditive form exists between the actual derived and
abelianized root modules when m >= 2. -/
theorem invariant_form_eq_zero {A : Type*} [AddCommGroup A]
    (m : ℕ) (hm : 2 ≤ m)
    (B : Additive (commutator (U m)) →+ (Additive (Abelianization (U m)) →+ A))
    (hB : ∀ u d a,
      B (Additive.ofMul (derivedTorusAction m u d.toMul))
        (Additive.ofMul (abelianizationTorusAction m u a.toMul)) = B d a) : B = 0 := by
  let : IsElementaryAbelian 2 (commutator (U m)) := derived_isElementaryAbelian m
  exact InvariantBiadditiveCoordinates.eq_zero (1 + 2 ^ (m + 1)) (by positivity)
    (ScalarPowerAdditivity.inverse_power_not_additive _ (by positivity) (inverse_weight_threshold m hm))
    (derivedAddEquiv m (by omega)) (abelianizationAddEquiv m (by omega))
    (fun u d => Additive.ofMul (derivedTorusAction m u d.toMul))
    (fun u a => Additive.ofMul (abelianizationTorusAction m u a.toMul))
    (derivedAddEquiv_torus m (by omega)) (abelianizationAddEquiv_torus m (by omega)) B hB

/-- Actual kernel-fixed torus lifts force a central root extension to have class two. -/
theorem commutator_le_center {P : Type*} [Group P] (m : ℕ) (hm : 2 ≤ m)
    (pi : P →* U m) (hpi : Function.Surjective pi)
    (hker : pi.ker ≤ Subgroup.center P) (alpha : (K m)ˣ → P ≃* P)
    (hcompat : ∀ u x, pi (alpha u x) = rootTorusAut m u (pi x))
    (hfix : ∀ u x, x ∈ pi.ker → alpha u x = x) : commutator P ≤ Subgroup.center P := by
  let : IsElementaryAbelian 2 (commutator (U m)) := derived_isElementaryAbelian m
  let : IsElementaryAbelian 2 (Abelianization (U m)) := abelianization_isElementaryAbelian m (by omega)
  apply commutator_le_center_of_invariant_bilinear_vanishing pi hpi hker
    (SuzukiRootDerivedCoordinates.commutator_le_center m) alpha (rootTorusAut m) hcompat hfix
  intro B hB
  let C : Additive (commutator (U m)) →+
      (Additive (Abelianization (U m)) →+ Additive (centerTwoTorsion P)) :=
    { toFun := fun d => (B d).toAddMonoidHom
      map_zero' := by ext a; simp
      map_add' := by intro d e; ext a; simp }
  have hC : C = 0 := by
    apply invariant_form_eq_zero m hm
    intro u d a
    exact hB u d a
  apply LinearMap.ext
  intro d
  apply LinearMap.ext
  intro a
  exact congrArg (fun C : Additive (commutator (U m)) →+
      (Additive (Abelianization (U m)) →+ Additive (centerTwoTorsion P)) => C d a) hC

end Kourovka2135.SuzukiCentralRootClassTwo
