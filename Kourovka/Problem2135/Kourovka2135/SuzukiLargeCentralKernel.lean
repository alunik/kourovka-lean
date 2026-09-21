import Kourovka2135.SuzukiCentralPreimage
import Kourovka2135.CentralClassTwoOddAverage

/-! Central binary kernels above the actual Suzuki group are trivial for
q >= 32. The proof combines transfer, the actual scalar root coordinates,
class-three pairing vanishing, and an odd-order norm of the commutator
pairing. No multiplier, cohomology, or representation assumption appears. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiLargeCentralKernel

open SuzukiGeometry SuzukiRootDerivedCoordinates SuzukiRootDerivedTorus
open scoped IsMulCommutative

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- Every finite perfect central binary cover of the actual Suzuki matrix
group is trivial above the quotient when m>=2. -/
theorem ker_eq_bot (m : ℕ) (hm : 2 ≤ m)
    (pi : E →* G m) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E) (hbinary : IsPGroup 2 pi.ker) : pi.ker = ⊥ := by
  classical
  let P := SuzukiCentralPreimage.P m pi
  let phi : P →* U m := SuzukiCentralPreimage.projection m pi
  have hphi : Function.Surjective phi := CentralPreimageAction.projection_surjective pi hpi (root m)
  have hphiker : phi.ker ≤ Subgroup.center P := CentralPreimageAction.projection_kernel_central pi hcentral (root m)
  have hD : commutator P ≤ Subgroup.center P := SuzukiCentralPreimage.commutator_le_center m pi hpi hcentral hm
  let psi : P →* Abelianization (U m) := (Abelianization.of : U m →* Abelianization (U m)).comp phi
  have hpsi : Function.Surjective psi :=
    (CentralClassThreePairing.abelianization_surjective (Q := U m)).comp hphi
  have hpsiker : psi.ker ≤ Subgroup.center P := by
    intro x hx
    have hxQ : phi x ∈ commutator (U m) := by
      rw [← Abelianization.ker_of (U m)]
      exact hx
    rw [← CentralClassThreePairing.map_commutator_of_surjective phi hphi] at hxQ
    obtain ⟨c, hc, hcx⟩ := hxQ
    have hr : c⁻¹ * x ∈ phi.ker := by
      change phi (c⁻¹ * x) = 1
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have h := (Subgroup.center P).mul_mem (hD hc) (hphiker hr)
    simpa only [mul_inv_cancel_left] using h
  let : IsElementaryAbelian 2 (Abelianization (U m)) := abelianization_isElementaryAbelian m (by omega)
  let : IsElementaryAbelian 2 (commutator P) :=
    CentralClassTwoAbelianPairing.derived_isElementaryAbelian psi hpsi hpsiker hD
  let : Fintype (K m)ˣ := Fintype.ofFinite (K m)ˣ
  let alpha : (K m)ˣ →* MulAut P := SuzukiCentralPreimage.torusAction m pi hpi hcentral
  let beta : (K m)ˣ →* MulAut (Abelianization (U m)) := abelianizationTorusAction m
  have hcompat : ∀ t x, psi (alpha t x) = beta t (psi x) := by
    intro t x
    change Abelianization.of (phi (alpha t x)) = Abelianization.of (rootTorusAut m t (phi x))
    rw [SuzukiCentralPreimage.torusAction_projection]
  have hodd : Odd (Nat.card (K m)ˣ) := by
    rw [Nat.card_units, SuzukiTorusMovingRank.card_field]
    exact Nat.Even.sub_odd (Nat.le_of_lt (one_lt_q m)) (even_q m) (by decide)
  have hvanish : ∀ B : Additive (Abelianization (U m)) →+
      (Additive (Abelianization (U m)) →+ Additive (commutator P)),
      (∀ t x y, B ((beta t).toAdditive x) ((beta t).toAdditive y) = B x y) → B = 0 := by
    intro B hB
    apply InvariantBiadditiveCoordinates.eq_zero 1 (by decide)
      (ScalarPowerAdditivity.inverse_power_not_additive 1 (by decide) (by
        have h := SuzukiCentralRootClassTwo.inverse_weight_threshold m hm
        omega))
      (abelianizationAddEquiv m (by omega)) (abelianizationAddEquiv m (by omega))
      (fun t x => (beta t).toAdditive x) (fun t x => (beta t).toAdditive x) ?_ ?_ B hB
    · intro t x
      change abelianizationAddEquiv m _
        (Additive.ofMul (abelianizationTorusAction m t x.toMul)) =
          (t : K m) ^ 1 * abelianizationAddEquiv m _ x
      rw [pow_one]
      exact abelianizationAddEquiv_torus m (by omega) t x
    · intro t x
      exact abelianizationAddEquiv_torus m (by omega) t x
  have htransfer := SuzukiCentralPreimage.kernel_le_commutator_map m pi hpi hcentral hbinary
  apply bot_unique
  intro r hr
  have hrP : r ∈ P := by change pi r ∈ root m; rw [hr]; exact (root m).one_mem
  let x : P := ⟨r, hrP⟩
  have hxphi : x ∈ phi.ker := Subtype.ext hr
  have hxD : x ∈ commutator P := by
    obtain ⟨c, hc, hcr⟩ := htransfer hr
    have he : c = x := Subtype.ext hcr
    exact he ▸ hc
  have hxfix : ∀ t : (K m)ˣ, alpha t x = x := fun t =>
    SuzukiCentralPreimage.torusAction_fixes_kernel m pi hpi hcentral t x hxphi
  have hx1 : x = 1 := CentralClassTwoOddAverage.fixed_mem_commutator_eq_one
    psi hpsi hpsiker hD alpha beta hcompat hodd hvanish x hxD hxfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1)

end Kourovka2135.SuzukiLargeCentralKernel
