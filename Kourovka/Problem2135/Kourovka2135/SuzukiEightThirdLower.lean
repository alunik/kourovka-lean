import Kourovka2135.SuzukiRootDerivedTorus
import Kourovka2135.CentralClassTwoOddAverage
import Kourovka2135.CentralClassThreePairing
import Kourovka2135.InvariantBiadditiveCoordinates

/-! The kernel of a torus-equivariant central extension of the actual
Suzuki root group over F8, lying in the derived subgroup, is exactly the
third lower-central subgroup. The quotient and its torus action are actual
constructions; no class-two assumption on the original extension is made. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightThirdLower

open CentralClassThreePairing
open SuzukiGeometry SuzukiRootDerivedCoordinates SuzukiRootDerivedTorus
open scoped IsMulCommutative commutatorElement

variable {P Q T : Type*} [Group P] [Group Q] [Group T]

abbrev third (P : Type*) [Group P] : Subgroup P := ⁅commutator P, ⊤⁆
abbrev ClassTwoQuotient (P : Type*) [Group P] := P ⧸ third P

/-- The genuine third lower-central quotient has class at most two. -/
theorem quotient_commutator_le_center :
    commutator (ClassTwoQuotient P) ≤ Subgroup.center (ClassTwoQuotient P) := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  calc
    ⁅commutator (ClassTwoQuotient P), ⊤⁆ =
        (third P).map (QuotientGroup.mk' (third P)) := by
      rw [Subgroup.map_commutator,
        map_commutator_of_surjective _ (QuotientGroup.mk'_surjective _),
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    _ = ⊥ := QuotientGroup.map_mk'_self (third P)

variable (pi : P →* Q) (hpi : Function.Surjective pi)
variable (hQ : commutator Q ≤ Subgroup.center Q)

include hpi hQ in
theorem third_le_kernel : third P ≤ pi.ker := by
  apply Subgroup.commutator_le.mpr
  intro c hc x _
  change pi ⁅c, x⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact (show Commute (pi x) (pi c) from
    Subgroup.mem_center_iff.mp (hQ (derivedMap pi hpi ⟨c, hc⟩).property) (pi x)).symm

/-- The actual map from the third lower-central quotient to Q. -/
def quotientProjection : ClassTwoQuotient P →* Q :=
  QuotientGroup.lift (third P) pi (third_le_kernel pi hpi hQ)

@[simp] theorem quotientProjection_mk (x : P) :
    quotientProjection pi hpi hQ (QuotientGroup.mk' (third P) x) = pi x := rfl

theorem quotientProjection_surjective : Function.Surjective (quotientProjection pi hpi hQ) := by
  intro q
  obtain ⟨x, rfl⟩ := hpi q
  exact ⟨QuotientGroup.mk' (third P) x, rfl⟩

include hpi hQ in
theorem quotientProjection_kernel_central (hker : pi.ker ≤ Subgroup.center P) :
    (quotientProjection pi hpi hQ).ker ≤ Subgroup.center (ClassTwoQuotient P) := by
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (third P) x
  have hxpi : x ∈ pi.ker := hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (third P) y
  exact congrArg (QuotientGroup.mk' (third P)) (Subgroup.mem_center_iff.mp (hker hxpi) y)

/-- Characteristicity gives the quotient automorphism for every actual automorphism. -/
def quotientAut (a : MulAut P) : MulAut (ClassTwoQuotient P) :=
  QuotientGroup.congr (third P) (third P) a
    (Subgroup.characteristic_iff_map_eq.mp inferInstance a)

@[simp] theorem quotientAut_mk (a : MulAut P) (x : P) :
    quotientAut a (QuotientGroup.mk' (third P) x) = QuotientGroup.mk' (third P) (a x) := rfl

/-- The quotient action is a genuine group homomorphism. -/
def quotientAction (alpha : T →* MulAut P) : T →* MulAut (ClassTwoQuotient P) where
  toFun t := quotientAut (alpha t)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (third P) x
    change QuotientGroup.mk' (third P) (alpha 1 x) = QuotientGroup.mk' (third P) x
    rw [map_one]
    rfl
  map_mul' t s := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (third P) x
    change QuotientGroup.mk' (third P) (alpha (t * s) x) =
      QuotientGroup.mk' (third P) (alpha t (alpha s x))
    rw [map_mul]
    rfl

@[simp] theorem quotientAction_mk (alpha : T →* MulAut P) (t : T) (x : P) :
    quotientAction alpha t (QuotientGroup.mk' (third P) x) =
      QuotientGroup.mk' (third P) (alpha t x) := rfl

include hpi in
/-- The preimage of an abelianization under a central class-two extension is central. -/
theorem abelianization_kernel_central (hker : pi.ker ≤ Subgroup.center P)
    (hD : commutator P ≤ Subgroup.center P) :
    ((Abelianization.of : Q →* Abelianization Q).comp pi).ker ≤ Subgroup.center P := by
  intro x hx
  have hxQ : pi x ∈ commutator Q := by
    rw [← Abelianization.ker_of Q]
    exact hx
  rw [← map_commutator_of_surjective pi hpi] at hxQ
  obtain ⟨c, hc, hcx⟩ := hxQ
  have hr : c⁻¹ * x ∈ pi.ker := by
    change pi (c⁻¹ * x) = 1
    rw [map_mul, map_inv, hcx, inv_mul_cancel]
  have h := (Subgroup.center P).mul_mem (hD hc) (hker hr)
  simpa only [mul_inv_cancel_left] using h

/-- The full local kernel is exactly the third lower-central subgroup at q=8. -/
theorem kernel_eq_third (phi : P →* U 1) (hphi : Function.Surjective phi)
    (hcentral : phi.ker ≤ Subgroup.center P) (hderived : phi.ker ≤ commutator P)
    (alpha : (K 1)ˣ →* MulAut P)
    (hcompat : ∀ t x, phi (alpha t x) = rootTorusAut 1 t (phi x))
    (hfix : ∀ t x, x ∈ phi.ker → alpha t x = x) : phi.ker = third P := by
  let pbar : ClassTwoQuotient P →* U 1 :=
    quotientProjection phi hphi (SuzukiRootDerivedCoordinates.commutator_le_center 1)
  have hpbar : Function.Surjective pbar := quotientProjection_surjective _ _ _
  have hpcentral : pbar.ker ≤ Subgroup.center (ClassTwoQuotient P) :=
    quotientProjection_kernel_central _ _ _ hcentral
  have hpD : commutator (ClassTwoQuotient P) ≤ Subgroup.center (ClassTwoQuotient P) :=
    quotient_commutator_le_center
  let psi : ClassTwoQuotient P →* Abelianization (U 1) :=
    (Abelianization.of : U 1 →* Abelianization (U 1)).comp pbar
  have hpsi : Function.Surjective psi := abelianization_surjective.comp hpbar
  have hpsiker : psi.ker ≤ Subgroup.center (ClassTwoQuotient P) :=
    abelianization_kernel_central pbar hpbar hpcentral hpD
  let : IsElementaryAbelian 2 (Abelianization (U 1)) := abelianization_isElementaryAbelian 1 (by decide)
  let : IsElementaryAbelian 2 (commutator (ClassTwoQuotient P)) :=
    CentralClassTwoAbelianPairing.derived_isElementaryAbelian psi hpsi hpsiker hpD
  let : Fintype (K 1)ˣ := Fintype.ofFinite (K 1)ˣ
  let beta := abelianizationTorusAction 1
  have hcompatbar : ∀ t x, psi (quotientAction alpha t x) = beta t (psi x) := by
    intro t x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (third P) x
    change Abelianization.of (phi (alpha t x)) = Abelianization.of (rootTorusAut 1 t (phi x))
    rw [hcompat]
  have hodd : Odd (Nat.card (K 1)ˣ) := by
    rw [Nat.card_units, SuzukiTorusMovingRank.card_field]
    norm_num
  have hvanish : ∀ B : Additive (Abelianization (U 1)) →+
      (Additive (Abelianization (U 1)) →+ Additive (commutator (ClassTwoQuotient P))),
      (∀ t x y, B ((beta t).toAdditive x) ((beta t).toAdditive y) = B x y) → B = 0 := by
    intro B hB
    apply InvariantBiadditiveCoordinates.eq_zero 1 (by decide)
      (ScalarPowerAdditivity.inverse_power_not_additive 1 (by decide) (by
        rw [SuzukiTorusMovingRank.card_field]
        norm_num))
      (abelianizationAddEquiv 1 (by decide)) (abelianizationAddEquiv 1 (by decide))
      (fun t x => (beta t).toAdditive x) (fun t x => (beta t).toAdditive x) ?_ ?_ B hB
    · intro t x
      change abelianizationAddEquiv 1 _
        (Additive.ofMul (abelianizationTorusAction 1 t x.toMul)) =
          (t : K 1) ^ 1 * abelianizationAddEquiv 1 _ x
      rw [pow_one]
      exact abelianizationAddEquiv_torus 1 (by decide) t x
    · intro t x
      exact abelianizationAddEquiv_torus 1 (by decide) t x
  apply le_antisymm ?_ (third_le_kernel phi hphi (SuzukiRootDerivedCoordinates.commutator_le_center 1))
  intro r hr
  have hrD : QuotientGroup.mk' (third P) r ∈ commutator (ClassTwoQuotient P) := by
    rw [← map_commutator_of_surjective _ (QuotientGroup.mk'_surjective (third P))]
    exact Subgroup.mem_map_of_mem _ (hderived hr)
  have hrfix : ∀ t, quotientAction alpha t (QuotientGroup.mk' (third P) r) =
      QuotientGroup.mk' (third P) r := by
    intro t
    rw [quotientAction_mk, hfix t r hr]
  have hrone := CentralClassTwoOddAverage.fixed_mem_commutator_eq_one
    psi hpsi hpsiker hpD (quotientAction alpha) beta hcompatbar hodd hvanish
    (QuotientGroup.mk' (third P) r) hrD hrfix
  exact (QuotientGroup.eq_one_iff r).mp hrone

end Kourovka2135.SuzukiEightThirdLower
