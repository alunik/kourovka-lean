import Kourovka2135.SuzukiEightCentralPairing
import Kourovka2135.SuzukiEightThirdLower
import Kourovka2135.SuzukiCentralPreimage

/-! The actual local central kernel at q=8 is the range of an explicit
additive-parameter homomorphism. Triple commutators generate that range,
and Hall-Witt forces its cardinal to be at most four. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightCentralKernel

open SuzukiGeometry SuzukiRootDerivedCoordinates SuzukiRootDerivedTorus
open CentralClassThreePairing SuzukiEightCentralPairing SuzukiEightThirdLower
open scoped IsMulCommutative commutatorElement CharTwo

variable {P : Type*} [Group P]
variable (phi : P →* U 1) (hphi : Function.Surjective phi)
variable (hcentral : phi.ker ≤ Subgroup.center P)

/-- An actual homomorphism from the additive field to the ambient extension. -/
def parameterHom : Multiplicative (K 1) →* P :=
  (Subgroup.center P).subtype.comp
    (SuzukiEightPairingBound.parameter (scalarForm phi hphi hcentral)).toMultiplicativeLeft

@[simp] theorem parameterHom_apply (d : K 1) :
    parameterHom phi hphi hcentral (Multiplicative.ofAdd d) =
      ((scalarForm phi hphi hcentral d 1).toMul : P) := rfl

/-- The paper convention gives an actual third lower-central generator. -/
theorem paperCommutator_mem_third (c : commutator P) (x : P) :
    paperCommutator (c : P) x ∈ third P := by
  have h := Subgroup.commutator_mem_commutator ((commutator P).inv_mem c.property)
    (Subgroup.mem_top x⁻¹)
  simpa only [commutatorElement_def, paperCommutator, inv_inv] using h

/-- Every scalar-form value is an actual third lower-central value. -/
theorem scalarForm_mem_third (d a : K 1) :
    ((scalarForm phi hphi hcentral d a).toMul : P) ∈ third P := by
  obtain ⟨c, hc⟩ := derivedMap_surjective phi hphi
    (derivedCoordinates.symm d).toMul
  obtain ⟨q, hq⟩ := abelianization_surjective (abelianCoordinates.symm a).toMul
  obtain ⟨x, hx⟩ := hphi q
  have hd : derivedCoordinates (Additive.ofMul (derivedMap phi hphi c)) = d := by
    rw [hc]
    exact derivedCoordinates.apply_symm_apply d
  have ha : abelianCoordinates (Additive.ofMul (Abelianization.of (phi x))) = a := by
    rw [hx, hq]
    exact abelianCoordinates.apply_symm_apply a
  rw [← hd, ← ha, scalarForm_lift_eval]
  exact paperCommutator_mem_third c x

theorem parameterHom_range_le_third : (parameterHom phi hphi hcentral).range ≤ third P := by
  rintro r ⟨d, rfl⟩
  exact scalarForm_mem_third phi hphi hcentral d.toAdd 1

variable (alpha : (K 1)ˣ → P ≃* P)
variable (hcompat : ∀ t x, phi (alpha t x) = rootTorusAut 1 t (phi x))
variable (hfix : ∀ t x, x ∈ phi.ker → alpha t x = x)

include hcompat hfix in
/-- Scalar reconstruction puts every actual triple commutator in the parameter range. -/
theorem third_le_parameterHom_range : third P ≤ (parameterHom phi hphi hcentral).range := by
  apply Subgroup.commutator_le.mpr
  intro c hc x _
  have he : ⁅c, x⁆ = paperCommutator c⁻¹ x⁻¹ := by
    simp only [commutatorElement_def, paperCommutator, inv_inv]
  rw [he]
  let d : commutator P := ⟨c⁻¹, (commutator P).inv_mem hc⟩
  let v := derivedCoordinates (Additive.ofMul (derivedMap phi hphi d))
  let a := abelianCoordinates (Additive.ofMul (Abelianization.of (phi x⁻¹)))
  have hv := scalarForm_lift_eval phi hphi hcentral d x⁻¹
  have hrec := SuzukiEightPairingBound.reconstruct SuzukiEightMoore.card_actual
    (scalarForm phi hphi hcentral)
    (scalarForm_invariant phi hphi hcentral alpha hcompat hfix) v a
  refine ⟨Multiplicative.ofAdd (v * a ^ 2), ?_⟩
  rw [parameterHom_apply]
  change ((SuzukiEightPairingBound.parameter (scalarForm phi hphi hcentral)
    (v * a ^ 2)).toMul : P) = paperCommutator c⁻¹ x⁻¹
  rw [← hrec]
  exact hv

include hcompat hfix in
/-- The actual third lower-central subgroup is precisely an actual parameter image. -/
theorem parameterHom_range_eq_third : (parameterHom phi hphi hcentral).range = third P :=
  le_antisymm (parameterHom_range_le_third phi hphi hcentral)
    (third_le_parameterHom_range phi hphi hcentral alpha hcompat hfix)

include hcompat hfix in
theorem parameterHom_one_eq_one :
    parameterHom phi hphi hcentral (Multiplicative.ofAdd (1 : K 1)) = 1 := by
  have h := SuzukiEightPairingBound.parameter_one_eq_zero SuzukiEightMoore.card_actual
    (scalarForm phi hphi hcentral)
    (scalarForm_invariant phi hphi hcentral alpha hcompat hfix)
    (scalarForm_jacobi phi hphi hcentral)
  exact congrArg (fun v : Additive (Subgroup.center P) => (v.toMul : P)) h

include hcompat hfix in
/-- The nontrivial field element one lies in the parameter kernel, halving its image. -/
theorem card_parameterHom_range_le_four : Nat.card (parameterHom phi hphi hcentral).range ≤ 4 := by
  let f := parameterHom phi hphi hcentral
  change Nat.card f.range ≤ 4
  have hone : f (Multiplicative.ofAdd (1 : K 1)) = 1 :=
    parameterHom_one_eq_one phi hphi hcentral alpha hcompat hfix
  have hne : (⟨Multiplicative.ofAdd (1 : K 1), hone⟩ : f.ker) ≠ 1 := by
    intro h
    exact one_ne_zero (congrArg (fun v : f.ker => v.val.toAdd) h)
  let : Nontrivial f.ker := nontrivial_of_ne _ _ hne
  have hk : 2 ≤ Nat.card f.ker := Finite.one_lt_card
  have he := f.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  change Nat.card f.ker * Nat.card f.range = Nat.card (K 1) at he
  rw [SuzukiEightMoore.card_actual] at he
  have hle := Nat.mul_le_mul_right (Nat.card f.range) hk
  rw [he] at hle
  omega

/-- Exponent two is inherited from the additive field by the actual homomorphism. -/
theorem parameterHom_range_square (r : P) (hr : r ∈ (parameterHom phi hphi hcentral).range) :
    r ^ 2 = 1 := by
  obtain ⟨d, rfl⟩ := hr
  rw [← map_pow]
  have hd : d ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    change 2 • d.toAdd = 0
    simp only [two_nsmul, CharTwo.add_self_eq_zero]
  rw [hd, map_one]

/-- Under the actual compatible torus action and transfer inclusion, the
local central kernel is an actual image of size at most four. -/
theorem kernel_eq_parameterHom_range (hderived : phi.ker ≤ commutator P)
    (action : (K 1)ˣ →* MulAut P)
    (hcompatAction : ∀ t x, phi (action t x) = rootTorusAut 1 t (phi x))
    (hfixAction : ∀ t x, x ∈ phi.ker → action t x = x) :
    phi.ker = (parameterHom phi hphi hcentral).range := by
  rw [kernel_eq_third phi hphi hcentral hderived action hcompatAction hfixAction]
  exact (parameterHom_range_eq_third phi hphi hcentral action hcompatAction hfixAction).symm

include hphi hcentral in
/-- The local kernel is finite, even without a finiteness assumption on P. -/
theorem finite_kernel (hderived : phi.ker ≤ commutator P)
    (action : (K 1)ˣ →* MulAut P)
    (hcompatAction : ∀ t x, phi (action t x) = rootTorusAut 1 t (phi x))
    (hfixAction : ∀ t x, x ∈ phi.ker → action t x = x) : Finite phi.ker := by
  rw [kernel_eq_parameterHom_range phi hphi hcentral hderived action hcompatAction hfixAction]
  exact Finite.of_surjective (parameterHom phi hphi hcentral).rangeRestrict
    (parameterHom phi hphi hcentral).rangeRestrict_surjective

include hphi hcentral in
/-- The actual local central-kernel bound at q=8. -/
theorem card_kernel_le_four (hderived : phi.ker ≤ commutator P)
    (action : (K 1)ˣ →* MulAut P)
    (hcompatAction : ∀ t x, phi (action t x) = rootTorusAut 1 t (phi x))
    (hfixAction : ∀ t x, x ∈ phi.ker → action t x = x) : Nat.card phi.ker ≤ 4 := by
  rw [kernel_eq_parameterHom_range phi hphi hcentral hderived action hcompatAction hfixAction]
  exact card_parameterHom_range_le_four phi hphi hcentral action hcompatAction hfixAction

include hphi hcentral in
/-- The actual local kernel is elementary abelian of exponent two. -/
theorem kernel_isElementaryAbelian (hderived : phi.ker ≤ commutator P)
    (action : (K 1)ˣ →* MulAut P)
    (hcompatAction : ∀ t x, phi (action t x) = rootTorusAut 1 t (phi x))
    (hfixAction : ∀ t x, x ∈ phi.ker → action t x = x) :
    IsElementaryAbelian 2 phi.ker where
  toIsMulCommutative := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral y.property) x.val
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply parameterHom_range_square phi hphi hcentral
    rw [← kernel_eq_parameterHom_range phi hphi hcentral hderived action hcompatAction hfixAction]
    exact x.property

variable {E : Type*} [Group E]

/-- The actual central kernel equals the kernel of its full-root preimage projection. -/
def preimageKernelEquiv (pi : E →* G 1) :
    pi.ker ≃* (SuzukiCentralPreimage.projection 1 pi).ker where
  toFun r := ⟨⟨r.val, by
    change pi r.val ∈ root 1
    rw [r.property]
    exact (root 1).one_mem⟩, Subtype.ext r.property⟩
  invFun r := ⟨r.val.val, congrArg Subtype.val r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Every finite perfect central binary cover of the actual Suzuki group
at q=8 has central kernel of order at most four. -/
theorem global_card_kernel_le_four [Finite E] [Group.IsPerfect E]
    (pi : E →* G 1) (hpi : Function.Surjective pi)
    (hEcentral : pi.ker ≤ Subgroup.center E) (hbinary : IsPGroup 2 pi.ker) :
    Nat.card pi.ker ≤ 4 := by
  let R := SuzukiCentralPreimage.P 1 pi
  let psi : R →* U 1 := SuzukiCentralPreimage.projection 1 pi
  have hpsi : Function.Surjective psi := CentralPreimageAction.projection_surjective pi hpi (root 1)
  have hpsicentral : psi.ker ≤ Subgroup.center R :=
    CentralPreimageAction.projection_kernel_central pi hEcentral (root 1)
  have htransfer := SuzukiCentralPreimage.kernel_le_commutator_map 1 pi hpi hEcentral hbinary
  have hpsiderived : psi.ker ≤ commutator R := by
    intro x hx
    have hxpi : x.val ∈ pi.ker := congrArg Subtype.val hx
    obtain ⟨c, hc, hcx⟩ := htransfer hxpi
    have he : c = x := Subtype.ext hcx
    exact he ▸ hc
  have hbound := card_kernel_le_four psi hpsi hpsicentral hpsiderived
    (SuzukiCentralPreimage.torusAction 1 pi hpi hEcentral)
    (SuzukiCentralPreimage.torusAction_projection 1 pi hpi hEcentral)
    (SuzukiCentralPreimage.torusAction_fixes_kernel 1 pi hpi hEcentral)
  rw [Nat.card_congr (preimageKernelEquiv pi).toEquiv]
  exact hbound

end Kourovka2135.SuzukiEightCentralKernel
