import Kourovka2135.ClassTwoPowers
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Transfer

/-! Transfer forces a central p-subgroup of a perfect group into the derived
subgroup of every subgroup of p-coprime finite index. If the latter has central
commutators and pth powers in the central kernel, that kernel is elementary
abelian. No classification, cohomology, or bound on the kernel is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CentralPGroupTransfer

variable {G : Type u} [Group G] [Group.IsPerfect G]

/-- On a central element, transfer to the abelianization of P is its index
power. Perfectness therefore puts that power in the actual derived subgroup. -/
theorem pow_index_mem_commutator_map (P : Subgroup G) [P.FiniteIndex]
    (x : G) (hx : x ∈ Subgroup.center G) :
    x ^ P.index ∈ (commutator P).map P.subtype := by
  let tau : G →* Abelianization P :=
    MonoidHom.transfer (Abelianization.of : P →* Abelianization P)
  have hconj (n : ℕ) (g : G) (_ : g⁻¹ * x ^ n * g ∈ P) :
      g⁻¹ * x ^ n * g = x ^ n := by
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.center G).pow_mem hx n) g
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hzero : tau x = 1 := by
    let : Group.IsPerfect tau.range := Group.IsPerfect.range tau
    have h : (⟨tau x, ⟨x, rfl⟩⟩ : tau.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h
  have hformula := MonoidHom.transfer_eq_pow
    (Abelianization.of : P →* Abelianization P) x hconj
  have hclass : Abelianization.of
      (⟨x ^ P.index, MonoidHom.transfer_eq_pow_aux x hconj⟩ : P) = 1 :=
    hformula.symm.trans hzero
  refine ⟨⟨x ^ P.index, MonoidHom.transfer_eq_pow_aux x hconj⟩, ?_, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp hclass

/-- Coprime index powers exhaust a central p-subgroup. The conclusion also
shows it is contained in P, without requiring that containment as a premise. -/
theorem le_commutator_map_of_coprime_index (p : ℕ)
    (R : Subgroup G) (hR : IsPGroup p R)
    (hcentral : R ≤ Subgroup.center G)
    (P : Subgroup G) [P.FiniteIndex] (hindex : p.Coprime P.index) :
    R ≤ (commutator P).map P.subtype := by
  intro x hx
  obtain ⟨y, hy⟩ := (hR.powEquiv hindex).surjective (⟨x, hx⟩ : R)
  have hpow : (y : G) ^ P.index = x := congrArg Subtype.val hy
  rw [← hpow]
  exact pow_index_mem_commutator_map P y (hcentral y.property)

/-- The binary specialization uses an actual odd subgroup index. -/
theorem binary_le_commutator_map_of_odd_index
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (hcentral : R ≤ Subgroup.center G)
    (P : Subgroup G) [P.FiniteIndex] (hindex : Odd P.index) :
    R ≤ (commutator P).map P.subtype :=
  le_commutator_map_of_coprime_index 2 R hR hcentral P hindex.coprime_two_left

/-- If the quotient of P by the central kernel is abelian of exponent p,
the actual kernel is elementary abelian. Its size need not be bounded. -/
theorem isElementaryAbelian_of_coprime_index (p : ℕ)
    (R : Subgroup G) (hR : IsPGroup p R)
    (hcentral : R ≤ Subgroup.center G)
    (P : Subgroup G) [P.FiniteIndex] (hindex : p.Coprime P.index)
    (hcomm : (commutator P).map P.subtype ≤ R)
    (hpow : ∀ x : P, (x : G) ^ p ∈ R) :
    IsElementaryAbelian p R := by
  have hD : commutator P ≤ Subgroup.center P := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hcentral (hcomm (Subgroup.mem_map_of_mem P.subtype hx))) y
  have hpower : ∀ x : P, x ^ p ∈ Subgroup.center P := by
    intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral (hpow x)) y
  let : IsElementaryAbelian p (commutator P) :=
    commutator_isElementaryAbelian_of_powers_central p hD hpower
  have hle := le_commutator_map_of_coprime_index p R hR hcentral P hindex
  refine {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hcentral b.property) a)⟩⟩
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro r
  obtain ⟨x, hx, hxr⟩ := hle r.property
  have hxpow : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  apply Subtype.ext
  change (r : G) ^ p = 1
  rw [← hxr]
  exact congrArg (fun y : P => (y : G)) hxpow

/-- In particular a central binary kernel with elementary-abelian quotient
inside an odd-index subgroup is itself elementary abelian. -/
theorem binary_isElementaryAbelian_of_odd_index
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (hcentral : R ≤ Subgroup.center G)
    (P : Subgroup G) [P.FiniteIndex] (hindex : Odd P.index)
    (hcomm : (commutator P).map P.subtype ≤ R)
    (hpow : ∀ x : P, (x : G) ^ 2 ∈ R) :
    IsElementaryAbelian 2 R :=
  isElementaryAbelian_of_coprime_index 2 R hR hcentral P hindex.coprime_two_left
    hcomm hpow

end Kourovka2135.CentralPGroupTransfer
