import Kourovka2135.CentralClassThreeVanishing

/-! The actual central triple-commutator pairing satisfies Jacobi. This is
proved from the group Hall-Witt identity, with the commutator conventions
converted explicitly. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.CentralClassThreeJacobi

open CentralClassThreePairing CentralClassThreeVanishing
open scoped IsMulCommutative commutatorElement

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- Central commutators agree for the two conventions used here. -/
theorem commutatorElement_eq_paperCommutator_of_central (x y : G)
    (h : paperCommutator x y ∈ Subgroup.center G) :
    ⁅x, y⁆ = paperCommutator x y := by
  calc
    ⁅x, y⁆ = (x * y) * paperCommutator x y * (x * y)⁻¹ := by
      simp only [commutatorElement_def, paperCommutator]
      group
    _ = paperCommutator x y := by
      rw [(Subgroup.mem_center_iff.mp h (x * y)), mul_inv_cancel_right]

theorem commutatorElement_inv_inv (x y : G) :
    ⁅x⁻¹, y⁻¹⁆ = paperCommutator x y := by
  simp only [commutatorElement_def, paperCommutator, inv_inv]

variable (pi : G →* Q) (hpi : Function.Surjective pi)
variable (hker : pi.ker ≤ Subgroup.center G)
variable (hQ : commutator Q ≤ Subgroup.center Q)

/-- An actual triple commutator, regarded as an element of the center. -/
def tripleCenter (x y z : G) : Subgroup.center G :=
  rightHom pi hpi hker hQ
    ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩ z

@[simp] theorem tripleCenter_coe (x y z : G) :
    (tripleCenter pi hpi hker hQ x y z : G) =
      paperCommutator (paperCommutator x y) z := rfl

theorem rightHom_conj_inv (c : commutator G) (y z : G) :
    rightHom pi hpi hker hQ c (y⁻¹ * z⁻¹ * y) =
      (rightHom pi hpi hker hQ c z)⁻¹ := by
  simp only [map_mul, map_inv]
  rw [mul_right_comm, inv_mul_cancel, one_mul]

/-- The three cyclic central triple commutators have product one. -/
theorem tripleCenter_jacobi (x y z : G) :
    tripleCenter pi hpi hker hQ x y z *
      tripleCenter pi hpi hker hQ y z x *
      tripleCenter pi hpi hker hQ z x y = 1 := by
  have he (a b c : G) :
      ⁅⁅a⁻¹, b⁻¹⁆, b⁻¹ * c⁻¹ * b⁆ =
        (tripleCenter pi hpi hker hQ a b c : G)⁻¹ := by
    rw [commutatorElement_inv_inv]
    rw [commutatorElement_eq_paperCommutator_of_central _ _
      (commutator_mem_center pi hpi hker hQ
        ⟨paperCommutator a b, paperCommutator_mem_commutator a b⟩ _)]
    exact congrArg Subtype.val (rightHom_conj_inv pi hpi hker hQ
      ⟨paperCommutator a b, paperCommutator_mem_commutator a b⟩ b c)
  have hw := commutatorElement_commutatorElement_conj_mul x⁻¹ y⁻¹ z⁻¹
  simp only [inv_inv] at hw
  rw [he, he, he] at hw
  have hc : (tripleCenter pi hpi hker hQ x y z)⁻¹ *
      (tripleCenter pi hpi hker hQ y z x)⁻¹ *
      (tripleCenter pi hpi hker hQ z x y)⁻¹ = 1 := Subtype.ext hw
  have hi := congrArg Inv.inv hc
  simpa only [mul_inv_rev, inv_inv, inv_one, mul_comm, mul_left_comm, mul_assoc] using hi

include pi hpi hker hQ in
/-- Jacobi for the paper's actual commutator convention. -/
theorem paperCommutator_jacobi (x y z : G) :
    paperCommutator (paperCommutator x y) z *
      paperCommutator (paperCommutator y z) x *
      paperCommutator (paperCommutator z x) y = 1 :=
  congrArg Subtype.val (tripleCenter_jacobi pi hpi hker hQ x y z)

/-- Jacobi for the descended pairing, evaluated on arbitrary actual lifts. -/
theorem pairingHom_jacobi (x y z : G) :
    pairingHom pi hpi hker hQ
      (derivedMap pi hpi ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩)
      (Abelianization.of (pi z)) *
    pairingHom pi hpi hker hQ
      (derivedMap pi hpi ⟨paperCommutator y z, paperCommutator_mem_commutator y z⟩)
      (Abelianization.of (pi x)) *
    pairingHom pi hpi hker hQ
      (derivedMap pi hpi ⟨paperCommutator z x, paperCommutator_mem_commutator z x⟩)
      (Abelianization.of (pi y)) = 1 := by
  apply Subtype.ext
  change (pairingHom pi hpi hker hQ _ _ : G) *
    (pairingHom pi hpi hker hQ _ _ : G) *
    (pairingHom pi hpi hker hQ _ _ : G) = 1
  rw [pairingHom_apply_lifts, pairingHom_apply_lifts, pairingHom_apply_lifts]
  exact paperCommutator_jacobi pi hpi hker hQ x y z

variable [IsElementaryAbelian 2 (Abelianization Q)]
variable [IsElementaryAbelian 2 (commutator Q)]

/-- Jacobi in the actual additive central two-torsion target. -/
theorem bilinear_jacobi (x y z : G) :
    bilinear pi hpi hker hQ
      (Additive.ofMul (derivedMap pi hpi
        ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩))
      (Additive.ofMul (Abelianization.of (pi z))) +
    bilinear pi hpi hker hQ
      (Additive.ofMul (derivedMap pi hpi
        ⟨paperCommutator y z, paperCommutator_mem_commutator y z⟩))
      (Additive.ofMul (Abelianization.of (pi x))) +
    bilinear pi hpi hker hQ
      (Additive.ofMul (derivedMap pi hpi
        ⟨paperCommutator z x, paperCommutator_mem_commutator z x⟩))
      (Additive.ofMul (Abelianization.of (pi y))) = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact pairingHom_jacobi pi hpi hker hQ x y z

end Kourovka2135.CentralClassThreeJacobi
