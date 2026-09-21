import Kourovka2135.ClassTwoPowers

/-! Multiplicativity and quotient descent of central commutators. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped commutatorElement
variable {G : Type u} [Group G]

theorem paperCommutator_mem_commutator (x y : G) :
    paperCommutator x y ∈ commutator G := by
  change paperCommutator x y ∈ ⁅(⊤ : Subgroup G), ⊤⁆
  simpa only [paperCommutator, commutatorElement_def, inv_inv] using
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := ⊤)
      (g₁ := x⁻¹) (g₂ := y⁻¹) (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem paperCommutator_inv_swap (x y : G) :
    (paperCommutator x y)⁻¹ = paperCommutator y x := by
  simp only [paperCommutator, mul_inv_rev, inv_inv, mul_assoc]

theorem paperCommutator_mul_left_of_central (x y z : G)
    (hx : paperCommutator x z ∈ Subgroup.center G) :
    paperCommutator (x * y) z = paperCommutator x z * paperCommutator y z := by
  have hcomm : Commute (paperCommutator x z) y :=
    (show Commute y (paperCommutator x z) from Subgroup.mem_center_iff.mp hx y).symm
  calc
    paperCommutator (x * y) z =
        y⁻¹ * paperCommutator x z * y * paperCommutator y z := by
      simp only [paperCommutator]
      group
    _ = paperCommutator x z * paperCommutator y z := by
      rw [mul_assoc y⁻¹, hcomm.eq, inv_mul_cancel_left]

theorem paperCommutator_mul_right_of_central (x y z : G)
    (hy : paperCommutator x y ∈ Subgroup.center G) :
    paperCommutator x (y * z) = paperCommutator x y * paperCommutator x z := by
  have hcomm (a : G) : Commute (paperCommutator x y) a :=
    (show Commute a (paperCommutator x y) from Subgroup.mem_center_iff.mp hy a).symm
  calc
    paperCommutator x (y * z) =
        paperCommutator x z * (z⁻¹ * paperCommutator x y * z) := by
      simp only [paperCommutator]
      group
    _ = paperCommutator x z * paperCommutator x y := by
      rw [mul_assoc z⁻¹, (hcomm z).eq, inv_mul_cancel_left]
    _ = paperCommutator x y * paperCommutator x z := (hcomm _).eq.symm

variable (hD : commutator G ≤ Subgroup.center G)

def centralCommutatorLeftHom (y : G) : G →* commutator G where
  toFun x := ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩
  map_one' := Subtype.ext (by simp [paperCommutator])
  map_mul' x z := Subtype.ext
    (paperCommutator_mul_left_of_central x z y (hD (paperCommutator_mem_commutator x y)))

def centralCommutatorRightHom (x : G) : G →* commutator G where
  toFun y := ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩
  map_one' := Subtype.ext (by simp [paperCommutator])
  map_mul' y z := Subtype.ext
    (paperCommutator_mul_right_of_central x y z (hD (paperCommutator_mem_commutator x y)))

def centralCommutatorLeftQuotientHom (y : G) : G ⧸ Subgroup.center G →* commutator G :=
  QuotientGroup.lift (Subgroup.center G) (centralCommutatorLeftHom hD y) (by
    intro x hx
    apply Subtype.ext
    apply (paperCommutator_eq_one_iff x y).mpr
    exact (show Commute y x from Subgroup.mem_center_iff.mp hx y).symm)

def centralCommutatorRightQuotientHom (x : G) : G ⧸ Subgroup.center G →* commutator G :=
  QuotientGroup.lift (Subgroup.center G) (centralCommutatorRightHom hD x) (by
    intro y hy
    apply Subtype.ext
    apply (paperCommutator_eq_one_iff x y).mpr
    exact Subgroup.mem_center_iff.mp hy x)

end Kourovka2135
