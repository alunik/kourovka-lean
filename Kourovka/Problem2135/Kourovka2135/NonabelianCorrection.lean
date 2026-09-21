import Kourovka2135.AbelianCommutatorFiber

/-! The exact nonabelian correction map and its descent to the center quotient.
This does not assert surjectivity or a quadratic polarization formula. -/
set_option autoImplicit false
namespace Kourovka2135
variable {N : Type*} [Group N]

def automorphismCorrection (D E : MulAut N) (x y : N) : N :=
  x⁻¹ * (D y)⁻¹ * E x * y

theorem automorphismCorrection_mul_center_left (D E : MulAut N)
    (x y z : N) (hz : z ∈ Subgroup.center N) (hEz : E z = z) :
    automorphismCorrection D E (x * z) y = automorphismCorrection D E x y := by
  let B := x⁻¹ * (D y)⁻¹ * E x
  have hc : z⁻¹ * B * z = B := by
    rw [mul_assoc, Subgroup.mem_center_iff.mp hz B, ← mul_assoc, inv_mul_cancel, one_mul]
  calc
    _ = (z⁻¹ * B * z) * y := by
      simp only [automorphismCorrection, map_mul, mul_inv_rev, hEz, B]
      group
    _ = _ := by rw [hc]; rfl

theorem automorphismCorrection_mul_center_right (D E : MulAut N)
    (x y z : N) (hz : z ∈ Subgroup.center N) (hDz : D z = z) :
    automorphismCorrection D E x (y * z) = automorphismCorrection D E x y := by
  let B := automorphismCorrection D E x y
  have hc : z⁻¹ * B * z = B := by
    rw [mul_assoc, Subgroup.mem_center_iff.mp hz B, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcomm : x⁻¹ * z⁻¹ = z⁻¹ * x⁻¹ :=
    Subgroup.mem_center_iff.mp ((Subgroup.center N).inv_mem hz) x⁻¹
  calc
    _ = z⁻¹ * B * z := by
      simp only [automorphismCorrection, map_mul, mul_inv_rev, hDz, B]
      calc
        _ = (x⁻¹ * z⁻¹) * ((D y)⁻¹ * E x * y * z) := by group
        _ = _ := by rw [hcomm]; group
    _ = _ := hc

def centerQuotientCorrection (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z)
    (x y : N ⧸ Subgroup.center N) : N :=
  x.liftOn₂' y (automorphismCorrection D E) (by
    intro a b a' b' ha hb
    have hza : a⁻¹ * a' ∈ Subgroup.center N := QuotientGroup.leftRel_apply.mp ha
    have hzb : b⁻¹ * b' ∈ Subgroup.center N := QuotientGroup.leftRel_apply.mp hb
    have hea : a' = a * (a⁻¹ * a') := by group
    have heb : b' = b * (b⁻¹ * b') := by group
    conv_rhs => rw [hea, heb]
    rw [automorphismCorrection_mul_center_left D E a _ _ hza (hE _ hza),
      automorphismCorrection_mul_center_right D E a b _ hzb (hD _ hzb)])

@[simp] theorem centerQuotientCorrection_mk (D E : MulAut N)
    (hD : ∀ z ∈ Subgroup.center N, D z = z)
    (hE : ∀ z ∈ Subgroup.center N, E z = z) (x y : N) :
    centerQuotientCorrection D E hD hE
      (QuotientGroup.mk' (Subgroup.center N) x) (QuotientGroup.mk' (Subgroup.center N) y) =
      automorphismCorrection D E x y := rfl

variable {G : Type*} [Group G] (A : Subgroup G) [A.Normal]

/-- Reparametrizing the two kernel inputs gives the same correction formula
without assuming that the normal subgroup is abelian. -/
theorem abelianCorrection_eq_automorphismCorrection (a b : G) (u v : A) :
    abelianCorrection A a b u v =
      automorphismCorrection
        (MulAut.conjNormal (a * paperCommutator a b)⁻¹)
        (MulAut.conjNormal ((paperCommutator a b)⁻¹ * b)⁻¹)
        (MulAut.conjNormal (paperCommutator a b)⁻¹ u) v := by
  have he : MulAut.conjNormal ((paperCommutator a b)⁻¹ * b)⁻¹
      (MulAut.conjNormal (paperCommutator a b)⁻¹ u) = MulAut.conjNormal b⁻¹ u := by
    rw [← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  simp only [abelianCorrection, automorphismCorrection, he]

end Kourovka2135
