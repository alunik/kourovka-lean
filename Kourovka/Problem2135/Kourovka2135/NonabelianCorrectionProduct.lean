import Kourovka2135.NonabelianCorrection
import Kourovka2135.ClassTwoCommutators

/-! Exact product comparison for the nonabelian commutator correction.
The center condition is used only to move commutator factors. -/
set_option autoImplicit false
namespace Kourovka2135
variable {N : Type*} [Group N]

theorem mul_eq_swap_mul_paperCommutator (x y : N) :
    x * y = y * x * paperCommutator x y := by
  simp only [paperCommutator]
  group

theorem paperCommutator_inv_left_of_classTwo
    (hC : commutator N ≤ Subgroup.center N) (x y : N) :
    paperCommutator x⁻¹ y = (paperCommutator x y)⁻¹ := by
  have h := congrArg Subtype.val ((centralCommutatorLeftHom hC y).map_inv x)
  exact h

theorem automorphismCorrection_mul_of_classTwo
    (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N) (x y x' y' : N) :
    automorphismCorrection D E (x * x') (y * y') =
      automorphismCorrection D E x y * automorphismCorrection D E x' y' *
        (paperCommutator (x'⁻¹ * (D y')⁻¹) (automorphismCorrection D E x y) *
          paperCommutator x (D y') * paperCommutator (E x') y) := by
  let f := automorphismCorrection D E x y
  let s := x'⁻¹ * (D y')⁻¹
  let c₁ := paperCommutator x (D y')
  let c₂ := paperCommutator (E x') y
  let c₃ := paperCommutator s f
  have hc (a b z : N) : Commute (paperCommutator a b) z :=
    (show Commute z (paperCommutator a b) from
      Subgroup.mem_center_iff.mp (hC (paperCommutator_mem_commutator a b)) z).symm
  have hx : x⁻¹ * (D y')⁻¹ * x = (D y')⁻¹ * c₁ := by
    have hi : paperCommutator (D y')⁻¹ x = c₁ := by
      rw [paperCommutator_inv_left_of_classTwo hC, paperCommutator_inv_swap]
    rw [← hi]
    simp only [paperCommutator]
    group
  have hy : y⁻¹ * E x' * y = E x' * c₂ := by
    simp only [c₂, paperCommutator]
    group
  have hs : s * f = f * s * c₃ := mul_eq_swap_mul_paperCommutator s f
  calc
    _ = x'⁻¹ * (x⁻¹ * (D y')⁻¹ * x) * f * (y⁻¹ * E x' * y) * y' := by
      simp only [automorphismCorrection, map_mul, mul_inv_rev, f]
      group
    _ = s * c₁ * f * (E x' * c₂) * y' := by rw [hx, hy]; dsimp [s]; group
    _ = (s * f) * E x' * y' * (c₁ * c₂) := by
      have h₁ := hc x (D y') f
      have h₂ := hc x (D y') (E x')
      have h₃ := hc x (D y') y'
      have h₄ := hc (E x') y y'
      change Commute c₁ f at h₁
      change Commute c₁ (E x') at h₂
      change Commute c₁ y' at h₃
      change Commute c₂ y' at h₄
      calc
        _ = s * (c₁ * (f * E x')) * (c₂ * y') := by group
        _ = s * ((f * E x') * c₁) * (y' * c₂) := by
          rw [(h₁.mul_right h₂).eq, h₄.eq]
        _ = s * (f * E x') * (c₁ * y') * c₂ := by group
        _ = _ := by rw [h₃.eq]; group
    _ = f * (s * E x' * y') * (c₃ * c₁ * c₂) := by
      rw [hs]
      have h₁ := hc s f (E x')
      have h₂ := hc s f y'
      change Commute c₃ (E x') at h₁
      change Commute c₃ y' at h₂
      calc
        _ = f * s * (c₃ * (E x' * y')) * (c₁ * c₂) := by group
        _ = f * s * ((E x' * y') * c₃) * (c₁ * c₂) := by
          rw [(h₁.mul_right h₂).eq]
        _ = _ := by group
    _ = _ := by rfl

theorem automorphismCorrection_mul_of_central_value
    (hC : commutator N ≤ Subgroup.center N)
    (D E : MulAut N) (x y x' y' : N)
    (hf : automorphismCorrection D E x y ∈ Subgroup.center N) :
    automorphismCorrection D E (x * x') (y * y') =
      automorphismCorrection D E x y * automorphismCorrection D E x' y' *
        (paperCommutator x (D y') * paperCommutator (E x') y) := by
  rw [automorphismCorrection_mul_of_classTwo hC]
  have h := (paperCommutator_eq_one_iff
    (x'⁻¹ * (D y')⁻¹) (automorphismCorrection D E x y)).mpr
      (Subgroup.mem_center_iff.mp hf _)
  rw [h, one_mul]

end Kourovka2135
