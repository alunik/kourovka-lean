import Kourovka2135.GeneratingSets
import Kourovka2135.Vendor.CFSG.ElementaryAbelian

/-! Power calculations with central commutators, used for minimal normal p-kernels. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped commutatorElement
variable {G : Type u} [Group G]

theorem paperCommutator_pow_left_of_commute (x y : G)
    (h : Commute (paperCommutator x y) x) (n : ℕ) :
    paperCommutator (x ^ n) y = paperCommutator x y ^ n := by
  induction n with
  | zero => simp [paperCommutator]
  | succ n ih =>
    have heq : paperCommutator (x ^ (n + 1)) y =
        x⁻¹ * paperCommutator (x ^ n) y * x * paperCommutator x y := by
      simp only [pow_succ, paperCommutator]
      group
    rw [heq, ih]
    have hcx : Commute (paperCommutator x y ^ n) x := h.pow_left n
    calc
      x⁻¹ * paperCommutator x y ^ n * x * paperCommutator x y =
          paperCommutator x y ^ n * paperCommutator x y := by
        rw [mul_assoc x⁻¹, hcx.eq, inv_mul_cancel_left]
      _ = paperCommutator x y ^ (n + 1) := (pow_succ _ _).symm

theorem commutator_isElementaryAbelian_of_powers_central (p : ℕ)
    (hD : commutator G ≤ Subgroup.center G)
    (hpow : ∀ x : G, x ^ p ∈ Subgroup.center G) :
    IsElementaryAbelian p (commutator G) := by
  have hsingle (a b : G) : paperCommutator a b ^ p = 1 := by
    have hcD : paperCommutator a b ∈ commutator G := by
      change paperCommutator a b ∈ ⁅(⊤ : Subgroup G), ⊤⁆
      simpa only [paperCommutator, commutatorElement_def, inv_inv] using
        Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := ⊤)
          (g₁ := a⁻¹) (g₂ := b⁻¹) (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hca : Commute (paperCommutator a b) a :=
      (show Commute a (paperCommutator a b) from
        Subgroup.mem_center_iff.mp (hD hcD) a).symm
    rw [← paperCommutator_pow_left_of_commute a b hca p]
    apply (paperCommutator_eq_one_iff _ _).mpr
    exact (show Commute b (a ^ p) from Subgroup.mem_center_iff.mp (hpow a) b).symm
  have hclosed : ∀ x ∈ commutator G, x ^ p = 1 := by
    intro x hx
    rw [commutator_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, b, rfl⟩ := hx
        simpa only [paperCommutator, commutatorElement_def, inv_inv] using hsingle a⁻¹ b⁻¹
    | one => exact one_pow p
    | mul a b ha _ iha ihb =>
        have haD : a ∈ commutator G := by rw [commutator_eq_closure]; exact ha
        have hab : Commute a b :=
          (show Commute b a from Subgroup.mem_center_iff.mp (hD haD) b).symm
        rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a _ iha => simp only [inv_pow, iha, inv_one]
  refine {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp (hD b.property) a)⟩⟩
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  exact Subtype.ext (hclosed x x.property)

end Kourovka2135
