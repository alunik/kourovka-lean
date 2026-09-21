import Kourovka2135.NonabelianCorrectionForms
import Kourovka2135.MinimalFaithful

/-! The actual central scalar forms and noncommuting correction operators
for a special minimal nonabelian kernel. -/
set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

/-- Central scalar forms are nondegenerate when the center equals the derived subgroup. -/
theorem minimal_special_centerScalarCommutatorForm_nondegenerate
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (commutator N)]
    [IsElementaryAbelian 2 (Subgroup.center N)]
    (hspecial : Subgroup.center N = commutator N)
    (hC : commutator N ≤ Subgroup.center N)
    (ell : Module.Dual (ZMod 2) (Additive (Subgroup.center N))) (hell : ell ≠ 0)
    {x : Additive (N ⧸ Subgroup.center N)}
    (hx : ∀ y, centerScalarCommutatorForm hC ell x y = 0) : x = 0 := by
  let j := (Subgroup.inclusion hC).toAdditive.toZModLinearMap 2
  let psi := ell.comp j
  have hj : Function.Surjective j := by
    intro z
    refine ⟨Additive.ofMul ⟨z.toMul, ?_⟩, rfl⟩
    rw [← hspecial]
    exact z.toMul.property
  have hpsi : psi ≠ 0 := by
    intro hzero
    apply hell
    apply LinearMap.ext
    intro z
    obtain ⟨d, rfl⟩ := hj z
    exact LinearMap.congr_fun hzero d
  apply minimal_noncentral_scalarCommutatorForm_nondegenerate N hmin 2 psi hpsi
  intro y
  exact hx y

/-- Ambient conjugation fixes the whole internal center of a minimal nonabelian kernel. -/
theorem minimal_nonabelian_conjNormal_fixes_center
    (N : Subgroup G) [N.Normal]
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (g : G) (z : N)
    (hz : z ∈ Subgroup.center N) : MulAut.conjNormal g z = z := by
  have hc : (z : G) ∈ Subgroup.center G :=
    minimal_noncentral_center_le N hnonabelian hmin
      (Subgroup.mem_map_of_mem N.subtype hz)
  apply Subtype.ext
  change g * (z : G) * g⁻¹ = (z : G)
  rw [Subgroup.mem_center_iff.mp hc g]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Commuting correction generators would force the original commutator to vanish. -/
theorem paperCommutator_eq_one_of_correction_pair_commute (a b : G)
    (h : Commute (a * paperCommutator a b)⁻¹ ((paperCommutator a b)⁻¹ * b)⁻¹) :
    paperCommutator a b = 1 := by
  have hd := h.inv_inv
  simp only [inv_inv] at hd
  have hi : (paperCommutator a b)⁻¹ = 1 := by
    apply mul_right_cancel (b := a * b)
    calc
      (paperCommutator a b)⁻¹ * (a * b) =
          ((paperCommutator a b)⁻¹ * b) * (a * paperCommutator a b) := by
        simp only [paperCommutator]
        group
      _ = (a * paperCommutator a b) * ((paperCommutator a b)⁻¹ * b) := hd.eq.symm
      _ = 1 * (a * b) := by group
  exact inv_eq_one.mp hi

/-- The correction operators cannot commute when their original commutator
has nonidentity image in the faithfully acting simple quotient. -/
theorem minimal_correction_centerAction_noncommuting [Finite G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    (a b : G) (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1) :
    (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
      (a * paperCommutator a b)⁻¹)).toLinearMap.comp
      (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
        ((paperCommutator a b)⁻¹ * b)⁻¹)).toLinearMap ≠
    (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
      ((paperCommutator a b)⁻¹ * b)⁻¹)).toLinearMap.comp
      (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
        (a * paperCommutator a b)⁻¹)).toLinearMap := by
  let q := QuotientGroup.mk' R
  let ρ := minimalCenterRepresentation N hN hmin R hR
  have hinj : Function.Injective ρ :=
    minimal_center_representation_injective N hN hmin hnonabelian hmove R hR
  intro heq
  have hpair : Commute (q ((a * paperCommutator a b)⁻¹))
      (q (((paperCommutator a b)⁻¹ * b)⁻¹)) := by
    change q ((a * paperCommutator a b)⁻¹) * q (((paperCommutator a b)⁻¹ * b)⁻¹) =
      q (((paperCommutator a b)⁻¹ * b)⁻¹) * q ((a * paperCommutator a b)⁻¹)
    apply hinj
    rw [map_mul, map_mul]
    exact heq
  have hpair' : Commute (q a * paperCommutator (q a) (q b))⁻¹
      ((paperCommutator (q a) (q b))⁻¹ * q b)⁻¹ := by
    simpa only [map_mul, map_inv, map_paperCommutator] using hpair
  apply hc
  rw [map_paperCommutator]
  exact paperCommutator_eq_one_of_correction_pair_commute (q a) (q b) hpair'

end Kourovka2135
