import Kourovka2135.NonabelianCorrectionFiber
import Kourovka2135.NonabelianCorrectionSurjective
import Kourovka2135.MinimalSpecialCorrectionForms

/-! The complete commutator fiber through a special minimal nonabelian
normal 2-subgroup. All linear, quadratic, and faithfulness conditions
are discharged for the actual ambient conjugation action. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

theorem exists_paperCommutator_mul_eq_of_special_minimal
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (hspecial : Subgroup.center N = commutator N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) [IsSimpleGroup (G ⧸ R)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsNilpotent N := hN.isNilpotent
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian (by decide) N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian (by decide) N hN hmin
  let : IsElementaryAbelian 2 (Subgroup.center N) := by
    rw [hspecial]
    infer_instance
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  have hmove := commutator_eq_self_of_minimal_noncentral N hnc hmin
  let c := paperCommutator a b
  let D : MulAut N := MulAut.conjNormal (a * c)⁻¹
  let E : MulAut N := MulAut.conjNormal (c⁻¹ * b)⁻¹
  have hD : ∀ z ∈ Subgroup.center N, D z = z :=
    minimal_nonabelian_conjNormal_fixes_center N hmin hnonabelian (a * c)⁻¹
  have hE : ∀ z ∈ Subgroup.center N, E z = z :=
    minimal_nonabelian_conjNormal_fixes_center N hmin hnonabelian (c⁻¹ * b)⁻¹
  have hC : commutator N ≤ Subgroup.center N :=
    minimal_noncentral_commutator_le_internal_center N hmin
  have hL : Function.Surjective (correctionLinearMap 2 D E) :=
    correctionLinearMap_surjective_of_generating_pair N 2 a b hgen hmove
  have hDE : (centerActionLinear 2 D).comp (centerActionLinear 2 E) ≠
      (centerActionLinear 2 E).comp (centerActionLinear 2 D) :=
    minimal_correction_centerAction_noncommuting N hN hmin hnonabelian hmove R hR a b hc
  obtain ⟨x, y, hxy⟩ := automorphismCorrection_full_fiber hC D E hD hE hL hDE
    (fun ell hell x hx => minimal_special_centerScalarCommutatorForm_nondegenerate
      N hmin hspecial hC ell hell hx) t
  refine ⟨MulAut.conjNormal c x, y, ?_⟩
  rw [paperCommutator_mul_eq_correction, abelianCorrection_eq_automorphismCorrection]
  have hx : MulAut.conjNormal c⁻¹ (MulAut.conjNormal c x) = x := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hx]
  exact congrArg (fun z : N => paperCommutator a b * (z : G)) hxy

end Kourovka2135
