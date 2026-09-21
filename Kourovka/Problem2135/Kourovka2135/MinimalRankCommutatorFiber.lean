import Kourovka2135.DerivedCorrectionFiber
import Kourovka2135.MinimalSpecialCorrectionForms

/-! The rank criterion for full fibers through an actual minimal normal
nonabelian 2-subgroup, allowing its center to be larger than its derived subgroup. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

theorem exists_paperCommutator_mul_eq_of_minimal_rank
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    [IsElementaryAbelian 2 (commutator N)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hrank : 2 * Module.finrank (ZMod 2) (Additive (commutator N)) +
      2 * (Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N))) ≤
      Module.finrank (ZMod 2) (BinaryCorrection.operatorCommutator
        (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
          (a * paperCommutator a b)⁻¹))
        (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
          ((paperCommutator a b)⁻¹ * b)⁻¹))).range) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsNilpotent N := hN.isNilpotent
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
  have hA : Function.Surjective (derivedCorrectionLinear hC D E hD hE) :=
    derivedCorrectionLinear_surjective_of_generating_pair N hC a b hgen hmove hD hE
  have hF := quotientCorrection_surjective_of_derived_rank hC D E hD hE hA
    (fun ell hell x hx => minimal_noncentral_scalarCommutatorForm_nondegenerate
      N hmin 2 ell hell hx) hrank
  obtain ⟨s, hs⟩ := hF t
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) s.1.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) s.2.toMul
  have hxy : automorphismCorrection D E x y = t := by
    change centerQuotientCorrection D E hD hE
      (QuotientGroup.mk' (Subgroup.center N) x) (QuotientGroup.mk' (Subgroup.center N) y) = t
    rw [hx, hy]
    exact hs
  refine ⟨MulAut.conjNormal c x, y, ?_⟩
  rw [paperCommutator_mul_eq_correction, abelianCorrection_eq_automorphismCorrection]
  have hx' : MulAut.conjNormal c⁻¹ (MulAut.conjNormal c x) = x := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hx']
  exact congrArg (fun z : N => paperCommutator a b * (z : G)) hxy

end Kourovka2135
