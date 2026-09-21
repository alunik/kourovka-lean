import Kourovka2135.CentralPGroupH2Obstruction
import Mathlib.GroupTheory.Subgroup.Center

/-! Eliminate the actual residual central 2-kernel after quotienting by a
normal subgroup, and turn equality of conjugation images into a group factorization.
-/

set_option autoImplicit false
namespace Kourovka2135

/-- Equality of the actual quotient images gives the corresponding factorization. -/
theorem sup_eq_of_quotient_images_eq
    {G : Type*} [Group G] (N R C : Subgroup G) [C.Normal]
    (hCR : C ≤ R)
    (himage : N.map (QuotientGroup.mk' C) = R.map (QuotientGroup.mk' C)) :
    N ⊔ C = R := by
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' C)) himage
  rw [QuotientGroup.comap_map_mk', QuotientGroup.comap_map_mk', sup_eq_right.mpr hCR] at h
  simpa only [sup_comm] using h

/-- A central factor remains central after quotienting the other factor. -/
theorem quotient_image_le_center_of_central_factor
    {G : Type*} [Group G] (N R C : Subgroup G) [N.Normal]
    (hR : N ⊔ C = R) (hC : C ≤ Subgroup.center G) :
    R.map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N) := by
  rw [← hR, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  exact (Subgroup.map_mono hC).trans
    (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N))

/-- If R/N is central and the simple quotient is binary SL2 with f≥3,
the actual central-kernel obstruction forces R=N. -/
theorem normal_two_subgroup_eq_of_central_binary_remainder
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N R : Subgroup G) [N.Normal] [R.Normal] (hNR : N ≤ R)
    (hR : IsPGroup 2 R)
    (hcentral : R.map (QuotientGroup.mk' N) ≤ Subgroup.center (G ⧸ N))
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : SLTwo.SL2 F ≃* (G ⧸ R)) : R = N := by
  have hbot := CentralPGroupH2Obstruction.binary_eq_bot
    (R.map (QuotientGroup.mk' N)) (hR.map (QuotientGroup.mk' N)) hcentral
    F f hcard hf (e.trans (QuotientGroup.quotientQuotientEquivQuotient N R hNR).symm)
  apply le_antisymm ?_ hNR
  intro r hr
  have hm := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hr
  rw [hbot] at hm
  exact (QuotientGroup.eq_one_iff (N := N) r).mp hm

/-- A central complement in a radical factorization disappears in the
perfect quotient; no Schur-multiplier statement is assumed. -/
theorem normal_two_subgroup_eq_of_central_factor
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N R C : Subgroup G) [N.Normal] [R.Normal]
    (hR : IsPGroup 2 R) (hfactor : N ⊔ C = R) (hC : C ≤ Subgroup.center G)
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : SLTwo.SL2 F ≃* (G ⧸ R)) : R = N :=
  normal_two_subgroup_eq_of_central_binary_remainder N R
    (hfactor ▸ le_sup_left) hR
    (quotient_image_le_center_of_central_factor N R C hfactor hC)
    F f hcard hf e

end Kourovka2135
