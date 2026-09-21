import Kourovka2135.CentralCommutatorGoodSet
import Kourovka2135.CanonicalOddGoodSet
import Kourovka2135.NestedNormalExtension

/-! An actual good set in the canonical central quotient of an odd
Frattini extension, and its full inverse image.

Starting with a generating good set in G/R, the central commutator
construction supplies one in G/[R,G] with exactly that image. The proved
odd moving-kernel lifting theorem then makes its full inverse image good
in G. No classification, multiplier, central-kernel size, or element-order
preservation is assumed or concluded here.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135.OddCanonicalCentralGoodSet

variable {G : Type u} [Group G]

/-- The natural projection from the canonical central quotient. -/
abbrev projection (R : Subgroup G) [R.Normal] :
    (G ⧸ ⁅R, (⊤ : Subgroup G)⁆) →* (G ⧸ R) :=
  NestedNormalExtension.projection ⁅R, (⊤ : Subgroup G)⁆ R
    (Subgroup.commutator_le_left _ _)

theorem projection_surjective (R : Subgroup G) [R.Normal] :
    Function.Surjective (projection R) :=
  NestedNormalExtension.projection_surjective ⁅R, (⊤ : Subgroup G)⁆ R
    (Subgroup.commutator_le_left _ _)

/-- Centrality is derived from the actual commutator quotient. -/
theorem projection_kernel_central (R : Subgroup G) [R.Normal] :
    (projection R).ker ≤ Subgroup.center (G ⧸ ⁅R, (⊤ : Subgroup G)⁆) := by
  let D := ⁅R, (⊤ : Subgroup G)⁆
  let q := QuotientGroup.mk' D
  change (NestedNormalExtension.projection D R
    (Subgroup.commutator_le_left _ _)).ker ≤ _
  rw [NestedNormalExtension.projection_ker]
  change R.map q ≤ Subgroup.center (G ⧸ D)
  have hqtop : (⊤ : Subgroup G).map q = ⊤ :=
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective D)
  have hDbot : D.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff D).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (le_refl D)
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  rw [← hqtop, ← Subgroup.map_commutator]
  exact hDbot

/-- A concrete good-set lift in the canonical quotient, not the full
inverse image of the original set. -/
def canonicalGoodSet (R : Subgroup G) [R.Normal] (B : Set (G ⧸ R)) :
    Set (G ⧸ ⁅R, (⊤ : Subgroup G)⁆) :=
  CentralCommutatorGoodSet.commutatorLift (projection R) B

theorem image_canonicalGoodSet (R : Subgroup G) [R.Normal]
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B) :
    projection R '' canonicalGoodSet R B = B :=
  CentralCommutatorGoodSet.image_commutatorLift (projection R)
    (projection_surjective R) hB

theorem isGeneratingGoodSet_canonicalGoodSet [Group.IsPerfect G]
    (R : Subgroup G) [R.Normal]
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B) :
    IsGeneratingGoodSet (canonicalGoodSet R B) :=
  CentralCommutatorGoodSet.isGeneratingGoodSet_commutatorLift
    (projection R) (projection_surjective R) (projection_kernel_central R) hB

/-- The full inverse image of the constructed canonical good set is good
through an actual odd-prime Frattini kernel. -/
theorem isGeneratingGoodSet_full_preimage [Finite G] [Group.IsPerfect G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hF : R ≤ frattini G)
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B) :
    IsGeneratingGoodSet
      ((QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆) ⁻¹' canonicalGoodSet R B) :=
  IsGeneratingGoodSet.preimage_quotient_commutator_of_odd_frattini hp hodd R hR hF
    (isGeneratingGoodSet_canonicalGoodSet R hB)

/-- The constructed good set retains precisely the original quotient image. -/
theorem image_full_preimage (R : Subgroup G) [R.Normal]
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B) :
    QuotientGroup.mk' R ''
      ((QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆) ⁻¹' canonicalGoodSet R B) = B := by
  apply Set.Subset.antisymm
  · rintro s ⟨g, hg, rfl⟩
    have hmem : projection R (QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆ g) ∈
        projection R '' canonicalGoodSet R B := ⟨_, hg, rfl⟩
    rw [image_canonicalGoodSet R hB] at hmem
    exact hmem
  · intro s hs
    have hmem : s ∈ projection R '' canonicalGoodSet R B := by
      rw [image_canonicalGoodSet R hB]
      exact hs
    obtain ⟨c, hc, hcs⟩ := hmem
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective ⁅R, (⊤ : Subgroup G)⁆ c
    refine ⟨g, ?_, ?_⟩
    · change QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆ g ∈ canonicalGoodSet R B
      rwa [hg]
    · change projection R (QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆ g) = s
      rw [hg]
      exact hcs

/-- Existence form exposing both the central quotient and the full lifted set. -/
theorem exists_canonical_good_set [Finite G] [Group.IsPerfect G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hF : R ≤ frattini G)
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B) :
    ∃ C : Set (G ⧸ ⁅R, (⊤ : Subgroup G)⁆),
      IsGeneratingGoodSet C ∧ projection R '' C = B ∧
      IsGeneratingGoodSet ((QuotientGroup.mk' ⁅R, (⊤ : Subgroup G)⁆) ⁻¹' C) :=
  ⟨canonicalGoodSet R B, isGeneratingGoodSet_canonicalGoodSet R hB,
    image_canonicalGoodSet R hB,
    isGeneratingGoodSet_full_preimage hp hodd R hR hF hB⟩

end Kourovka2135.OddCanonicalCentralGoodSet
