import Kourovka2135.NormalSubgroupExtension
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.PGroup

/-! Actual short exact sequences after quotienting a nested pair of normal
subgroups, including transport of the Frattini and p-group kernel properties.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135.NestedNormalExtension

variable {G : Type u} [Group G]
variable (C R : Subgroup G) [C.Normal] [R.Normal] (hCR : C ≤ R)

/-- The actual image of the larger normal subgroup in the first quotient. -/
abbrev kernel : Subgroup (G ⧸ C) := R.map (QuotientGroup.mk' C)

/-- The canonical projection G/C -> G/R. -/
def projection : (G ⧸ C) →* (G ⧸ R) :=
  QuotientGroup.map C R (MonoidHom.id G) hCR

@[simp] theorem projection_mk (g : G) :
    projection C R hCR (QuotientGroup.mk' C g) = QuotientGroup.mk' R g := rfl

theorem projection_surjective : Function.Surjective (projection C R hCR) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R q
  exact ⟨QuotientGroup.mk' C g, rfl⟩

theorem projection_ker : (projection C R hCR).ker = kernel C R := by
  simpa only [projection, kernel, Subgroup.comap_id] using
    QuotientGroup.ker_map C R (MonoidHom.id G) hCR

/-- The actual sequence, ready to receive an additive kernel representation. -/
def extension : GroupExtension (Multiplicative (Additive (kernel C R)))
    (G ⧸ C) (G ⧸ R) where
  inl := NormalSubgroupExtension.inclusion (kernel C R)
  rightHom := projection C R hCR
  inl_injective := NormalSubgroupExtension.inclusion_injective (kernel C R)
  range_inl_eq_ker_rightHom := by
    rw [NormalSubgroupExtension.inclusion_range, projection_ker]
  rightHom_surjective := projection_surjective C R hCR

@[simp] theorem extension_inl_range : (extension C R hCR).inl.range = kernel C R :=
  NormalSubgroupExtension.inclusion_range (kernel C R)

omit [R.Normal] in
/-- Images of Frattini subgroups remain in the actual quotient's Frattini subgroup. -/
theorem kernel_le_frattini (hRΦ : R ≤ frattini G) :
    kernel C R ≤ frattini (G ⧸ C) :=
  Subgroup.map_le_iff_le_comap.mpr
    (hRΦ.trans (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective C)))

omit [R.Normal] in
/-- The actual kernel image remains a p-group. -/
theorem kernel_isPGroup (p : ℕ) (hR : IsPGroup p R) : IsPGroup p (kernel C R) :=
  hR.map (QuotientGroup.mk' C)

end Kourovka2135.NestedNormalExtension
