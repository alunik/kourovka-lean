import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

/-! Finite coverage of a generated subgroup from generator transitions alone. -/

namespace Kourovka.P21_99

/-- A finite set containing the identity and closed under right multiplication
by the generators contains their whole subgroup. Inverses follow from the
injectivity of right multiplication on that finite set. -/
theorem closure_subset_of_finite_right_closed
    {G : Type*} [Group G] {S R : Set G}
    (hR : R.Finite) (hone : (1 : G) ∈ R)
    (hstep : ∀ g ∈ S, ∀ x ∈ R, x * g ∈ R) :
    (Subgroup.closure S : Set G) ⊆ R := by
  let P : Subgroup G :=
    { carrier := {g | ∀ x ∈ R, x * g ∈ R}
      one_mem' := by
        intro x hx
        simpa using hx
      mul_mem' := by
        intro g h hg hh x hx
        simpa only [mul_assoc] using hh (x * g) (hg x hx)
      inv_mem' := by
        intro g hg x hx
        have hm : Set.MapsTo (fun y : G => y * g) R R := fun y hy => hg y hy
        have hi : Set.InjOn (fun y : G => y * g) R := by
          intro y hy z hz heq
          exact mul_right_cancel heq
        have hs := (hR.injOn_iff_bijOn_of_mapsTo hm).mp hi
        obtain ⟨y, hy, hyx⟩ := hs.surjOn hx
        simpa only [← hyx, mul_inv_cancel_right] using hy }
  have hclosure : Subgroup.closure S ≤ P :=
    (Subgroup.closure_le P).mpr (fun g hg => hstep g hg)
  intro g hg
  simpa only [one_mul] using hclosure hg 1 hone

/-- Table-index form of `closure_subset_of_finite_right_closed`. Only a
transition for each table element and generator is required; no multiplication
table for arbitrary pairs of table elements is assumed. -/
theorem generated_mem_range
    {G ι κ : Type*} [Group G] [Finite ι]
    (table : ι → G) (generator : κ → G)
    (hone : ∃ i, table i = 1)
    (hstep : ∀ i j, ∃ k, table i * generator j = table k)
    {g : G} (hg : g ∈ Subgroup.closure (Set.range generator)) :
    ∃ i, table i = g := by
  apply closure_subset_of_finite_right_closed (Set.finite_range table) hone ?_ hg
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩
  obtain ⟨k, hk⟩ := hstep i j
  exact ⟨k, hk.symm⟩

end Kourovka.P21_99
