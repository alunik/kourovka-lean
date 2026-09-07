import Kourovka.Problems.P21_03.Proof.TranspositionCore
import Kourovka.Problems.P21_03.Proof.YoungSubgroup

/-!
# The bounded partition carried by the transposition core

The blocks are the orbits of the transposition core.  We encode each orbit by
its least point, so equality of labels is definitionally independent of any
choice of orbit representative.  For a soluble permutation subgroup these
blocks have size at most four, and the associated Young subgroup is exactly
the transposition core.
-/

open Equiv MulAction Set Subgroup
open scoped Pointwise

namespace Kourovka213

variable {n : ℕ}

/-- The finite orbit of `x` under the transposition core. -/
noncomputable def coreOrbitFinset (H : Subgroup (Sym n)) (x : Fin n) : Finset (Fin n) :=
  (MulAction.orbit (transpositionCore H) x).toFinite.toFinset

@[simp]
theorem mem_coreOrbitFinset (H : Subgroup (Sym n)) (x y : Fin n) :
    y ∈ coreOrbitFinset H x ↔ y ∈ MulAction.orbit (transpositionCore H) x := by
  simp [coreOrbitFinset]

theorem coreOrbitFinset_nonempty (H : Subgroup (Sym n)) (x : Fin n) :
    (coreOrbitFinset H x).Nonempty := by
  exact ⟨x, mem_coreOrbitFinset H x x |>.2 (MulAction.mem_orbit_self x)⟩

/-- The canonical label of a transposition-core orbit: its least point. -/
noncomputable def coreOrbitLabel (H : Subgroup (Sym n)) (x : Fin n) : Fin n :=
  (coreOrbitFinset H x).min' (coreOrbitFinset_nonempty H x)

theorem coreOrbitLabel_mem_orbit (H : Subgroup (Sym n)) (x : Fin n) :
    coreOrbitLabel H x ∈ MulAction.orbit (transpositionCore H) x := by
  exact mem_coreOrbitFinset H x (coreOrbitLabel H x) |>.1
    (Finset.min'_mem (coreOrbitFinset H x) (coreOrbitFinset_nonempty H x))

/-- Canonical labels agree exactly on transposition-core orbits. -/
theorem coreOrbitLabel_eq_iff (H : Subgroup (Sym n)) (x y : Fin n) :
    coreOrbitLabel H x = coreOrbitLabel H y ↔
      x ∈ MulAction.orbit (transpositionCore H) y := by
  constructor
  · intro hlabel
    have hx : MulAction.orbit (transpositionCore H) (coreOrbitLabel H x) =
        MulAction.orbit (transpositionCore H) x :=
      MulAction.orbit_eq_iff.mpr (coreOrbitLabel_mem_orbit H x)
    have hy : MulAction.orbit (transpositionCore H) (coreOrbitLabel H y) =
        MulAction.orbit (transpositionCore H) y :=
      MulAction.orbit_eq_iff.mpr (coreOrbitLabel_mem_orbit H y)
    apply MulAction.orbit_eq_iff.mp
    rw [← hx, ← hy, hlabel]
  · intro hxy
    have horbit : MulAction.orbit (transpositionCore H) x =
        MulAction.orbit (transpositionCore H) y :=
      MulAction.orbit_eq_iff.mpr hxy
    have hfinset : coreOrbitFinset H x = coreOrbitFinset H y := by
      ext z
      simp only [mem_coreOrbitFinset]
      rw [horbit]
    simp only [coreOrbitLabel, hfinset]

private theorem card_coreOrbitLabel_fiber_le_four
    (H : Subgroup (Sym n)) [Group.IsSolvable H] (i : Fin n) :
    Fintype.card {x // coreOrbitLabel H x = i} ≤ 4 := by
  classical
  by_cases hi : Nonempty {x // coreOrbitLabel H x = i}
  · let x₀ : {x // coreOrbitLabel H x = i} := Classical.choice hi
    have hset : {x : Fin n | coreOrbitLabel H x = i} =
        MulAction.orbit (transpositionCore H) (x₀ : Fin n) := by
      ext x
      change coreOrbitLabel H x = i ↔
        x ∈ MulAction.orbit (transpositionCore H) (x₀ : Fin n)
      rw [← coreOrbitLabel_eq_iff H x (x₀ : Fin n), x₀.property]
    let e : {x // coreOrbitLabel H x = i} ≃
        TranspositionOrbit H (x₀ : Fin n) :=
      Equiv.setCongr hset
    calc
      Fintype.card {x // coreOrbitLabel H x = i} =
          Fintype.card (TranspositionOrbit H (x₀ : Fin n)) :=
        Fintype.card_congr e
      _ = Set.ncard (MulAction.orbit (transpositionCore H) (x₀ : Fin n)) := by
        rw [Set.fintypeCard_eq_ncard]
      _ ≤ 4 := ncard_transpositionCore_orbit_le_four H (x₀ : Fin n)
  · have hempty : IsEmpty {x // coreOrbitLabel H x = i} :=
      not_nonempty_iff.mp hi
    let _ : IsEmpty {x // coreOrbitLabel H x = i} := hempty
    simp

/-- The bounded partition whose blocks are the transposition-core orbits. -/
noncomputable def corePartition (H : Subgroup (Sym n)) [Group.IsSolvable H] :
    BoundedPartition n where
  block := coreOrbitLabel H
  card_fiber_le_four := card_coreOrbitLabel_fiber_le_four H

@[simp]
theorem corePartition_block (H : Subgroup (Sym n)) [Group.IsSolvable H]
    (x : Fin n) :
    (corePartition H).block x = coreOrbitLabel H x :=
  rfl

theorem corePartition_block_eq_iff (H : Subgroup (Sym n)) [Group.IsSolvable H]
    (x y : Fin n) :
    (corePartition H).block x = (corePartition H).block y ↔
      x ∈ MulAction.orbit (transpositionCore H) y :=
  coreOrbitLabel_eq_iff H x y

/-- The Young subgroup on the core-orbit partition is the core itself. -/
theorem youngSubgroup_corePartition (H : Subgroup (Sym n)) [Group.IsSolvable H] :
    youngSubgroup (corePartition H) = transpositionCore H := by
  ext sigma
  rw [mem_youngSubgroup, mem_transpositionCore_iff]
  constructor
  · intro hsigma x
    exact (corePartition_block_eq_iff H (sigma x) x).mp (hsigma x)
  · intro hsigma x
    exact (corePartition_block_eq_iff H (sigma x) x).mpr (hsigma x)

/-- Two soluble transposition cores in relative position `sigma` are disjoint
exactly when their canonical block table is simple. -/
theorem disjoint_transpositionCore_conjugate_iff_isSimple
    (H K : Subgroup (Sym n)) [Group.IsSolvable H] [Group.IsSolvable K]
    (sigma : Sym n) :
    Disjoint (transpositionCore H) (conjugate (transpositionCore K) sigma) ↔
      IsSimple (corePartition H) (corePartition K) sigma := by
  rw [← youngSubgroup_corePartition H, ← youngSubgroup_corePartition K]
  exact disjoint_youngSubgroup_conjugate_iff_isSimple
    (corePartition H) (corePartition K) sigma

/-- Equivalent zero-collision formulation of disjointness of the two cores. -/
theorem disjoint_transpositionCore_conjugate_iff_collisionCount_eq_zero
    (H K : Subgroup (Sym n)) [Group.IsSolvable H] [Group.IsSolvable K]
    (sigma : Sym n) :
    Disjoint (transpositionCore H) (conjugate (transpositionCore K) sigma) ↔
      collisionCount (corePartition H) (corePartition K) sigma = 0 := by
  rw [disjoint_transpositionCore_conjugate_iff_isSimple,
    isSimple_iff_collisionCount_eq_zero]

/-- Intersection form of the simplicity criterion. -/
theorem inf_transpositionCore_conjugate_eq_bot_iff_isSimple
    (H K : Subgroup (Sym n)) [Group.IsSolvable H] [Group.IsSolvable K]
    (sigma : Sym n) :
    transpositionCore H ⊓ conjugate (transpositionCore K) sigma = ⊥ ↔
      IsSimple (corePartition H) (corePartition K) sigma := by
  rw [← le_bot_iff, ← disjoint_iff_inf_le]
  exact disjoint_transpositionCore_conjugate_iff_isSimple H K sigma

/-- Intersection form of the zero-collision criterion. -/
theorem inf_transpositionCore_conjugate_eq_bot_iff_collisionCount_eq_zero
    (H K : Subgroup (Sym n)) [Group.IsSolvable H] [Group.IsSolvable K]
    (sigma : Sym n) :
    transpositionCore H ⊓ conjugate (transpositionCore K) sigma = ⊥ ↔
      collisionCount (corePartition H) (corePartition K) sigma = 0 := by
  rw [inf_transpositionCore_conjugate_eq_bot_iff_isSimple,
    isSimple_iff_collisionCount_eq_zero]

end Kourovka213
