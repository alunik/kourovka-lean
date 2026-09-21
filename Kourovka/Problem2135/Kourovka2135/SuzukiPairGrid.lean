import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! The four-by-four counting step in the Suzuki pair-weight bound. The only
finite certificate is a single row, with sixteen possible supports. Global
cardinality bounds are obtained by summing the proved row inequality. -/

set_option autoImplicit false
namespace Kourovka2135.SuzukiPairGrid

open Finset
abbrev Grid := Fin 4 × Fin 4

def PathSupport (T : Finset (Fin 4)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, a < b → b.val = a.val + 1

instance (T : Finset (Fin 4)) : Decidable (PathSupport T) :=
  inferInstanceAs (Decidable (∀ a ∈ T, ∀ b ∈ T, a < b → b.val = a.val + 1))

/-- An admissible row has at most one initial vertex plus one for each
selected edge. This bounded fact concerns only the four-vertex path. -/
theorem row_bound : ∀ T : Finset (Fin 4), PathSupport T →
    T.card ≤ 1 + (if (0 : Fin 4) ∈ T ∧ (1 : Fin 4) ∈ T then 1 else 0) +
      (if (1 : Fin 4) ∈ T ∧ (2 : Fin 4) ∈ T then 1 else 0) +
      (if (2 : Fin 4) ∈ T ∧ (3 : Fin 4) ∈ T then 1 else 0) := by
  decide +kernel

def row (S : Finset Grid) (r : Fin 4) : Finset (Fin 4) :=
  univ.filter fun c => (c,r) ∈ S

def outerCount (S : Finset Grid) : ℕ :=
  ∑ r : Fin 4,
    ((if ((0 : Fin 4),r) ∈ S ∧ ((1 : Fin 4),r) ∈ S then 1 else 0) +
    (if ((2 : Fin 4),r) ∈ S ∧ ((3 : Fin 4),r) ∈ S then 1 else 0))

def innerCount (S : Finset Grid) : ℕ :=
  ∑ r : Fin 4, if ((1 : Fin 4),r) ∈ S ∧ ((2 : Fin 4),r) ∈ S then 1 else 0

def outerLeft (i : Fin 2) : Fin 4 := ![0,2] i
def outerRight (i : Fin 2) : Fin 4 := ![1,3] i

def outerEdges (S : Finset Grid) : Finset (Fin 2 × Fin 4) :=
  univ.filter fun p => (outerLeft p.1,p.2) ∈ S ∧ (outerRight p.1,p.2) ∈ S

theorem outerLeft_injective : Function.Injective outerLeft := by
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num [outerLeft, Fin.ext_iff] at *

theorem outerCount_eq_card (S : Finset Grid) : outerCount S = (outerEdges S).card := by
  unfold outerEdges
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [outerCount, outerLeft, outerRight, sum_add_distrib]
  rw [card_eq_sum_ones, sum_filter]
  rfl

/-- Uniqueness of the actual lower endpoint bounds the number of outer
edges, with the two possible edge locations counted separately. -/
theorem outerCount_le_one_of_unique (S : Finset Grid)
    (h : ∀ (i j : Fin 2) (r s : Fin 4),
      (outerLeft i,r) ∈ S → (outerRight i,r) ∈ S →
      (outerLeft j,s) ∈ S → (outerRight j,s) ∈ S →
      (outerLeft i,r) = (outerLeft j,s)) : outerCount S ≤ 1 := by
  rw [outerCount_eq_card]
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpl,hpr⟩ := (mem_filter.mp hp).2
  obtain ⟨hql,hqr⟩ := (mem_filter.mp hq).2
  have he := h p.1 q.1 p.2 q.2 hpl hpr hql hqr
  exact Prod.ext (outerLeft_injective (congrArg Prod.fst he))
    (congrArg (fun z : Grid => z.2) he)

theorem innerCount_le_one_of_unique (S : Finset Grid)
    (h : ∀ r s : Fin 4,
      ((1 : Fin 4),r) ∈ S → ((2 : Fin 4),r) ∈ S →
      ((1 : Fin 4),s) ∈ S → ((2 : Fin 4),s) ∈ S → r = s) : innerCount S ≤ 1 := by
  have he : innerCount S = (univ.filter fun r : Fin 4 =>
      ((1 : Fin 4),r) ∈ S ∧ ((2 : Fin 4),r) ∈ S).card := by
    unfold innerCount
    rw [card_eq_sum_ones, sum_filter]
  rw [he]
  apply card_le_one.mpr
  intro r hr s hs
  exact h r s (mem_filter.mp hr).2.1 (mem_filter.mp hr).2.2
    (mem_filter.mp hs).2.1 (mem_filter.mp hs).2.2

theorem card_eq_sum_rows (S : Finset Grid) : S.card = ∑ r : Fin 4, (row S r).card := by
  calc
    S.card = ∑ p : Grid, if p ∈ S then 1 else 0 := by simp
    _ = ∑ r : Fin 4, ∑ c : Fin 4, if (c,r) ∈ S then 1 else 0 := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = ∑ r : Fin 4, (row S r).card := by simp [row]

/-- At most four initial vertices plus the actual selected edges. -/
theorem card_le_four_add_edges (S : Finset Grid) (hpath : ∀ r, PathSupport (row S r)) :
    S.card ≤ 4 + outerCount S + innerCount S := by
  rw [card_eq_sum_rows]
  have hh := sum_le_sum (s := (univ : Finset (Fin 4)))
    (fun r _ => row_bound (row S r) (hpath r))
  simpa [row, outerCount, innerCount, sum_add_distrib, add_assoc, add_left_comm, add_comm] using hh

/-- One edge of each difference type permits at most six selected pairs. -/
theorem card_le_six (S : Finset Grid) (hpath : ∀ r, PathSupport (row S r))
    (houter : outerCount S ≤ 1) (hinner : innerCount S ≤ 1) : S.card ≤ 6 := by
  have := card_le_four_add_edges S hpath
  omega

/-- Attaining six requires an edge of each type. -/
theorem six_forces_edges (S : Finset Grid) (hpath : ∀ r, PathSupport (row S r))
    (houter : outerCount S ≤ 1) (hinner : innerCount S ≤ 1) (hcard : 6 ≤ S.card) :
    outerCount S = 1 ∧ innerCount S = 1 := by
  have := card_le_four_add_edges S hpath
  omega

theorem exists_outer_of_pos (S : Finset Grid) (h : 0 < outerCount S) :
    ∃ r : Fin 4,
      (((0 : Fin 4),r) ∈ S ∧ ((1 : Fin 4),r) ∈ S) ∨
      (((2 : Fin 4),r) ∈ S ∧ ((3 : Fin 4),r) ∈ S) := by
  by_contra hnone
  have hz : outerCount S = 0 := by
    unfold outerCount
    apply sum_eq_zero
    intro r _
    have h0 : ¬ (((0 : Fin 4),r) ∈ S ∧ ((1 : Fin 4),r) ∈ S) :=
      fun hp => hnone ⟨r, Or.inl hp⟩
    have h2 : ¬ (((2 : Fin 4),r) ∈ S ∧ ((3 : Fin 4),r) ∈ S) :=
      fun hp => hnone ⟨r, Or.inr hp⟩
    simp [h0, h2]
  omega

theorem exists_inner_of_pos (S : Finset Grid) (h : 0 < innerCount S) :
    ∃ r : Fin 4, ((1 : Fin 4),r) ∈ S ∧ ((2 : Fin 4),r) ∈ S := by
  by_contra hnone
  have hz : innerCount S = 0 := by
    unfold innerCount
    apply sum_eq_zero
    intro r _
    exact ite_eq_right (fun hp => hnone ⟨r, hp⟩)
  omega

end Kourovka2135.SuzukiPairGrid
