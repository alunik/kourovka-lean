import Mathlib.Algebra.Order.Field.Rat
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary interval branches

A finite binary word gives an affine chart from `[0,1]` onto its standard
dyadic interval. A branch records equality of actual rational permutations
on that entire interval. The subgroup relation below uses elements of the
ordinary subgroup, not piecewise closure.
-/

namespace Kourovka.P21_38

namespace BinaryWord

/-- The affine chart of a standard binary interval. -/
def chart : List Bool → ℚ → ℚ
  | [], t => t
  | b :: w, t => ((if b then 1 else 0) + chart w t) / 2

@[simp] theorem chart_nil (t : ℚ) : chart [] t = t := rfl

@[simp] theorem chart_cons (b : Bool) (w : List Bool) (t : ℚ) :
    chart (b :: w) t = ((if b then 1 else 0) + chart w t) / 2 := rfl

/-- Concatenation of words is composition of their interval charts. -/
theorem chart_append (u v : List Bool) (t : ℚ) :
    chart (u ++ v) t = chart u (chart v t) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, chart_cons, ih]

theorem chart_strictMono (w : List Bool) : StrictMono (chart w) := by
  induction w with
  | nil => exact strictMono_id
  | cons b w ih =>
    intro s t hst
    have h := ih hst
    simp only [chart_cons]
    linarith

/-- Every binary interval lies in the unit interval. -/
theorem chart_mem_unit (w : List Bool) {t : ℚ} (ht : t ∈ Set.Icc (0 : ℚ) 1) :
    chart w t ∈ Set.Icc (0 : ℚ) 1 := by
  induction w with
  | nil => exact ht
  | cons b w ih =>
    cases b <;> simp only [chart_cons, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [ih.1, ih.2]

/-- The chart has slope `2 ^ (-length)`; this formula uses only natural powers. -/
theorem chart_affine (w : List Bool) (t : ℚ) :
    chart w t = chart w 0 + t / (2 : ℚ) ^ w.length := by
  induction w with
  | nil => simp [chart]
  | cons b w ih =>
    simp only [chart_cons, List.length_cons, pow_succ, ih]
    ring

end BinaryWord

/-- A permutation has the branch from the binary interval `u` to `v`. -/
def HasBranch (f : Equiv.Perm ℚ) (u v : List Bool) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℚ) 1, f (BinaryWord.chart u t) = BinaryWord.chart v t

namespace HasBranch

variable {f g : Equiv.Perm ℚ} {u v w : List Bool}

theorem one (u : List Bool) : HasBranch 1 u u := fun _ _ => rfl

theorem inv (h : HasBranch f u v) : HasBranch f⁻¹ v u := by
  intro t ht
  exact Equiv.Perm.inv_eq_iff_eq.mpr (h t ht).symm

theorem mul (hf : HasBranch f u v) (hg : HasBranch g v w) :
    HasBranch (g * f) u w := by
  intro t ht
  rw [Equiv.Perm.mul_apply, hf t ht, hg t ht]

theorem append (h : HasBranch f u v) (w : List Bool) :
    HasBranch f (u ++ w) (v ++ w) := by
  intro t ht
  simp only [BinaryWord.chart_append]
  exact h _ (BinaryWord.chart_mem_unit w ht)

end HasBranch

/-- Branch equivalence witnessed by an element of the ordinary subgroup `H`. -/
def BranchRelated (H : Subgroup (Equiv.Perm ℚ)) (u v : List Bool) : Prop :=
  ∃ f ∈ H, HasBranch f u v

namespace BranchRelated

variable {H : Subgroup (Equiv.Perm ℚ)} {u v w : List Bool}

theorem refl (H : Subgroup (Equiv.Perm ℚ)) (u : List Bool) : BranchRelated H u u :=
  ⟨1, H.one_mem, HasBranch.one u⟩

theorem symm (h : BranchRelated H u v) : BranchRelated H v u := by
  obtain ⟨f, hf, hb⟩ := h
  exact ⟨f⁻¹, H.inv_mem hf, hb.inv⟩

theorem trans (huv : BranchRelated H u v) (hvw : BranchRelated H v w) :
    BranchRelated H u w := by
  obtain ⟨f, hf, hfb⟩ := huv
  obtain ⟨g, hg, hgb⟩ := hvw
  exact ⟨g * f, H.mul_mem hg hf, hfb.mul hgb⟩

theorem append (h : BranchRelated H u v) (w : List Bool) :
    BranchRelated H (u ++ w) (v ++ w) := by
  obtain ⟨f, hf, hb⟩ := h
  exact ⟨f, hf, hb.append w⟩

end BranchRelated

end Kourovka.P21_38
