import Kourovka.Problems.P21_38.Proof.BinaryBranches
import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.PLMoves

/-!
# Global affine maps between binary intervals

These maps are used only as pieces in a finite construction. Their membership
in the dyadic PL group is proved by composing dyadic affine coordinate charts.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

namespace BinaryWord

def bitOrigin (b : Bool) : ℚ := (if b then 1 else 0) / 2

theorem bitOrigin_grid (b : Bool) : bitOrigin b ∈ Grid 2 1 := by
  cases b <;> simp only [bitOrigin, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

/-- The chart of a binary interval, extended affinely to the whole line. -/
noncomputable def chartPerm : List Bool → Equiv.Perm ℚ
  | [] => 1
  | b :: w => (scalePerm 0 1 (bitOrigin b))⁻¹ * chartPerm w

@[simp] theorem chartPerm_apply (w : List Bool) (t : ℚ) : chartPerm w t = chart w t := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [chartPerm, Equiv.Perm.mul_apply, scalePerm_inv_apply, ih, chart_cons,
      bitOrigin]
    norm_num
    ring

theorem chartPerm_mem (w : List Bool) : chartPerm w ∈ PLGroup 2 (powSlopes 0) := by
  induction w with
  | nil => exact (PLGroup 2 (powSlopes 0)).one_mem
  | cons b w ih =>
    exact (PLGroup 2 (powSlopes 0)).mul_mem
      ((PLGroup 2 (powSlopes 0)).inv_mem (scalePerm_mem 0 1 (bitOrigin_grid b))) ih

theorem chart_dyadic (w : List Bool) {t : ℚ} (ht : ∃ N, t ∈ Grid 2 N) :
    ∃ N, chart w t ∈ Grid 2 N := by
  obtain ⟨N, ht⟩ := ht
  obtain ⟨Nf, Bf, hf⟩ := (chartPerm_mem w).2.1
  exact ⟨_, by simpa using hf.mapsGrid ht⟩

theorem chart_zero_dyadic (w : List Bool) : ∃ N, chart w 0 ∈ Grid 2 N :=
  chart_dyadic w ⟨0, int_mem_grid (m := 2) 0 0⟩

theorem chart_one_dyadic (w : List Bool) : ∃ N, chart w 1 ∈ Grid 2 N :=
  chart_dyadic w ⟨0, int_mem_grid (m := 2) 0 1⟩

theorem chart_zero_lt_one (w : List Bool) : chart w 0 < chart w 1 :=
  chart_strictMono w (by norm_num)

end BinaryWord

/-- The unique affine permutation carrying one binary interval onto another. -/
noncomputable def branchAffine (u v : List Bool) : Equiv.Perm ℚ :=
  BinaryWord.chartPerm v * (BinaryWord.chartPerm u)⁻¹

theorem branchAffine_mem (u v : List Bool) :
    branchAffine u v ∈ PLGroup 2 (powSlopes 0) :=
  (PLGroup 2 (powSlopes 0)).mul_mem (BinaryWord.chartPerm_mem v)
    ((PLGroup 2 (powSlopes 0)).inv_mem (BinaryWord.chartPerm_mem u))

@[simp] theorem branchAffine_chart (u v : List Bool) (t : ℚ) :
    branchAffine u v (BinaryWord.chart u t) = BinaryWord.chart v t := by
  rw [← BinaryWord.chartPerm_apply u t]
  change BinaryWord.chartPerm v ((BinaryWord.chartPerm u)⁻¹ (BinaryWord.chartPerm u t)) = _
  rw [perm_inv_apply_self, BinaryWord.chartPerm_apply]

theorem branchAffine_hasBranch (u v : List Bool) : HasBranch (branchAffine u v) u v :=
  fun t _ => branchAffine_chart u v t

#audit_axioms branchAffine_mem
#audit_axioms branchAffine_hasBranch

end Kourovka.P21_38
