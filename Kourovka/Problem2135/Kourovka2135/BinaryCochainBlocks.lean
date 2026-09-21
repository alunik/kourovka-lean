import Kourovka2135.BinaryDefectWeight
import Kourovka2135.SquarefreeBlock
import Mathlib.LinearAlgebra.DFinsupp

/-! The explicit contraction of cochain defect blocks.

Only weights whose support misses the coefficient support survive. The
projection retains every such weight, including nonzero outside exponents.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCochainBlocks

open BinaryDefectWeight

variable {ι : Type*} [DecidableEq ι]
variable (k : Type*) [Semiring k] (I : Finset ι)

/-- The actual direct sum of cochain defect blocks. -/
abbrev Space (I : Finset ι) (k : Type*) [Zero k] :=
  Π₀ w : ι →₀ ℕ, SquarefreeBlock.Space (activeSet I w) k

/-- Creation in each active coefficient support. -/
def differential : Module.End k (Space I k) :=
  DFinsupp.mapRange.linearMap fun w => SquarefreeBlock.differential k (activeSet I w)

/-- Annihilate one chosen active index; use zero when no index is active. -/
def blockHomotopy (w : ι →₀ ℕ) :
    Module.End k (SquarefreeBlock.Space (activeSet I w) k) :=
  if h : (activeSet I w).Nonempty then
    SquarefreeBlock.annihilation k (activeSet I w) h.choose else 0

def homotopy : Module.End k (Space I k) :=
  DFinsupp.mapRange.linearMap (blockHomotopy k I)

/-- Retain exactly the weights with no active coefficient index. -/
def survivorProjection : Module.End k (Space I k) :=
  DFinsupp.mapRange.linearMap fun w =>
    if activeSet I w = ∅ then LinearMap.id else 0

@[simp] theorem differential_apply (v : Space I k) (w : ι →₀ ℕ) :
    differential k I v w = SquarefreeBlock.differential k (activeSet I w) (v w) := rfl

@[simp] theorem homotopy_apply (v : Space I k) (w : ι →₀ ℕ) :
    homotopy k I v w = blockHomotopy k I w (v w) := rfl

@[simp] theorem survivorProjection_apply (v : Space I k) (w : ι →₀ ℕ) :
    survivorProjection k I v w = if activeSet I w = ∅ then v w else 0 := by
  change (if activeSet I w = ∅ then (LinearMap.id : Module.End k _) else 0) (v w) = _
  by_cases h : activeSet I w = ∅ <;> simp [h]

theorem survivorProjection_eq_zero_iff (v : Space I k) :
    survivorProjection k I v = 0 ↔ ∀ w, activeSet I w = ∅ → v w = 0 := by
  constructor
  · intro h w hw
    have hz := congrArg (fun z : Space I k => z w) h
    simpa [hw] using hz
  · intro h
    apply DFinsupp.ext
    intro w
    by_cases hw : activeSet I w = ∅
    · simp [hw, h w hw]
    · simp [hw]

/-- The surviving coordinates form an actual projection. -/
theorem survivorProjection_idempotent :
    survivorProjection k I * survivorProjection k I = survivorProjection k I := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  by_cases hw : activeSet I w = ∅ <;>
    simp [Module.End.mul_apply, hw]

/-- An empty active set has no creation columns. -/
theorem blockDifferential_eq_zero_of_activeSet_eq_empty (w : ι →₀ ℕ)
    (hw : activeSet I w = ∅) : SquarefreeBlock.differential k (activeSet I w) = 0 := by
  unfold SquarefreeBlock.differential
  apply Finset.sum_eq_zero
  intro i _
  exact (Finset.notMem_empty i.val (hw ▸ i.property)).elim

/-- Every surviving block has zero differential. -/
theorem differential_survivorProjection :
    differential k I * survivorProjection k I = 0 := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  by_cases hw : activeSet I w = ∅
  · simp [Module.End.mul_apply, hw, blockDifferential_eq_zero_of_activeSet_eq_empty k I w hw]
  · simp [Module.End.mul_apply, hw]

/-- Every boundary has zero surviving component. -/
theorem survivorProjection_differential :
    survivorProjection k I * differential k I = 0 := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  by_cases hw : activeSet I w = ∅
  · simp [Module.End.mul_apply, hw, blockDifferential_eq_zero_of_activeSet_eq_empty k I w hw]
  · simp [Module.End.mul_apply, hw]

variable [CharP k 2]

theorem differential_square_zero : differential k I * differential k I = 0 := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  exact LinearMap.congr_fun
    (SquarefreeBlock.differential_square_zero k (activeSet I w)) (v w)

/-- The actual block contraction retains all and only the inactive blocks. -/
theorem contraction (v : Space I k) :
    differential k I (homotopy k I v) + homotopy k I (differential k I v) +
      survivorProjection k I v = v := by
  apply DFinsupp.ext
  intro w
  by_cases h : (activeSet I w).Nonempty
  · have hw : activeSet I w ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    have hc := LinearMap.congr_fun
      (SquarefreeBlock.differential_annihilation_add k (activeSet I w)
        h.choose h.choose_spec) (v w)
    simpa [blockHomotopy, h, hw, Module.End.mul_apply] using hc
  · have hw : activeSet I w = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [blockHomotopy, hw, SquarefreeBlock.differential]

/-- A cycle with no surviving coordinate has the explicit preimage `H v`. -/
theorem differential_homotopy_of_cycle (v : Space I k)
    (hv : differential k I v = 0) (hzero : survivorProjection k I v = 0) :
    differential k I (homotopy k I v) = v := by
  simpa [hv, hzero] using contraction k I v

theorem exists_boundary_of_cycle_of_survivorProjection_eq_zero (v : Space I k)
    (hv : differential k I v = 0) (hzero : survivorProjection k I v = 0) :
    ∃ u : Space I k, differential k I u = v :=
  ⟨homotopy k I v, differential_homotopy_of_cycle k I v hv hzero⟩

end Kourovka2135.BinaryCochainBlocks
