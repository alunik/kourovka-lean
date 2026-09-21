import Kourovka2135.SquarefreeBlock
import Mathlib.LinearAlgebra.DFinsupp

/-! The ground-field contraction of the direct sum of weight blocks.
Only the zero-weight block survives. This is an explicit contraction, with
no exactness or cohomology vanishing hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolutionBlocks
variable {ι : Type*} [DecidableEq ι]
variable (k : Type*) [Semiring k]

abbrev Space (ι : Type*) (k : Type*) [Zero k] :=
  Π₀ w : ι →₀ ℕ, SquarefreeBlock.Space w.support k

def differential : Module.End k (Space ι k) :=
  DFinsupp.mapRange.linearMap fun w => SquarefreeBlock.differential k w.support

def blockHomotopy (w : ι →₀ ℕ) : Module.End k (SquarefreeBlock.Space w.support k) :=
  if h : w.support.Nonempty then
    SquarefreeBlock.annihilation k w.support h.choose else 0

def homotopy : Module.End k (Space ι k) :=
  DFinsupp.mapRange.linearMap (blockHomotopy k)

def zeroWeightProjection : Module.End k (Space ι k) := by
  classical
  exact DFinsupp.mapRange.linearMap fun w => if w = 0 then LinearMap.id else 0

@[simp] theorem differential_apply (v : Space ι k) (w : ι →₀ ℕ) :
    differential k v w = SquarefreeBlock.differential k w.support (v w) := rfl

@[simp] theorem homotopy_apply (v : Space ι k) (w : ι →₀ ℕ) :
    homotopy k v w = blockHomotopy k w (v w) := rfl

@[simp] theorem zeroWeightProjection_apply (v : Space ι k) (w : ι →₀ ℕ) :
    zeroWeightProjection k v w = if w = 0 then v w else 0 := by
  classical
  change (if w = 0 then (LinearMap.id : Module.End k _) else 0) (v w) = _
  by_cases h : w = 0 <;> simp [h]

theorem zeroWeightProjection_eq_zero_iff (v : Space ι k) :
    zeroWeightProjection k v = 0 ↔ v 0 = 0 := by
  constructor
  · intro h
    simpa using congrArg (fun z : Space ι k => z 0) h
  · intro h
    ext w
    by_cases hw : w = 0
    · subst w
      simp [h]
    · simp [hw]

variable [CharP k 2]

theorem differential_square_zero : differential k * differential (ι := ι) k = 0 := by
  apply LinearMap.ext
  intro v
  apply DFinsupp.ext
  intro w
  exact LinearMap.congr_fun (SquarefreeBlock.differential_square_zero k w.support) (v w)

/-- All nonzero-weight blocks are contracted by removing a fixed active
coordinate; the remaining projection is exactly the zero-weight block. -/
theorem contraction (v : Space ι k) :
    differential k (homotopy k v) + homotopy k (differential k v) +
      zeroWeightProjection k v = v := by
  classical
  apply DFinsupp.ext
  intro w
  by_cases h : w.support.Nonempty
  · have hw : w ≠ 0 := by intro hw; subst w; simp at h
    have hc := LinearMap.congr_fun
      (SquarefreeBlock.differential_annihilation_add k w.support h.choose h.choose_spec) (v w)
    simpa [blockHomotopy, h, hw, Module.End.mul_apply] using hc
  · have hw : w = 0 := by
      simpa only [Finsupp.support_eq_empty] using Finset.not_nonempty_iff_eq_empty.mp h
    subst w
    simp [blockHomotopy, SquarefreeBlock.differential]

/-- The explicit homotopy supplies a preimage for every cycle whose
zero-weight component vanishes. -/
theorem differential_homotopy_of_cycle (v : Space ι k)
    (hv : differential k v = 0) (hzero : v 0 = 0) :
    differential k (homotopy k v) = v := by
  have hp := (zeroWeightProjection_eq_zero_iff k v).mpr hzero
  simpa [hv, hp] using contraction k v

end Kourovka2135.PeriodicResolutionBlocks
