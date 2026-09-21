import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-! Degree indices and the elementary reindexing maps for the tensor-periodic
resolution. Raising adds one copy of an index; lowering removes one copy only
on the active locus where that coordinate is positive. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolution

variable {ι : Type*}

/-- Exponent vectors of total homological degree `n`. Repeated indices are
retained, as required for the tensor of periodic resolutions. -/
abbrev DegreeIndex (ι : Type*) (n : ℕ) := {a : ι →₀ ℕ // a.degree = n}

instance degreeIndexFinite [Finite ι] (n : ℕ) : Finite (DegreeIndex ι n) := by
  have hfinite : {a : ι →₀ ℕ | a.degree = n}.Finite := by
    simpa only [Finsupp.degree_eq_weight_one] using
      Finsupp.finite_of_nat_weight_eq (fun _ : ι => (1 : ℕ)) (fun _ => one_ne_zero) n
  exact hfinite.to_subtype

instance degreeIndexFintype [Finite ι] (n : ℕ) : Fintype (DegreeIndex ι n) :=
  Fintype.ofFinite _

/-- The inclusion used to embed one degree into the ungraded free module. -/
def degreeIndexEmbedding (n : ℕ) : DegreeIndex ι n ↪ (ι →₀ ℕ) :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem degreeIndexEmbedding_apply (n : ℕ) (a : DegreeIndex ι n) :
    degreeIndexEmbedding n a = a.val := rfl

instance degreeIndexZeroUnique : Unique (DegreeIndex ι 0) where
  default := ⟨0, by simp⟩
  uniq a := by
    apply Subtype.ext
    exact (Finsupp.degree_eq_zero_iff a.val).mp a.property

/-- Raising one exponent increases the total degree by exactly one. -/
theorem degree_add_single_one (a : ι →₀ ℕ) (i : ι) :
    (a + Finsupp.single i 1).degree = a.degree + 1 := by
  simp

/-- Lowering a positive exponent decreases the total degree by exactly one. -/
theorem degree_sub_single_one_add (a : ι →₀ ℕ) (i : ι) (hi : a i ≠ 0) :
    (a - Finsupp.single i 1).degree + 1 = a.degree := by
  simpa only [Finsupp.degree_eq_weight_one] using
    (Finsupp.weight_sub_single_add (w := fun _ : ι => (1 : ℕ)) hi)

@[simp] theorem add_single_one_apply_same (a : ι →₀ ℕ) (i : ι) :
    (a + Finsupp.single i 1 : ι →₀ ℕ) i = a i + 1 := by simp

@[simp] theorem add_single_one_apply_ne (a : ι →₀ ℕ) (i j : ι) (hji : j ≠ i) :
    (a + Finsupp.single i 1 : ι →₀ ℕ) j = a j := by simp [hji]

@[simp] theorem sub_single_one_apply_same (a : ι →₀ ℕ) (i : ι) :
    (a - Finsupp.single i 1 : ι →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]

@[simp] theorem sub_single_one_apply_ne (a : ι →₀ ℕ) (i j : ι) (hji : j ≠ i) :
    (a - Finsupp.single i 1 : ι →₀ ℕ) j = a j := by simp [Finsupp.tsub_apply, hji]

/-- Raising inserts the chosen index into the support. -/
theorem add_single_one_support [DecidableEq ι] (a : ι →₀ ℕ) (i : ι) :
    (a + Finsupp.single i 1).support = insert i a.support := by
  simp [Finsupp.support_add_eq_union]

/-- Lowering never creates a new support index. -/
theorem sub_single_one_support_subset (a : ι →₀ ℕ) (i : ι) :
    (a - Finsupp.single i 1).support ⊆ a.support :=
  Finsupp.support_tsub

/-- Lowering removes an index from the support precisely when its previous
exponent was one. This includes the inactive exponent-zero case. -/
theorem sub_single_one_support [DecidableEq ι] (a : ι →₀ ℕ) (i : ι) :
    (a - Finsupp.single i 1).support =
      if a i = 1 then a.support.erase i else a.support := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : a i = 1
    · simp [hi]
    · simp only [ite_eq_right hi, Finsupp.mem_support_iff, sub_single_one_apply_same]
      omega
  · by_cases hi : a i = 1 <;>
      simp [hi, Finsupp.mem_support_iff, Finsupp.tsub_apply, hji]

/-- For a fixed index, raising is injective on all exponent vectors. -/
theorem add_single_one_injective (i : ι) :
    Function.Injective (fun a : ι →₀ ℕ => a + Finsupp.single i 1) := by
  intro a b hab
  exact add_right_cancel hab

/-- For a fixed index, lowering is injective on the active locus. -/
theorem sub_single_one_injOn (i : ι) :
    Set.InjOn (fun a : ι →₀ ℕ => a - Finsupp.single i 1) {a | a i ≠ 0} := by
  intro a ha b hb hab
  change a - Finsupp.single i 1 = b - Finsupp.single i 1 at hab
  calc
    a = a - Finsupp.single i 1 + Finsupp.single i 1 :=
      (Finsupp.sub_add_single_one_cancel ha).symm
    _ = b - Finsupp.single i 1 + Finsupp.single i 1 := by rw [hab]
    _ = b := Finsupp.sub_add_single_one_cancel hb

/-- The degree-raising map on exponent indices. -/
def raiseIndex {n : ℕ} (i : ι) (a : DegreeIndex ι n) : DegreeIndex ι (n + 1) :=
  ⟨a.val + Finsupp.single i 1, by simp [a.property]⟩

/-- The degree-lowering map, with its necessary active-coordinate hypothesis. -/
def lowerIndex {n : ℕ} (i : ι) (a : DegreeIndex ι (n + 1)) (hi : a.val i ≠ 0) :
    DegreeIndex ι n :=
  ⟨a.val - Finsupp.single i 1, by
    have hh := degree_sub_single_one_add a.val i hi
    have ha := a.property
    omega⟩

@[simp] theorem raiseIndex_val {n : ℕ} (i : ι) (a : DegreeIndex ι n) :
    (raiseIndex i a).val = a.val + Finsupp.single i 1 := rfl

@[simp] theorem lowerIndex_val {n : ℕ} (i : ι) (a : DegreeIndex ι (n + 1))
    (hi : a.val i ≠ 0) :
    (lowerIndex i a hi).val = a.val - Finsupp.single i 1 := rfl

@[simp] theorem raiseIndex_active {n : ℕ} (i : ι) (a : DegreeIndex ι n) :
    (raiseIndex i a).val i ≠ 0 := by simp

theorem raiseIndex_injective {n : ℕ} (i : ι) :
    Function.Injective (raiseIndex (n := n) i) := by
  intro a b hab
  apply Subtype.ext
  exact add_single_one_injective i (congrArg Subtype.val hab)

@[simp] theorem lowerIndex_raiseIndex {n : ℕ} (i : ι) (a : DegreeIndex ι n) :
    lowerIndex i (raiseIndex i a) (raiseIndex_active i a) = a := by
  apply Subtype.ext
  exact add_tsub_cancel_right _ _

@[simp] theorem raiseIndex_lowerIndex {n : ℕ} (i : ι) (a : DegreeIndex ι (n + 1))
    (hi : a.val i ≠ 0) :
    raiseIndex i (lowerIndex i a hi) = a := by
  apply Subtype.ext
  exact Finsupp.sub_add_single_one_cancel hi

/-- Raising identifies degree `n` with the active locus of degree `n+1`.
Its inverse is the injective reindexing required by each differential column. -/
def raiseIndexEquiv {n : ℕ} (i : ι) :
    DegreeIndex ι n ≃ {a : DegreeIndex ι (n + 1) // a.val i ≠ 0} where
  toFun a := ⟨raiseIndex i a, raiseIndex_active i a⟩
  invFun a := lowerIndex i a.val a.property
  left_inv a := lowerIndex_raiseIndex i a
  right_inv a := by
    apply Subtype.ext
    exact raiseIndex_lowerIndex i a.val a.property

/-- Lowering restricted to its active degree subtype is injective. -/
theorem lowerIndex_injective {n : ℕ} (i : ι) :
    Function.Injective (fun a : {a : DegreeIndex ι (n + 1) // a.val i ≠ 0} =>
      lowerIndex i a.val a.property) :=
  (raiseIndexEquiv i).symm.injective

end Kourovka2135.PeriodicResolution
