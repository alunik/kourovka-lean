import Kourovka2135.ResolutionDegree
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Subtype

/-! The conserved multidegree of a periodic-resolution basis vector `(a,J)`
is `a + 1_J`. Its fibers are the finite squarefree blocks indexed by subsets
of the support of that multidegree. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolution

variable {ι : Type*} [DecidableEq ι]

/-- The natural-valued indicator of a finite subset. -/
def subsetIndicator (J : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator J fun _ _ => 1

@[simp] theorem subsetIndicator_apply (J : Finset ι) (i : ι) :
    subsetIndicator J i = if i ∈ J then 1 else 0 := by
  simp [subsetIndicator]

@[simp] theorem subsetIndicator_support (J : Finset ι) :
    (subsetIndicator J).support = J := by
  ext i
  simp [Finsupp.mem_support_iff]

@[simp] theorem subsetIndicator_degree (J : Finset ι) :
    (subsetIndicator J).degree = J.card := by
  rw [Finsupp.degree_apply, subsetIndicator_support]
  simp

@[simp] theorem subsetIndicator_empty : subsetIndicator (∅ : Finset ι) = 0 := by
  ext i
  simp

@[simp] theorem subsetIndicator_eq_zero_iff (J : Finset ι) :
    subsetIndicator J = 0 ↔ J = ∅ := by
  rw [← Finsupp.support_eq_empty, subsetIndicator_support]

/-- Subset indicators can be subtracted without truncation exactly on the
support-bounded fibers. -/
theorem subsetIndicator_le_iff (J : Finset ι) (w : ι →₀ ℕ) :
    subsetIndicator J ≤ w ↔ J ⊆ w.support := by
  constructor
  · intro h i hi
    have hle := h i
    rw [subsetIndicator_apply, ite_eq_left hi] at hle
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h i
    by_cases hi : i ∈ J
    · have hn : w i ≠ 0 := Finsupp.mem_support_iff.mp (h hi)
      simpa [hi] using (Nat.one_le_iff_ne_zero.mpr hn)
    · simp [hi]

/-- Inserting an absent element adds its unit exponent. -/
theorem subsetIndicator_insert (J : Finset ι) (i : ι) (hi : i ∉ J) :
    subsetIndicator (insert i J) = subsetIndicator J + Finsupp.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [hji]

/-- Erasing a present element removes its unit exponent. -/
theorem subsetIndicator_erase_add (J : Finset ι) (i : ι) (hi : i ∈ J) :
    subsetIndicator (J.erase i) + Finsupp.single i 1 = subsetIndicator J := by
  rw [← subsetIndicator_insert (J.erase i) i (Finset.notMem_erase i J),
    Finset.insert_erase hi]

/-- The invariant multidegree of a flattened resolution basis vector. -/
def blockWeight (a : ι →₀ ℕ) (J : Finset ι) : ι →₀ ℕ :=
  a + subsetIndicator J

@[simp] theorem blockWeight_apply (a : ι →₀ ℕ) (J : Finset ι) (i : ι) :
    blockWeight a J i = a i + if i ∈ J then 1 else 0 := by
  simp [blockWeight]

@[simp] theorem blockWeight_support (a : ι →₀ ℕ) (J : Finset ι) :
    (blockWeight a J).support = a.support ∪ J := by
  simp [blockWeight, Finsupp.support_add_eq_union]

/-- A subset in a basis pair is automatically contained in the conserved support. -/
theorem subset_le_blockWeight_support (a : ι →₀ ℕ) (J : Finset ι) :
    J ⊆ (blockWeight a J).support := by
  rw [blockWeight_support]
  exact Finset.subset_union_right

/-- Homological degree plus squarefree coefficient degree is the conserved degree. -/
theorem blockWeight_degree (a : ι →₀ ℕ) (J : Finset ι) :
    a.degree + J.card = (blockWeight a J).degree := by
  simp [blockWeight]

@[simp] theorem blockWeight_zero_iff (a : ι →₀ ℕ) (J : Finset ι) :
    blockWeight a J = 0 ↔ a = 0 ∧ J = ∅ := by
  rw [← Finsupp.support_eq_empty, blockWeight_support, Finset.union_eq_empty,
    Finsupp.support_eq_empty]

/-- Reconstruct the conserved weight from a support-bounded subset. -/
theorem blockWeight_sub_indicator (w : ι →₀ ℕ) (J : Finset ι) (hJ : J ⊆ w.support) :
    blockWeight (w - subsetIndicator J) J = w := by
  exact tsub_add_cancel_of_le ((subsetIndicator_le_iff J w).mpr hJ)

/-- The inverse reindexing has precisely the degree required for its block. -/
theorem sub_indicator_degree_add_card (w : ι →₀ ℕ) (J : Finset ι)
    (hJ : J ⊆ w.support) :
    (w - subsetIndicator J).degree + J.card = w.degree := by
  rw [blockWeight_degree, blockWeight_sub_indicator w J hJ]

/-- Subset coordinates in one conserved multidegree. This is definitionally
`SquarefreeBlock.Index w.support` without depending on the block module. -/
abbrev WeightBlockIndex (w : ι →₀ ℕ) := {J : Finset ι // J ⊆ w.support}

/-- Actual reindexing of flattened basis coordinates by conserved weight and
its support-bounded squarefree coordinate. -/
def weightIndexEquiv : ((ι →₀ ℕ) × Finset ι) ≃ Σ w : ι →₀ ℕ, WeightBlockIndex w where
  toFun z := ⟨blockWeight z.1 z.2, ⟨z.2, subset_le_blockWeight_support z.1 z.2⟩⟩
  invFun z := (z.1 - subsetIndicator z.2.val, z.2.val)
  left_inv z := by
    rcases z with ⟨a, J⟩
    apply Prod.ext
    · exact add_tsub_cancel_right a (subsetIndicator J)
    · rfl
  right_inv z := by
    rcases z with ⟨w, J, hJ⟩
    apply Sigma.ext (blockWeight_sub_indicator w J hJ)
    dsimp only
    refine (Subtype.heq_iff_coe_eq (fun K => ?_)).mpr ?_
    · rw [blockWeight_sub_indicator w J hJ]
    · rfl

@[simp] theorem weightIndexEquiv_apply_fst (a : ι →₀ ℕ) (J : Finset ι) :
    (weightIndexEquiv (a, J)).1 = blockWeight a J := rfl

@[simp] theorem weightIndexEquiv_apply_snd_val (a : ι →₀ ℕ) (J : Finset ι) :
    (weightIndexEquiv (a, J)).2.val = J := rfl

@[simp] theorem weightIndexEquiv_symm_apply (w : ι →₀ ℕ) (J : WeightBlockIndex w) :
    weightIndexEquiv.symm ⟨w, J⟩ = (w - subsetIndicator J.val, J.val) := rfl

/-- Every active nonzero differential term stays in its conserved-weight block. -/
theorem blockWeight_lower_insert (a : ι →₀ ℕ) (J : Finset ι) (i : ι)
    (hai : a i ≠ 0) (hiJ : i ∉ J) :
    blockWeight (a - Finsupp.single i 1) (insert i J) = blockWeight a J := by
  rw [blockWeight, subsetIndicator_insert J i hiJ]
  calc
    _ = (a - Finsupp.single i 1 + Finsupp.single i 1) + subsetIndicator J := by ac_rfl
    _ = blockWeight a J := by rw [Finsupp.sub_add_single_one_cancel hai]; rfl

/-- Every nonzero contracting-homotopy term stays in its conserved-weight block. -/
theorem blockWeight_raise_erase (a : ι →₀ ℕ) (J : Finset ι) (i : ι) (hiJ : i ∈ J) :
    blockWeight (a + Finsupp.single i 1) (J.erase i) = blockWeight a J := by
  change (a + Finsupp.single i 1) + subsetIndicator (J.erase i) = a + subsetIndicator J
  calc
    _ = a + (subsetIndicator (J.erase i) + Finsupp.single i 1) := by ac_rfl
    _ = _ := by rw [subsetIndicator_erase_add J i hiJ]

end Kourovka2135.PeriodicResolution
