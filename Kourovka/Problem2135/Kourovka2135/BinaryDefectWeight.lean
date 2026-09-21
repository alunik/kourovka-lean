import Kourovka2135.PeriodicResolutionWeight

/-! Conserved defect weights for the cochain basis with coefficient support `I`.

A basis pair `(a,J)`, with `J ⊆ I`, has defect `a + 1_(I \ J)`.
Its active block is the intersection of the defect support with `I`.
The reindexing retains all exponent coordinates outside `I`.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryDefectWeight

open Kourovka2135.PeriodicResolution

variable {ι : Type*} [DecidableEq ι]

/-- Cochain basis indices with coefficient monomial supported in `I`. -/
abbrev CochainIndex (I : Finset ι) :=
  (ι →₀ ℕ) × {J : Finset ι // J ⊆ I}

/-- The defect conserved by raising an exponent and inserting its coefficient index. -/
def defectWeight (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι) : ι →₀ ℕ :=
  blockWeight a (I \ J)

/-- Only defect coordinates lying in the coefficient support are active. -/
def activeSet (I : Finset ι) (w : ι →₀ ℕ) : Finset ι := w.support ∩ I

/-- The squarefree coordinate inside the active block. -/
def defectCoordinate (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι) : Finset ι :=
  J ∩ activeSet I (defectWeight I a J)

/-- Coordinates in a fixed defect block. -/
abbrev DefectBlockIndex (I : Finset ι) (w : ι →₀ ℕ) :=
  {L : Finset ι // L ⊆ activeSet I w}

@[simp] theorem defectWeight_apply (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (i : ι) :
    defectWeight I a J i = a i + if i ∈ I \ J then 1 else 0 := by
  simp [defectWeight]

@[simp] theorem activeSet_mem (I : Finset ι) (w : ι →₀ ℕ) (i : ι) :
    i ∈ activeSet I w ↔ w i ≠ 0 ∧ i ∈ I := by
  simp [activeSet, Finsupp.mem_support_iff]

theorem activeSet_subset_support (I : Finset ι) (w : ι →₀ ℕ) :
    activeSet I w ⊆ w.support := Finset.inter_subset_left

theorem activeSet_subset (I : Finset ι) (w : ι →₀ ℕ) :
    activeSet I w ⊆ I := Finset.inter_subset_right

theorem sdiff_subset_activeSet (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι) :
    I \ J ⊆ activeSet I (defectWeight I a J) := by
  intro i hi
  exact Finset.mem_inter.mpr
    ⟨subset_le_blockWeight_support a (I \ J) hi, (Finset.mem_sdiff.mp hi).1⟩

theorem defectCoordinate_subset (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι) :
    defectCoordinate I a J ⊆ activeSet I (defectWeight I a J) :=
  Finset.inter_subset_right

/-- The complement of the block coordinate is exactly the missing coefficient support. -/
theorem activeSet_sdiff_defectCoordinate (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) :
    activeSet I (defectWeight I a J) \ defectCoordinate I a J = I \ J := by
  ext i
  have hS := @activeSet_subset ι _ I (defectWeight I a J) i
  have hD := @sdiff_subset_activeSet ι _ I a J i
  simp only [defectCoordinate, Finset.mem_sdiff, Finset.mem_inter] at hS hD ⊢
  tauto

/-- Recover the full coefficient subset by filling in the inactive part of `I`. -/
def recoveredSubset (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι) : Finset ι :=
  (I \ activeSet I w) ∪ L

/-- Recover the exponent vector by subtracting the missing active indicator. -/
def recoveredExponent (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι) : ι →₀ ℕ :=
  w - subsetIndicator (activeSet I w \ L)

theorem recoveredSubset_subset (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι)
    (hL : L ⊆ activeSet I w) : recoveredSubset I w L ⊆ I := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (Finset.mem_sdiff.mp hi).1
  · exact activeSet_subset I w (hL hi)

theorem sdiff_recoveredSubset (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι) :
    I \ recoveredSubset I w L = activeSet I w \ L := by
  ext i
  have hS := @activeSet_subset ι _ I w i
  simp only [recoveredSubset, Finset.mem_sdiff, Finset.mem_union] at hS ⊢
  tauto

theorem recoveredSubset_inter_activeSet (I : Finset ι) (w : ι →₀ ℕ)
    (L : Finset ι) (hL : L ⊆ activeSet I w) :
    recoveredSubset I w L ∩ activeSet I w = L := by
  ext i
  have hLi := @hL i
  simp only [recoveredSubset, Finset.mem_inter, Finset.mem_union,
    Finset.mem_sdiff]
  tauto

theorem recoveredSubset_defectCoordinate (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (hJ : J ⊆ I) :
    recoveredSubset I (defectWeight I a J) (defectCoordinate I a J) = J := by
  ext i
  have hJi := @hJ i
  have hD := @sdiff_subset_activeSet ι _ I a J i
  simp only [recoveredSubset, defectCoordinate, Finset.mem_union,
    Finset.mem_inter, Finset.mem_sdiff] at hD ⊢
  tauto

theorem recoveredExponent_defectCoordinate (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) :
    recoveredExponent I (defectWeight I a J) (defectCoordinate I a J) = a := by
  rw [recoveredExponent, activeSet_sdiff_defectCoordinate]
  exact add_tsub_cancel_right a (subsetIndicator (I \ J))

theorem defectWeight_recovered (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι) :
    defectWeight I (recoveredExponent I w L) (recoveredSubset I w L) = w := by
  rw [defectWeight, sdiff_recoveredSubset]
  exact blockWeight_sub_indicator w (activeSet I w \ L) (by
    intro i hi
    exact activeSet_subset_support I w (Finset.mem_sdiff.mp hi).1)

theorem defectCoordinate_recovered (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι)
    (hL : L ⊆ activeSet I w) :
    defectCoordinate I (recoveredExponent I w L) (recoveredSubset I w L) = L := by
  rw [defectCoordinate, defectWeight_recovered]
  exact recoveredSubset_inter_activeSet I w L hL

/-- The actual bijection between cochain basis pairs and their defect blocks. -/
def defectIndexEquiv (I : Finset ι) :
    CochainIndex I ≃ Σ w : ι →₀ ℕ, DefectBlockIndex I w where
  toFun z := ⟨defectWeight I z.1 z.2.val,
    ⟨defectCoordinate I z.1 z.2.val, defectCoordinate_subset I z.1 z.2.val⟩⟩
  invFun z := (recoveredExponent I z.1 z.2.val,
    ⟨recoveredSubset I z.1 z.2.val, recoveredSubset_subset I z.1 z.2.val z.2.property⟩)
  left_inv z := by
    rcases z with ⟨a, J, hJ⟩
    apply Prod.ext
    · exact recoveredExponent_defectCoordinate I a J
    · exact Subtype.ext (recoveredSubset_defectCoordinate I a J hJ)
  right_inv z := by
    rcases z with ⟨w, L, hL⟩
    apply Sigma.ext (defectWeight_recovered I w L)
    dsimp only
    refine (Subtype.heq_iff_coe_eq (fun K => ?_)).mpr ?_
    · rw [defectWeight_recovered]
    · exact defectCoordinate_recovered I w L hL

@[simp] theorem defectIndexEquiv_apply_fst (I : Finset ι) (a : ι →₀ ℕ)
    (J : {J : Finset ι // J ⊆ I}) :
    (defectIndexEquiv I (a, J)).1 = defectWeight I a J.val := rfl

@[simp] theorem defectIndexEquiv_apply_snd_val (I : Finset ι) (a : ι →₀ ℕ)
    (J : {J : Finset ι // J ⊆ I}) :
    (defectIndexEquiv I (a, J)).2.val = J.val ∩ activeSet I (defectWeight I a J.val) := rfl

@[simp] theorem defectIndexEquiv_symm_apply_fst (I : Finset ι) (w : ι →₀ ℕ)
    (L : DefectBlockIndex I w) :
    ((defectIndexEquiv I).symm ⟨w, L⟩).1 =
      w - subsetIndicator (activeSet I w \ L.val) := rfl

@[simp] theorem defectIndexEquiv_symm_apply_snd_val (I : Finset ι) (w : ι →₀ ℕ)
    (L : DefectBlockIndex I w) :
    ((defectIndexEquiv I).symm ⟨w, L⟩).2.val = (I \ activeSet I w) ∪ L.val := rfl

/-- Each nonzero cochain differential term preserves its defect weight. -/
theorem defectWeight_raise_insert (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι)
    (i : ι) (hi : i ∈ I \ J) :
    defectWeight I (a + Finsupp.single i 1) (insert i J) = defectWeight I a J := by
  unfold defectWeight
  rw [Finset.sdiff_insert]
  exact blockWeight_raise_erase a (I \ J) i hi

/-- The same differential term is ordinary creation in the active squarefree block. -/
theorem defectCoordinate_raise_insert (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (i : ι) (hi : i ∈ I \ J) :
    defectCoordinate I (a + Finsupp.single i 1) (insert i J) =
      insert i (defectCoordinate I a J) := by
  unfold defectCoordinate
  rw [defectWeight_raise_insert I a J i hi]
  have hiS := sdiff_subset_activeSet I a J hi
  ext j
  by_cases hji : j = i
  · subst j
    simp [hiS]
  · simp [hji]

theorem notMem_defectCoordinate_of_mem_sdiff (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (i : ι) (hi : i ∈ I \ J) :
    i ∉ defectCoordinate I a J := by
  exact fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp h).1

/-- An empty active set means precisely that all defect coordinates in `I` vanish. -/
theorem activeSet_eq_empty_iff (I : Finset ι) (w : ι →₀ ℕ) :
    activeSet I w = ∅ ↔ ∀ i ∈ I, w i = 0 := by
  constructor
  · intro h i hi
    by_contra hn
    have hm : i ∈ activeSet I w := (activeSet_mem I w i).mpr ⟨hn, hi⟩
    rw [h] at hm
    exact Finset.notMem_empty i hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases (activeSet_mem I w i).mp hi with ⟨hn, hI⟩
    exact hn (h i hI)

/-- Zero active blocks have the full coefficient monomial and no inside exponents. -/
theorem activeSet_defectWeight_eq_empty_iff (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (hJ : J ⊆ I) :
    activeSet I (defectWeight I a J) = ∅ ↔ J = I ∧ ∀ i ∈ I, a i = 0 := by
  rw [activeSet_eq_empty_iff]
  constructor
  · intro h
    have hIJ : I ⊆ J := by
      intro i hi
      by_contra hn
      have hz := h i hi
      simp [hi, hn] at hz
    refine ⟨Finset.Subset.antisymm hJ hIJ, ?_⟩
    intro i hi
    have hz := h i hi
    simpa [hIJ hi] using hz
  · rintro ⟨rfl, h⟩ i hi
    simpa using h i hi

/-- Outside exponents are retained exactly; zero active blocks need not have zero weight. -/
theorem defectWeight_apply_of_notMem (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (i : ι) (hi : i ∉ I) : defectWeight I a J i = a i := by
  simp [hi]

theorem defectWeight_eq_exponent_of_zero_active (I : Finset ι) (a : ι →₀ ℕ)
    (J : Finset ι) (hJ : J ⊆ I)
    (h : activeSet I (defectWeight I a J) = ∅) : defectWeight I a J = a := by
  have hJI := ((activeSet_defectWeight_eq_empty_iff I a J hJ).mp h).1
  simp [hJI, defectWeight, blockWeight]

/-- The defect grading records both cochain degree and coefficient degree. -/
theorem defectWeight_degree (I : Finset ι) (a : ι →₀ ℕ) (J : Finset ι)
    (hJ : J ⊆ I) :
    a.degree + I.card = (defectWeight I a J).degree + J.card := by
  have hd := blockWeight_degree a (I \ J)
  have hc := Finset.card_sdiff_add_card_eq_card hJ
  change a.degree + (I \ J).card = (defectWeight I a J).degree at hd
  omega

theorem recoveredExponent_degree (I : Finset ι) (w : ι →₀ ℕ) (L : Finset ι)
    (hL : L ⊆ activeSet I w) :
    (recoveredExponent I w L).degree + I.card = w.degree + (recoveredSubset I w L).card := by
  have h := defectWeight_degree I (recoveredExponent I w L) (recoveredSubset I w L)
    (recoveredSubset_subset I w L hL)
  rwa [defectWeight_recovered] at h

end Kourovka2135.BinaryDefectWeight
