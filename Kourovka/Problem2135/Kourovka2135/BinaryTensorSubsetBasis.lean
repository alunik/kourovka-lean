import Kourovka2135.BinaryTensorCoefficient

/-! Global-subset coordinates for the concrete binary coefficient module.

The coefficient basis is reindexed from finite subsets of the subtype `I`
to global finite subsets equipped with a proof that they lie in `I`.
This uses an actual equivalence of index types and preserves the module.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorSubsetBasis

open scoped CharTwo IsMulCommutative

section Subsets

variable {f : ℕ} (I : Finset (Fin f))

/-- The global subset indices for the coefficient module belonging to `I`. -/
abbrev Subsets := {J : Finset (Fin f) // J ⊆ I}

/-- Forget subtype membership proofs while retaining the subset condition. -/
def subsetEquiv : Finset I ≃ Subsets I :=
  Equiv.finsetSubtypeComm (fun i : Fin f => i ∈ I)

@[simp] theorem subsetEquiv_apply_val (J : Finset I) :
    (subsetEquiv I J).val = J.map ⟨Subtype.val, Subtype.val_injective⟩ := rfl

@[simp] theorem mem_subsetEquiv_iff (J : Finset I) (i : I) :
    (i : Fin f) ∈ (subsetEquiv I J).val ↔ i ∈ J :=
  Finset.mem_map' ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_subsetEquiv_symm_iff (J : Subsets I) (i : I) :
    i ∈ (subsetEquiv I).symm J ↔ (i : Fin f) ∈ J.val := by
  simpa only [Equiv.apply_symm_apply] using
    (mem_subsetEquiv_iff I ((subsetEquiv I).symm J) i).symm

@[simp] theorem card_subsetEquiv (J : Finset I) :
    (subsetEquiv I J).val.card = J.card := by
  rw [subsetEquiv_apply_val, Finset.card_map]

def emptyIndex : Subsets I := ⟨∅, Finset.empty_subset I⟩

def topIndex : Subsets I := ⟨I, Finset.Subset.refl I⟩

/-- Insertion with the proof needed to remain a global subset of `I`. -/
def insertIndex (i : Fin f) (hi : i ∈ I) (J : Subsets I) : Subsets I :=
  ⟨insert i J.val, Finset.insert_subset_iff.mpr ⟨hi, J.property⟩⟩

@[simp] theorem insertIndex_val (i : Fin f) (hi : i ∈ I) (J : Subsets I) :
    (insertIndex I i hi J).val = insert i J.val := rfl

@[simp] theorem subsetEquiv_empty : subsetEquiv I ∅ = emptyIndex I := by
  apply Subtype.ext
  simp [emptyIndex]

@[simp] theorem subsetEquiv_symm_empty : (subsetEquiv I).symm (emptyIndex I) = ∅ := by
  apply (subsetEquiv I).injective
  simp

@[simp] theorem subsetEquiv_insert (i : I) (J : Finset I) :
    subsetEquiv I (insert i J) = insertIndex I i i.property (subsetEquiv I J) := by
  apply Subtype.ext
  simp [insertIndex]

@[simp] theorem subsetEquiv_symm_insert (i : Fin f) (hi : i ∈ I) (J : Subsets I) :
    (subsetEquiv I).symm (insertIndex I i hi J) =
      insert ⟨i, hi⟩ ((subsetEquiv I).symm J) := by
  apply (subsetEquiv I).injective
  simp

end Subsets

variable (k : Type*) [CommRing k] {f : ℕ} (I : Finset (Fin f))

/-- The existing coefficient basis, now indexed by global subsets. -/
def basis : Module.Basis (Subsets I) k (BinaryTensorCoefficient.Carrier k I) :=
  (BinaryTensorCoefficient.basis k I).reindex (subsetEquiv I)

@[simp] theorem basis_apply (J : Subsets I) :
    basis k I J = BinaryTensorCoefficient.basis k I ((subsetEquiv I).symm J) :=
  Module.Basis.reindex_apply _ _ _

@[simp] theorem repr_basis_apply (v : BinaryTensorCoefficient.Carrier k I) (J : Subsets I) :
    (basis k I).repr v J =
      (BinaryTensorCoefficient.basis k I).repr v ((subsetEquiv I).symm J) :=
  Module.Basis.repr_reindex_apply _ _ _ _

@[simp] theorem basis_empty : basis k I (emptyIndex I) = 1 := by
  simp

variable [CharP k 2]

/-- Included generators insert their global index unless it is already present. -/
theorem generator_smul_basis_of_mem (i : Fin f) (hi : i ∈ I) (J : Subsets I) :
    BinaryExteriorAlgebra.generator k f i • basis k I J =
      if i ∈ J.val then 0 else basis k I (insertIndex I i hi J) := by
  calc
    BinaryExteriorAlgebra.generator k f i • basis k I J =
        if (⟨i, hi⟩ : I) ∈ (subsetEquiv I).symm J then 0
        else BinaryTensorCoefficient.basis k I
          (insert ⟨i, hi⟩ ((subsetEquiv I).symm J)) := by
      rw [basis_apply]
      exact BinaryTensorCoefficient.generator_smul_basis k I ⟨i, hi⟩ _
    _ = _ := by simp

/-- The complete global-index formula for the actual algebra action. -/
theorem generator_smul_basis (i : Fin f) (J : Subsets I) :
    BinaryExteriorAlgebra.generator k f i • basis k I J =
      if h : i ∈ I ∧ i ∉ J.val then basis k I (insertIndex I i h.1 J) else 0 := by
  by_cases hi : i ∈ I
  · rw [generator_smul_basis_of_mem k I i hi J]
    by_cases hij : i ∈ J.val <;> simp [hi, hij]
  · rw [BinaryTensorCoefficient.generator_smul_of_not_mem k I i hi]
    simp [hi]

theorem generator_smul_basis_zero (i : Fin f) (J : Subsets I)
    (h : i ∉ I ∨ i ∈ J.val) :
    BinaryExteriorAlgebra.generator k f i • basis k I J = 0 := by
  rw [generator_smul_basis]
  rcases h with h | h <;> simp [h]

theorem generator_smul_basis_insert (i : Fin f) (hi : i ∈ I) (J : Subsets I)
    (hij : i ∉ J.val) :
    BinaryExteriorAlgebra.generator k f i • basis k I J =
      basis k I (insertIndex I i hi J) := by
  rw [generator_smul_basis_of_mem k I i hi J]
  simp [hij]

/-- The full-subset basis vector is killed by every algebra generator. -/
theorem generator_smul_top (i : Fin f) :
    BinaryExteriorAlgebra.generator k f i • basis k I (topIndex I) = 0 := by
  apply generator_smul_basis_zero
  by_cases hi : i ∈ I
  · exact Or.inr hi
  · exact Or.inl hi

end Kourovka2135.BinaryTensorSubsetBasis
