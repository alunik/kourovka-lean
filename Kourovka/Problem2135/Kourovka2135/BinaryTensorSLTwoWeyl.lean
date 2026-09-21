import Kourovka2135.BinaryTensorSLTwo

/-! The genuine Weyl matrix complements the actual tensor subset basis.

The matrix is defined with determinant one over an arbitrary field. Its
minus sign disappears only after passage to the characteristic-two
coefficient field. The resulting top-to-empty formula is used in the
independent elementary simplicity proof for the tensor modules.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwo

/-- The determinant-one Weyl matrix, before specialization to characteristic two. -/
def weyl (F : Type v) [Field F] : SL2 F :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem weyl_val (F : Type v) [Field F] :
    (weyl F).val = !![0, -1; 1, 0] := rfl

end Kourovka2135.SLTwo

namespace Kourovka2135.BinaryTensorSLTwo

open BinaryTensorSubsetBasis
open scoped TensorProduct PiTensorProduct CharTwo

section Indices

variable {f : ℕ} (I : Finset (Fin f))

/-- The subset obtained by swapping both natural basis choices in every tensor factor. -/
def complementIndex (J : Subsets I) : Subsets I := ⟨I \ J.val, Finset.sdiff_subset⟩

@[simp] theorem complementIndex_val (J : Subsets I) :
    (complementIndex I J).val = I \ J.val := rfl

@[simp] theorem complementIndex_top : complementIndex I (topIndex I) = emptyIndex I := by
  apply Subtype.ext
  simp [complementIndex, topIndex, emptyIndex]

@[simp] theorem complementIndex_empty : complementIndex I (emptyIndex I) = topIndex I := by
  apply Subtype.ext
  simp [complementIndex, topIndex, emptyIndex]

end Indices

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] (σ : F →+* k) {f : ℕ} (I : Finset (Fin f))

/-- Every natural binary Frobenius twist has the same Weyl swap. -/
theorem naturalTwist_weyl (n : ℕ) (x : Fin 2 → k) :
    naturalTwist k σ n (SLTwo.weyl F) x = ![x 1, x 0] := by
  funext j
  fin_cases j <;>
    simp [naturalTwist_apply, SLTwo.weyl_val, Fin.sum_univ_two, CharTwo.neg_eq]

/-- The actual natural Weyl action reverses the subset choice at each factor. -/
theorem naturalTwist_weyl_subsetBits (J : Subsets I) (i : I) :
    naturalTwist k σ i.val.val (SLTwo.weyl F)
        (Pi.basisFun k (Fin 2) (subsetBits I J i)) =
      Pi.basisFun k (Fin 2) (subsetBits I (complementIndex I J) i) := by
  rw [naturalTwist_weyl]
  funext j
  by_cases hi : i.val ∈ J.val <;> fin_cases j <;>
    simp [subsetBits, complementIndex, hi, i.property]

/-- The genuine tensor-product Weyl map complements the tensor basis index. -/
theorem tensorRepresentation_weyl_basis (J : Subsets I) :
    tensorRepresentation k σ I (SLTwo.weyl F) (tensorBasis k I J) =
      tensorBasis k I (complementIndex I J) := by
  rw [tensorBasis_apply, tensorRepresentation_tprod, tensorBasis_apply]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  exact naturalTwist_weyl_subsetBits k σ I J i

/-- The coefficient-space Weyl action is proved through the actual tensor equivalence. -/
theorem representation_weyl_basis (J : Subsets I) :
    representation k σ I (SLTwo.weyl F) (basis k I J) =
      basis k I (complementIndex I J) := by
  rw [representation_apply, tensorEquiv_symm_basis,
    tensorRepresentation_weyl_basis, tensorEquiv_basis]

/-- The top line is sent to the empty basis vector, including empty support. -/
@[simp] theorem representation_weyl_top :
    representation k σ I (SLTwo.weyl F) (basis k I (topIndex I)) =
      basis k I (emptyIndex I) := by
  simpa only [complementIndex_top] using representation_weyl_basis k σ I (topIndex I)

/-- The empty basis vector is sent back to the top. -/
@[simp] theorem representation_weyl_empty :
    representation k σ I (SLTwo.weyl F) (basis k I (emptyIndex I)) =
      basis k I (topIndex I) := by
  simpa only [complementIndex_empty] using representation_weyl_basis k σ I (emptyIndex I)

end Kourovka2135.BinaryTensorSLTwo
