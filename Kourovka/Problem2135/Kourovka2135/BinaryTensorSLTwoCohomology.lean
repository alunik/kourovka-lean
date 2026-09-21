import Kourovka2135.BinaryTensorSLTwoCohomologyTransfer
import Kourovka2135.BinaryAdditiveTorusBounds

/-! Low-degree cohomology bounds for the actual tensor products of binary
Frobenius-twisted natural SL2 modules. All action transport and finiteness
premises are discharged by the independent transfer module.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryTensorSLTwoCohomology

open CategoryTheory BinaryTensorSLTwoRestriction

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

include hcard in
/-- The actual tensor coefficient has first cohomology of dimension at most one. -/
theorem finrank_H1_le (hf : 2 ≤ f) :
    Module.finrank k (groupCohomology (ambient k I σ) 1) ≤ 1 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard
  exact (finrank_le_fixed k I σ hcard r 0 (Or.inl rfl)).trans
    (BinaryAdditiveTorusBounds.finrank_fixed_one_le k I σ hcard r hr hf)

include hcard in
/-- Every nonsingleton support has zero-dimensional actual first SL2 cohomology. -/
theorem finrank_H1_eq_zero (hf : 2 ≤ f) (hI : I.card ≠ 1) :
    Module.finrank k (groupCohomology (ambient k I σ) 1) = 0 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard
  have h := finrank_le_fixed k I σ hcard r 0 (Or.inl rfl)
  rw [BinaryAdditiveTorusBounds.fixed_one_eq_bot k I σ hcard r hr hf hI] at h
  exact Nat.eq_zero_of_le_zero (by simpa using h)

include hcard in
/-- Nonsingleton supports have genuinely vanishing first cohomology. -/
theorem subsingleton_H1 (hf : 2 ≤ f) (hI : I.card ≠ 1) :
    Subsingleton (groupCohomology (ambient k I σ) 1) := by
  have := finiteDimensional_ambient k I σ hcard 0
  exact Module.finrank_zero_iff.mp (finrank_H1_eq_zero k I σ hcard hf hI)

include hcard in
/-- The natural Frobenius-twisted coefficient has H2 dimension at most one for f ≥ 3. -/
theorem finrank_H2_singleton_le (hf : 3 ≤ f) (i : Fin f) :
    Module.finrank k (groupCohomology (ambient k {i} σ) 2) ≤ 1 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard
  exact (finrank_le_fixed k {i} σ hcard r 1 (Or.inr rfl)).trans
    (BinaryAdditiveTorusBounds.finrank_fixed_two_le k σ hcard r hr hf i)

/-- The natural coefficient over four parameters has zero-dimensional actual H2. -/
theorem finrank_H2_singleton_at_two_eq_zero (hcard₂ : Fintype.card F = 2 ^ 2) (i : Fin 2) :
    Module.finrank k (groupCohomology (ambient k {i} σ) 2) = 0 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard₂
  have h := finrank_le_fixed k {i} σ hcard₂ r 1 (Or.inr rfl)
  rw [BinaryAdditiveTorusBounds.fixed_two_at_two_eq_bot k σ hcard₂ r hr i] at h
  exact Nat.eq_zero_of_le_zero (by simpa using h)

/-- The exceptional four-parameter H2 statement is genuine vanishing. -/
theorem subsingleton_H2_singleton_at_two
    (hcard₂ : Fintype.card F = 2 ^ 2) (i : Fin 2) :
    Subsingleton (groupCohomology (ambient k {i} σ) 2) := by
  have := finiteDimensional_ambient k {i} σ hcard₂ 1
  exact Module.finrank_zero_iff.mp (finrank_H2_singleton_at_two_eq_zero k σ hcard₂ i)

include hcard in
/-- H1 bound directly on the genuine tensor of natural Frobenius twists. -/
theorem finrank_tensor_H1_le (hf : 2 ≤ f) :
    Module.finrank k
      (groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ I)) 1) ≤ 1 := by
  rw [(tensorCohomologyIso k I σ 1).toLinearEquiv.finrank_eq]
  exact finrank_H1_le k I σ hcard hf

include hcard in
/-- H1 vanishing dimension directly on every nonsingleton genuine tensor support. -/
theorem finrank_tensor_H1_eq_zero (hf : 2 ≤ f) (hI : I.card ≠ 1) :
    Module.finrank k
      (groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ I)) 1) = 0 := by
  rw [(tensorCohomologyIso k I σ 1).toLinearEquiv.finrank_eq]
  exact finrank_H1_eq_zero k I σ hcard hf hI

include hcard in
/-- H2 bound directly on a single genuine Frobenius-twisted natural factor. -/
theorem finrank_tensor_H2_singleton_le (hf : 3 ≤ f) (i : Fin f) :
    Module.finrank k
      (groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ {i})) 2) ≤ 1 := by
  rw [(tensorCohomologyIso k {i} σ 2).toLinearEquiv.finrank_eq]
  exact finrank_H2_singleton_le k σ hcard hf i

/-- Over four parameters the genuine natural tensor factor has H2 dimension zero. -/
theorem finrank_tensor_H2_singleton_at_two_eq_zero
    (hcard₂ : Fintype.card F = 2 ^ 2) (i : Fin 2) :
    Module.finrank k
      (groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ {i})) 2) = 0 := by
  rw [(tensorCohomologyIso k {i} σ 2).toLinearEquiv.finrank_eq]
  exact finrank_H2_singleton_at_two_eq_zero k σ hcard₂ i

end Kourovka2135.BinaryTensorSLTwoCohomology
