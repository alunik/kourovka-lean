/-
Adapted from the Qiuzhen CFSG project (https://github.com/Qiuzhen-CFSG/CFSG).
Released under Apache 2.0 license as described in that repository's LICENSE.
Source: Theory/Representation/Unbundled.lean, lines 32-66.
Commit: 96b2a02085dc678f3e0a97b334c31ada599c55fd.
Original file SHA256: fd5d7b435d54d7bfa071168a1f6bcea9a3dfe16625cc95e7b40b08d17277b760.
Only the generic finite-coordinate trace lemma is selected.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The trace of a coordinate permutation with linear coefficient maps is
exactly the sum of the traces at its fixed coordinates. The coordinate map
need not be bijective. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.MonomialTrace
open Module
open scoped BigOperators

theorem trace_pi_map_perm {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Type*} [AddCommGroup M] [Module R M]
    (b : Basis κ R M) (e : ι → ι) (L : ι → M →ₗ[R] M)
    (T : (ι → M) →ₗ[R] (ι → M))
    (hT : ∀ x i, T x i = L i (x (e i))) :
    LinearMap.trace R (ι → M) T =
      ∑ i : ι, if e i = i then LinearMap.trace R M (L i) else 0 := by
  classical
  let B : Basis (Σ _ : ι, κ) R (ι → M) := Pi.basis (fun _ : ι => b)
  rw [LinearMap.trace_eq_matrix_trace R B T]
  simp only [Matrix.trace]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : e i = i
  · rw [ite_eq_left h]
    rw [LinearMap.trace_eq_matrix_trace R b (L i)]
    simp only [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro a ha
    change (LinearMap.toMatrix B B T) ⟨i, a⟩ ⟨i, a⟩ =
      (LinearMap.toMatrix b b (L i)) a a
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [B, hT]
    rw [h]
    simp
  · rw [ite_eq_right h]
    rw [Finset.sum_eq_zero]
    intro a ha
    change (LinearMap.toMatrix B B T) ⟨i, a⟩ ⟨i, a⟩ = 0
    rw [LinearMap.toMatrix_apply]
    have hne : i ≠ e i := fun hi => h hi.symm
    simp [B, hT, hne]


end Kourovka2135.MonomialTrace
