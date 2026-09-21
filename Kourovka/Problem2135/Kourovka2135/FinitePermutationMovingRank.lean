import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Moving-rank lower bounds from actual independent vectors. These statements
apply in every characteristic, including permutation cycles and swaps whose
orders are divisible by the coefficient characteristic. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.FinitePermutationMovingRank

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (A : V →ₗ[k] V)

/-- A difference along an iterate is a sum of actual moving vectors. -/
theorem pow_sub_mem_range (n : ℕ) (v : V) :
    (A ^ n) v - v ∈ LinearMap.range (A - LinearMap.id) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : A ((A ^ n) v) - (A ^ n) v ∈
          LinearMap.range (A - LinearMap.id) := ⟨(A ^ n) v, rfl⟩
      have he : (A ^ (n + 1)) v - v =
          (A ((A ^ n) v) - (A ^ n) v) + ((A ^ n) v - v) := by
        rw [pow_succ', Module.End.mul_apply]
        abel
      rw [he]
      exact Submodule.add_mem _ hstep ih

/-- Independent vectors in one actual orbit give all but one moving dimension. -/
theorem card_sub_one_le_finrank_of_orbit [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] (v : ι → V) (hv : LinearIndependent k v)
    (i₀ : ι) (horbit : ∀ i : ι, ∃ n : ℕ, (A ^ n) (v i₀) = v i) :
    Fintype.card ι - 1 ≤ Module.finrank k (LinearMap.range (A - LinearMap.id)) := by
  classical
  have hd : LinearIndependent k (fun i : {i : ι // i ≠ i₀} => v i - v i₀) := by
    simpa only [vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub k v i₀).mp hv.affineIndependent
  let d (i : {i : ι // i ≠ i₀}) : LinearMap.range (A - LinearMap.id) :=
    ⟨v i - v i₀, by
      obtain ⟨n, hn⟩ := horbit i
      rw [← hn]
      exact pow_sub_mem_range A n (v i₀)⟩
  have hdi : LinearIndependent k d :=
    LinearIndependent.of_comp (LinearMap.range (A - LinearMap.id)).subtype hd
  simpa using hdi.fintype_card_le_finrank

/-- Nonfixed eigenvectors lie in the actual image of A-id. -/
theorem mem_range_of_eigenvalue_ne_one (c : k) (v : V)
    (hc : c ≠ 1) (hv : A v = c • v) :
    v ∈ LinearMap.range (A - LinearMap.id) := by
  refine ⟨(c - 1)⁻¹ • v, ?_⟩
  have hn : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  change A ((c - 1)⁻¹ • v) - (c - 1)⁻¹ • v = v
  rw [map_smul, hv, ← smul_sub]
  have he : c • v - v = (c - 1) • v := by rw [sub_smul, one_smul]
  rw [he, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Each member of an independent family of nonfixed eigenvectors contributes
one dimension to the actual moving image. -/
theorem card_le_finrank_of_eigenvectors [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] (v : ι → V) (hv : LinearIndependent k v)
    (c : ι → k) (hc : ∀ i, c i ≠ 1) (he : ∀ i, A (v i) = c i • v i) :
    Fintype.card ι ≤ Module.finrank k (LinearMap.range (A - LinearMap.id)) := by
  let d (i : ι) : LinearMap.range (A - LinearMap.id) :=
    ⟨v i, mem_range_of_eigenvalue_ne_one A (c i) (v i) (hc i) (he i)⟩
  have hd : LinearIndependent k d :=
    LinearIndependent.of_comp (LinearMap.range (A - LinearMap.id)).subtype hv
  exact hd.fintype_card_le_finrank

/-- Differences across disjoint independent pairs stay independent. -/
theorem paired_differences_independent {ι : Type*} [Fintype ι]
    (v : ι × Bool → V) (hv : LinearIndependent k v) :
    LinearIndependent k (fun i => v (i, true) - v (i, false)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let c : ι × Bool → k := fun p => if p.2 then a p.1 else -a p.1
  have hs : ∑ p, c p • v p = 0 := by
    rw [Fintype.sum_prod_type]
    simpa [c, Fintype.sum_bool, sub_eq_add_neg, add_comm] using ha
  have hz := Fintype.linearIndependent_iff.mp hv c hs (i, true)
  simpa [c] using hz

/-- Disjoint actual swaps provide one moving dimension each, even in
characteristic two. Only one direction of each swap is needed. -/
theorem card_le_finrank_of_pairs [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] (v : ι × Bool → V) (hv : LinearIndependent k v)
    (he : ∀ i, A (v (i, false)) = v (i, true)) :
    Fintype.card ι ≤ Module.finrank k (LinearMap.range (A - LinearMap.id)) := by
  let d (i : ι) : LinearMap.range (A - LinearMap.id) :=
    ⟨v (i, true) - v (i, false), ⟨v (i, false), by
      change A (v (i, false)) - v (i, false) = v (i, true) - v (i, false)
      rw [he i]⟩⟩
  have hd : LinearIndependent k d :=
    LinearIndependent.of_comp (LinearMap.range (A - LinearMap.id)).subtype
      (paired_differences_independent v hv)
  exact hd.fintype_card_le_finrank

end Kourovka2135.FinitePermutationMovingRank
