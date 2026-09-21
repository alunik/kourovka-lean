import Kourovka2135.FinitePermutationMovingRank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Additive moving-rank bounds for several independent permutation orbits.
One chosen representative per orbit costs at most one dimension. The proof
uses actual independent differences and works in every characteristic. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IndependentOrbitMovingRank

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [Fintype ι] [DecidableEq ι]

/-- Extend the coordinate functionals of an independent finite family to V. -/
theorem exists_coordinateMap (v : ι → V) (hv : LinearIndependent k v) :
    ∃ r : V →ₗ[k] (ι → k), ∀ i, r (v i) = Pi.single i 1 := by
  classical
  let l := Fintype.linearCombination k v
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective l
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  refine ⟨r, fun i => ?_⟩
  have he := LinearMap.congr_fun hr (Pi.single i 1)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, l,
    Fintype.linearCombination_apply_single, one_smul] using he

/-- Differences to an idempotent representative map are independent away
from its fixed points. No action or orbit classification is needed here. -/
theorem differences_independent (v : ι → V) (hv : LinearIndependent k v)
    (rep : ι → ι) (hrep : ∀ i, rep (rep i) = rep i) :
    LinearIndependent k (fun i : {i : ι // rep i ≠ i} => v i - v (rep i)) := by
  classical
  obtain ⟨r, hr⟩ := exists_coordinateMap v hv
  let f (i : {i : ι // rep i ≠ i}) : Module.Dual k V :=
    (LinearMap.proj (i : ι)).comp r
  have hri (i : {i : ι // rep i ≠ i}) (j : ι) : rep j ≠ (i : ι) := by
    intro he
    apply i.property
    calc
      rep (i : ι) = rep (rep j) := congrArg rep he.symm
      _ = rep j := hrep j
      _ = i := he
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ f
  · intro i j hij
    have hji : (j : ι) ≠ (i : ι) := fun he => hij (Subtype.ext he.symm)
    simp only [f, LinearMap.comp_apply, LinearMap.proj_apply, map_sub, hr,
      Pi.single_apply, Ne.symm hji, Ne.symm (hri i j), ite_false, sub_self]
  · intro i
    simp only [f, LinearMap.comp_apply, LinearMap.proj_apply, map_sub, hr,
      Pi.single_apply, Ne.symm (hri i i), ite_false, ite_true, sub_zero]

/-- All nonrepresentative vectors contribute independent moving differences. -/
theorem card_le_finrank [FiniteDimensional k V]
    (A : V →ₗ[k] V) (v : ι → V) (hv : LinearIndependent k v)
    (rep : ι → ι) (hrep : ∀ i, rep (rep i) = rep i)
    (horbit : ∀ i, ∃ n : ℕ, (A ^ n) (v (rep i)) = v i) :
    Fintype.card {i : ι // rep i ≠ i} ≤
      Module.finrank k (LinearMap.range (A - LinearMap.id)) := by
  let d (i : {i : ι // rep i ≠ i}) : LinearMap.range (A - LinearMap.id) :=
    ⟨v i - v (rep i), by
      obtain ⟨n, hn⟩ := horbit i
      rw [← hn]
      exact FinitePermutationMovingRank.pow_sub_mem_range A n (v (rep i))⟩
  have hd : LinearIndependent k d :=
    LinearIndependent.of_comp (LinearMap.range (A - LinearMap.id)).subtype
      (differences_independent v hv rep hrep)
  exact hd.fintype_card_le_finrank

end Kourovka2135.IndependentOrbitMovingRank
