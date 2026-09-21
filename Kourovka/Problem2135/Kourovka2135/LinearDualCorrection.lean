import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Elementary finite-dimensional duality used to correct conjugation of a linear functional. -/

set_option autoImplicit false
universe u v w
namespace Kourovka2135
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

theorem exists_linear_functional_ne_zero {x : W} (hx : x ≠ 0) :
    ∃ ell : W →ₗ[K] K, ell x ≠ 0 :=
  Module.Projective.exists_dual_ne_zero K hx

theorem bilinear_surjective_of_nondegenerate [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) : Function.Surjective B := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := K) (V := V)).symm).mp
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro x hx
  change x = 0
  apply hB x
  intro y
  exact congrArg (fun f : V →ₗ[K] K => f y) hx

theorem exists_linear_factor_of_surjective (q : W →ₗ[K] V) (hq : Function.Surjective q)
    (d : W →ₗ[K] K) (hd : q.ker ≤ d.ker) :
    ∃ e : V →ₗ[K] K, e.comp q = d := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  refine ⟨d.comp s, ?_⟩
  apply LinearMap.ext
  intro x
  have hq0 : q (s (q x) - x) = 0 := by
    rw [map_sub]
    have hh := congrArg (fun f : V →ₗ[K] V => f (q x)) hs
    exact sub_eq_zero.mpr hh
  have hd0 : d (s (q x) - x) = 0 := hd hq0
  change d (s (q x)) = d x
  exact sub_eq_zero.mp (by simpa only [map_sub] using hd0)

theorem exists_bilinear_correction [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (q : W →ₗ[K] V) (hq : Function.Surjective q)
    (d : W →ₗ[K] K) (hd : q.ker ≤ d.ker) :
    ∃ v : V, ∀ x : W, B v (q x) = d x := by
  obtain ⟨e, he⟩ := exists_linear_factor_of_surjective q hq d hd
  obtain ⟨v, hv⟩ := bilinear_surjective_of_nondegenerate B hB e
  refine ⟨v, ?_⟩
  intro x
  rw [hv]
  exact congrArg (fun f : W →ₗ[K] K => f x) he

end Kourovka2135
