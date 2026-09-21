import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Prod

/-! A finitely generated nonzero semisimple isotypic module is either one copy
of its type or has an actual surjective linear map onto two copies.

Only module semisimplicity is assumed, not semisimplicity of the coefficient
ring. The proof constructs the quotient from the finite product decomposition.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.IsotypicTwoCopyQuotient

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (S : Type w) [AddCommGroup S] [Module R S]

/-- Projection to the first two coordinates of a product with at least two factors. -/
def firstTwo (n : ℕ) : (Fin (n + 2) → S) →ₗ[R] S × S :=
  (LinearMap.proj (0 : Fin (n + 2))).prod (LinearMap.proj (1 : Fin (n + 2)))

theorem firstTwo_surjective (n : ℕ) : Function.Surjective (firstTwo R S n) := by
  intro z
  refine ⟨fun i => if i = 0 then z.1 else z.2, ?_⟩
  simp [firstTwo]

/-- A finite semisimple isotypic decomposition gives either an actual
one-copy equivalence or an actual quotient onto two copies. Finite means
finitely generated as an R-module; the carrier need not be a finite type. -/
theorem linearEquiv_or_surjective_prod
    [IsSemisimpleModule R M] [Module.Finite R M] [Nontrivial M]
    (h : IsIsotypicOfType R M S) :
    Nonempty (M ≃ₗ[R] S) ∨ ∃ f : M →ₗ[R] S × S, Function.Surjective f := by
  obtain ⟨n, ⟨e⟩⟩ := h.linearEquiv_fun
  cases n with
  | zero =>
      exact ((not_subsingleton M) e.injective.subsingleton).elim
  | succ n =>
      cases n with
      | zero =>
          exact Or.inl ⟨e.trans (LinearEquiv.funUnique (Fin 1) R S)⟩
      | succ n =>
          exact Or.inr ⟨(firstTwo R S n).comp e.toLinearMap,
            (firstTwo_surjective R S n).comp e.surjective⟩

/-- Excluding every actual two-copy quotient forces a single-copy equivalence. -/
theorem nonempty_linearEquiv_of_no_surjective_prod
    [IsSemisimpleModule R M] [Module.Finite R M] [Nontrivial M]
    (h : IsIsotypicOfType R M S)
    (hno : ∀ f : M →ₗ[R] S × S, ¬ Function.Surjective f) :
    Nonempty (M ≃ₗ[R] S) := by
  rcases linearEquiv_or_surjective_prod R M S h with he | ⟨f, hf⟩
  · exact he
  · exact (hno f hf).elim

end Kourovka2135.IsotypicTwoCopyQuotient
