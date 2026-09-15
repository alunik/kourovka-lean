import Kourovka.Problems.P21_40.Proof.Orbits
import Kourovka.Problems.P21_40.Proof.MatrixRoots
import Kourovka.Problems.P21_40.Proof.Eigenvalues
import Kourovka.Problems.P21_40.Proof.TraceKernel

/-!
# Finite automorphism orbits force bounded integral traces

Large-prime power injectivity becomes surjectivity on each subgroup with
finitely many automorphism orbits. Coherent roots and arithmetic finiteness
then bound the traces and the index of the trace kernel.
-/

namespace Kourovka.P21_40

/-- Every trace in the rational representation is an integer between `-n` and `n`. -/
theorem trace_bounds_of_finite_automorphism_orbits {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hG : HasFiniteAutomorphismOrbits G) :
    ∀ g : G, ∃ z : ℤ, Matrix.trace (matrixRepresentation G g) = (z : ℚ) ∧
      -(n : ℤ) ≤ z ∧ z ≤ n := by
  obtain ⟨p, _, hp, hinj⟩ := exists_prime_pow_injective n
  have hinjG : Function.Injective (fun g : G => g ^ p) := by
    intro g h heq
    apply Subtype.ext
    exact hinj (congrArg Subtype.val heq)
  have hsurj := surjective_pow_of_injective hG hinjG
  intro g
  obtain ⟨b, hb0, hb⟩ := exists_root_chain hsurj g
  have hchain (k : ℕ) : matrixRepresentation G (b (k + 1)) ^ p =
      matrixRepresentation G (b k) := by rw [← map_pow, hb]
  have hunit (k : ℕ) : IsUnit (matrixRepresentation G (b k)) :=
    (b k).val.isUnit
  have htrace := trace_bounds_of_root_chain hp (fun k => matrixRepresentation G (b k))
    hchain hunit
  simpa only [hb0, Fintype.card_fin] using htrace

/-- The trace kernel has finite index with an explicit bound depending only on dimension. -/
theorem traceKernel_index_of_finite_automorphism_orbits {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hG : HasFiniteAutomorphismOrbits G) :
    (traceKernel G).FiniteIndex ∧ (traceKernel G).index ≤ (2 * n + 1) ^ (n ^ 2) :=
  traceKernel_finiteIndex_and_index_le G (trace_bounds_of_finite_automorphism_orbits G hG)

end Kourovka.P21_40
