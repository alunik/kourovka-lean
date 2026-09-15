import Kourovka.Problems.P21_40.Proof.FiniteOrbits
import Kourovka.Problems.P21_40.Proof.RationalFlag
import Kourovka.Problems.P21_40.Proof.ConjugateStructure
import Kourovka.Problems.P21_40.Proof.NumberFields

/-!
# An affirmative answer to Kourovka Problem 21.40

A rational linear group with finitely many abstract automorphism orbits
has a normal, rationally unitriangular subgroup of explicitly bounded
finite index. In particular, it is virtually torsion-free nilpotent and
virtually soluble. All dimensions and arbitrary, possibly infinitely
generated, subgroups are included.
-/

namespace Kourovka.P21_40

/-- A normal rationally unitriangular subgroup with index at most `(2n+1)^(n²)`.
The class bound uses natural-number subtraction, including dimension zero. -/
theorem structural_theorem {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hG : HasFiniteAutomorphismOrbits G) : StructuralConclusion G := by
  obtain ⟨hfinite, hindex⟩ := traceKernel_index_of_finite_automorphism_orbits G hG
  obtain ⟨P, hP⟩ := exists_conjugating_strict_upper (groupAlgebra G)
    (traceIdeal (groupAlgebra G)) (traceIdeal_le _)
    (fun _ hr _ ha => traceIdeal_mul_left hr ha)
    (fun _ hr => traceIdeal_isNilpotent hr)
  have hupper (g : G) (hg : g ∈ traceKernel G) :
      IsUpperUnitriangular
        ((P⁻¹ * (g : Matrix.GeneralLinearGroup (Fin n) ℚ) * P :
          Matrix.GeneralLinearGroup (Fin n) ℚ) : RationalMatrix n) := by
    let M : RationalMatrix n :=
      ((P⁻¹ * (g : Matrix.GeneralLinearGroup (Fin n) ℚ) * P :
        Matrix.GeneralLinearGroup (Fin n) ℚ) : RationalMatrix n)
    have heq : (↑P⁻¹ : RationalMatrix n) * (matrixRepresentation G g - 1) *
        (↑P : RationalMatrix n) = M - 1 := by
      change (↑P⁻¹ : RationalMatrix n) * (matrixRepresentation G g - 1) *
          (↑P : RationalMatrix n) =
        (↑P⁻¹ : RationalMatrix n) * matrixRepresentation G g * (↑P : RationalMatrix n) - 1
      rw [mul_sub, mul_one, sub_mul, Units.inv_mul]
    refine ⟨?_, ?_⟩
    · intro i
      have hz := hP _ hg i i le_rfl
      rw [heq] at hz
      exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply, Matrix.one_apply_eq] using hz)
    · intro i j hji
      have hz := hP _ hg i j hji.le
      rw [heq] at hz
      simpa only [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hji), sub_zero] using hz
  obtain ⟨hnil, hclass, htf⟩ := nilpotent_torsionFree_of_conjugate_upperUnitriangular P hupper
  exact ⟨traceKernel G, traceKernel_normal G, hfinite, hindex, hnil, hclass, htf, P, hupper⟩

/-- Rational linear groups with finitely many automorphism orbits are virtually nilpotent. -/
theorem virtually_nilpotent {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hG : HasFiniteAutomorphismOrbits G) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨K, _, hfinite, _, hnil, _⟩ := structural_theorem G hG
  exact ⟨K, hnil, hfinite⟩

/-- Rational linear groups with finitely many automorphism orbits are virtually soluble. -/
theorem virtually_solvable {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hG : HasFiniteAutomorphismOrbits G) : IsVirtuallySolvable G := by
  obtain ⟨K, hnil, hfinite⟩ := virtually_nilpotent G hG
  let : Group.IsNilpotent K := hnil
  exact ⟨K, hfinite, inferInstance⟩

/-- The full affirmative answer to Kourovka Notebook Problem 21.40. -/
theorem notebookStatement : NotebookStatement := fun _ G hG => virtually_solvable G hG

/-- Over every number field, there is a finite-index torsion-free nilpotent subgroup. -/
theorem numberField_structure {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hG : HasFiniteAutomorphismOrbits G) :
    ∃ N : Subgroup G, N.FiniteIndex ∧ Group.IsNilpotent N ∧
      (∀ g : N, IsOfFinOrder g → g = 1) :=
  numberField_structure_of_rational_structure (fun _ H hH => structural_theorem H hH) n G hG

/-- Linear groups over number fields with finitely many automorphism orbits
are virtually nilpotent. -/
theorem numberField_virtually_nilpotent {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hG : HasFiniteAutomorphismOrbits G) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨N, hfin, hnil, _⟩ := numberField_structure G hG
  exact ⟨N, hnil, hfin⟩

end Kourovka.P21_40
