import Kourovka2135.CocycleWordOperators

/-! Concatenation formulas for actual word values and cocycle derivatives.
They support short append/doubling certificates with literal intermediate
matrices, avoiding repeated expansion of long nested word expressions. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.CocycleWordConcatenation
open CocycleGeneratorEvaluation

variable {k G : Type u} {V : Type v} {I : Type w} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

theorem wordValue_append (gens : I → G) (a b : List I) :
    wordValue gens (a ++ b) = wordValue gens a * wordValue gens b := by
  induction a with
  | nil => simp [wordValue]
  | cons i a ih => simp only [List.cons_append, wordValue, ih, mul_assoc]

theorem wordDerivative_append (ρ : Representation k G V) (gens : I → G) (a b : List I) :
    wordDerivative ρ gens (a ++ b) =
      (ρ (wordValue gens a)).comp (wordDerivative ρ gens b) + wordDerivative ρ gens a := by
  induction a with
  | nil => simp [wordDerivative, wordValue, Module.End.one_eq_id]
  | cons i a ih =>
      change (ρ (gens i)).comp (wordDerivative ρ gens (a ++ b)) + LinearMap.proj i =
        (ρ (gens i * wordValue gens a)).comp (wordDerivative ρ gens b) +
          ((ρ (gens i)).comp (wordDerivative ρ gens a) + LinearMap.proj i)
      rw [ih, map_mul, Module.End.mul_eq_comp, LinearMap.comp_add,
        LinearMap.comp_assoc, add_assoc]

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Fintype I] [DecidableEq I]
variable (ρ : Representation k G (n → k)) (gens : I → G)

/-- The actual group operator in standard coordinates. -/
def operatorMatrix (word : List I) : Matrix n n k :=
  LinearMap.toMatrix' (ρ (wordValue gens word))

/-- The actual cocycle derivative on flattened generator coordinates. -/
def derivativeMatrix (word : List I) : Matrix n (I × n) k :=
  LinearMap.toMatrix' ((wordDerivative ρ gens word).comp
    (CocycleWordOperators.flatten (k := k) (I := I) (n := n)).symm.toLinearMap)

omit [Fintype I] [DecidableEq I] in
theorem operatorMatrix_append (a b : List I) :
    operatorMatrix ρ gens (a ++ b) = operatorMatrix ρ gens a * operatorMatrix ρ gens b := by
  rw [operatorMatrix, wordValue_append, map_mul, LinearMap.toMatrix'_mul]
  rfl

theorem derivativeMatrix_append (a b : List I) :
    derivativeMatrix ρ gens (a ++ b) =
      operatorMatrix ρ gens a * derivativeMatrix ρ gens b + derivativeMatrix ρ gens a := by
  unfold derivativeMatrix operatorMatrix
  rw [wordDerivative_append, LinearMap.add_comp, map_add,
    LinearMap.comp_assoc, LinearMap.toMatrix'_comp]

/-- Read back an individual certified derivative entry. -/
theorem derivativeMatrix_entry (word : List I) (i : n) (j : I × n) :
    derivativeMatrix ρ gens word i j =
      wordDerivative ρ gens word (Pi.single j.1 (Pi.single j.2 1)) i := by
  rw [derivativeMatrix, LinearMap.toMatrix'_apply, LinearMap.comp_apply]
  have hv : (CocycleWordOperators.flatten (k := k) (I := I) (n := n)).symm
      (Pi.single j 1) = Pi.single j.1 (Pi.single j.2 1) := by
    ext a b
    by_cases ha : a = j.1 <;> by_cases hb : b = j.2 <;>
      simp [CocycleWordOperators.flatten, Prod.ext_iff, ha, hb]
  exact congrArg (fun f : I → n → k => wordDerivative ρ gens word f i) hv

end Matrix
end Kourovka2135.CocycleWordConcatenation
