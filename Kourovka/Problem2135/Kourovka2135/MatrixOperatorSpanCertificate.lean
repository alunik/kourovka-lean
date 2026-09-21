import Kourovka2135.RepresentationSpanCertificate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A rectangular matrix certificate for the span of actual representation operators.

Rows are actual pairs of matrix coordinates; columns are actual group elements.
A checked right inverse of this coordinate matrix proves surjectivity of the
operator sum and hence of the actual group-algebra action. No numerical rank,
irreducibility or absolute-irreducibility premise is substituted for this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MatrixOperatorSpanCertificate

variable {k G n I : Type*} [Field k] [Monoid G]
variable [Fintype n] [DecidableEq n] [Fintype I]

/-- The entries and right inverse of an actual operator-coordinate matrix
give a surjective finite linear combination of the actual operators. -/
theorem linearCombination_surjective_of_right_inverse
    (ρ : Representation k G (n → k)) (elements : I → G)
    (S : Matrix (n × n) I k) (C : Matrix I (n × n) k)
    (hoperators : ∀ i, LinearMap.toMatrix' (ρ (elements i)) =
      fun a b => S (a, b) i)
    (hSC : S * C = 1) :
    Function.Surjective (Fintype.linearCombination k (ρ ∘ elements)) := by
  classical
  intro T
  let v : n × n → k := fun ij => LinearMap.toMatrix' T ij.1 ij.2
  have hv : S.mulVec (C.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hSC, Matrix.one_mulVec]
  refine ⟨C.mulVec v, ?_⟩
  apply LinearMap.toMatrix'.injective
  ext a b
  have h := congrFun hv (a, b)
  simp only [Fintype.linearCombination_apply, map_sum, map_smul,
    Matrix.sum_apply, Function.comp_apply, hoperators]
  change (∑ i, (C.mulVec v) i * S (a, b) i) = LinearMap.toMatrix' T a b
  simpa only [Matrix.mulVec, dotProduct, v, mul_comm] using h

/-- A fully checked coordinate right inverse proves actual full matrix-algebra image. -/
theorem asAlgebraHom_surjective_of_right_inverse
    (ρ : Representation k G (n → k)) (elements : I → G)
    (S : Matrix (n × n) I k) (C : Matrix I (n × n) k)
    (hoperators : ∀ i, LinearMap.toMatrix' (ρ (elements i)) =
      fun a b => S (a, b) i)
    (hSC : S * C = 1) : Function.Surjective ρ.asAlgebraHom :=
  RepresentationSpanCertificate.asAlgebraHom_surjective ρ elements
    (linearCombination_surjective_of_right_inverse ρ elements S C hoperators hSC)

end Kourovka2135.MatrixOperatorSpanCertificate
