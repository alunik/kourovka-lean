import Kourovka2135.SuzukiTensorBorelCohomology
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The scalar extension of the actual defining-field Suzuki tensor is the
actual tensor of the embedded natural twists. The equivalence is constructed
on the two pure-tensor bases and checked on every group matrix coefficient. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorBaseChange

open SuzukiTorusMovingRank SuzukiTensorNatural
open scoped TensorProduct PiTensorProduct

variable (k : Type) [Field k] [CharP k 2] (m : ℕ)
variable (I : Finset (Fin (2 * m + 1)))

/-- The pure-basis coefficient formula for every ambient group element. -/
theorem basis_coefficient (σ : K m →+* k) (g : G m) (a b : I → Fin 4) :
    (tensorBasis k m I).repr (representation k m I σ g (tensorBasis k m I b)) a =
      ∏ i : I, (σ (matrixHom m g (a i) (b i))) ^ (2 ^ i.val.val) := by
  simp only [tensorBasis, Basis.piTensorProduct_apply, representation_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  apply Finset.prod_congr rfl
  intro i _
  simp [naturalTwist_apply, Pi.basisFun_apply, Pi.single_apply]

variable [Algebra (K m) k]

def linearEquiv : k ⊗[K m] TensorSpace (K m) m I ≃ₗ[k] TensorSpace k m I :=
  ((tensorBasis (K m) m I).baseChange k).equiv (tensorBasis k m I) (Equiv.refl _)

omit [CharP k 2] in
theorem repr_linearEquiv (x : k ⊗[K m] TensorSpace (K m) m I) (a : I → Fin 4) :
    (tensorBasis k m I).repr (linearEquiv k m I x) a =
      ((tensorBasis (K m) m I).baseChange k).repr x a := by
  simp [linearEquiv, Module.Basis.equiv]

/-- A proved equivalence to the actual embedded tensor, with no comparison premise. -/
def representationEquiv :
    (RepresentationDensityBaseChange.baseChange k
      (representation (K m) m I (RingHom.id (K m)))).Equiv
      (representation k m I (algebraMap (K m) k)) := by
  refine Representation.Equiv.mk (linearEquiv k m I) ?_
  intro g
  apply ((tensorBasis (K m) m I).baseChange k).ext
  intro a
  change linearEquiv k m I
      (RepresentationDensityBaseChange.baseChange k
        (representation (K m) m I (RingHom.id (K m))) g
        (((tensorBasis (K m) m I).baseChange k) a)) =
    representation k m I (algebraMap (K m) k) g
      (linearEquiv k m I (((tensorBasis (K m) m I).baseChange k) a))
  rw [show linearEquiv k m I (((tensorBasis (K m) m I).baseChange k) a) =
    tensorBasis k m I a by
      simp only [linearEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]]
  rw [Module.Basis.baseChange_apply, RepresentationDensityBaseChange.baseChange_apply,
    LinearMap.baseChange_tmul]
  apply (tensorBasis k m I).repr.injective
  ext b
  rw [repr_linearEquiv, Module.Basis.baseChange_repr_tmul,
    basis_coefficient, basis_coefficient]
  simp [Algebra.smul_def]

theorem finrank_H1_le_count :
    Module.finrank k (groupCohomology
      (Rep.of (representation k m I (algebraMap (K m) k))) 1) ≤
      SuzukiTensorBorelCohomology.supportCount m I := by
  rw [← RepresentationCohomologyAlternative.finrank_cohomology_eq _ _
    (representationEquiv k m I) 1]
  exact SuzukiTensorBorelCohomology.finrank_H1_baseChange_le_count m I k

omit [Algebra (K m) k] in
/-- The coefficient embedding alone suffices for the concrete tensor endpoint. -/
theorem finrank_H1_embedding_le_count (σ : K m →+* k) :
    Module.finrank k (groupCohomology (Rep.of (representation k m I σ)) 1) ≤
      SuzukiTensorBorelCohomology.supportCount m I := by
  let := σ.toAlgebra
  exact finrank_H1_le_count k m I

end Kourovka2135.SuzukiTensorBaseChange
