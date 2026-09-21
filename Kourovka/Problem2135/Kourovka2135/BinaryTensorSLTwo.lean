import Kourovka2135.SLTwoUnipotent
import Kourovka2135.BinaryTensorTorus
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.CharP.Frobenius

/-! The actual tensor product of natural Frobenius-twisted SL2 modules.

The first natural basis vector records a present squarefree index, and the
second records an absent index. Thus upper unipotents insert indices. The
tensor module is identified with the existing exterior coefficient module
by an explicit equivalence of their actual bases.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.BinaryTensorSLTwo

open BinaryTensorSubsetBasis
open scoped TensorProduct PiTensorProduct IsMulCommutative

section Indices

variable {f : ℕ} (I : Finset (Fin f))

/-- Present indices use the first natural vector; absent indices use the second. -/
def subsetBits (J : Subsets I) (i : I) : Fin 2 := if i.val ∈ J.val then 0 else 1

@[simp] theorem subsetBits_eq_zero (J : Subsets I) (i : I) :
    subsetBits I J i = 0 ↔ i.val ∈ J.val := by
  by_cases hi : i.val ∈ J.val <;> simp [subsetBits, hi]

/-- Recover the global subset from its first-vector choices. -/
def bitsSubset (p : I → Fin 2) : Subsets I :=
  subsetEquiv I (Finset.univ.filter fun i => p i = 0)

@[simp] theorem bitsSubset_mem (p : I → Fin 2) (i : I) :
    i.val ∈ (bitsSubset I p).val ↔ p i = 0 := by
  simp [bitsSubset]

/-- The genuine equivalence of tensor basis indices with squarefree subsets. -/
def bitsEquiv : (I → Fin 2) ≃ Subsets I where
  toFun := bitsSubset I
  invFun := subsetBits I
  left_inv p := by
    funext i
    by_cases hp : p i = 0
    · simp [subsetBits, hp]
    · have hp' : p i = 1 := by omega
      simp [subsetBits, hp']
  right_inv J := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ I
    · exact (bitsSubset_mem I (subsetBits I J) ⟨i, hi⟩).trans
        (subsetBits_eq_zero I J ⟨i, hi⟩)
    · exact iff_of_false (fun h => hi ((bitsSubset I (subsetBits I J)).property h))
        (fun h => hi (J.property h))

@[simp] theorem bitsEquiv_apply (p : I → Fin 2) : bitsEquiv I p = bitsSubset I p := rfl

@[simp] theorem bitsEquiv_symm_apply (J : Subsets I) :
    (bitsEquiv I).symm J = subsetBits I J := rfl

end Indices

section TensorBasis

variable (k : Type u) [Field k] {f : ℕ} (I : Finset (Fin f))

/-- The actual tensor of two-dimensional natural spaces indexed by `I`. -/
abbrev TensorSpace := ⨂[k] _i : I, (Fin 2 → k)

def rawTensorBasis : Module.Basis (I → Fin 2) k (TensorSpace k I) :=
  Basis.piTensorProduct fun _ : I => Pi.basisFun k (Fin 2)

/-- Reindex the actual tensor basis by global squarefree subsets. -/
def tensorBasis : Module.Basis (Subsets I) k (TensorSpace k I) :=
  (rawTensorBasis k I).reindex (bitsEquiv I)

theorem tensorBasis_apply (J : Subsets I) :
    tensorBasis k I J = PiTensorProduct.tprod k
      (fun i : I => Pi.basisFun k (Fin 2) (subsetBits I J i)) := by
  simp only [tensorBasis, rawTensorBasis, Module.Basis.reindex_apply,
    bitsEquiv_symm_apply, Basis.piTensorProduct_apply]

/-- An explicit basis-preserving identification with the exterior coefficient space. -/
def tensorEquiv : TensorSpace k I ≃ₗ[k] BinaryTensorCoefficient.Carrier k I :=
  (tensorBasis k I).equiv (basis k I) (Equiv.refl _)

@[simp] theorem tensorEquiv_basis (J : Subsets I) :
    tensorEquiv k I (tensorBasis k I J) = basis k I J := by
  simp [tensorEquiv]

@[simp] theorem tensorEquiv_symm_basis (J : Subsets I) :
    (tensorEquiv k I).symm (basis k I J) = tensorBasis k I J := by
  apply (tensorEquiv k I).injective
  simp

end TensorBasis

section Representation

variable {F : Type v} [Field F]
variable (k : Type u) [Field k] [CharP k 2]
variable (σ : F →+* k) {f : ℕ} (I : Finset (Fin f))

/-- Apply the embedding followed by the chosen binary Frobenius power. -/
def twistEmbedding (n : ℕ) : F →+* k := (iterateFrobenius k 2 n).comp σ

@[simp] theorem twistEmbedding_apply (n : ℕ) (x : F) :
    twistEmbedding k σ n x = (σ x) ^ (2 ^ n) := rfl

/-- The actual natural two-dimensional representation with one Frobenius twist. -/
def naturalTwist (n : ℕ) : Representation k (SLTwo.SL2 F) (Fin 2 → k) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (Matrix.SpecialLinearGroup.toLin'.comp
      (Matrix.SpecialLinearGroup.map (twistEmbedding k σ n)))

theorem naturalTwist_apply (n : ℕ) (g : SLTwo.SL2 F) (x : Fin 2 → k) (j : Fin 2) :
    naturalTwist k σ n g x j = ∑ l : Fin 2, (σ (g.val j l)) ^ (2 ^ n) * x l := by
  change (Matrix.toLin' (Matrix.SpecialLinearGroup.map (twistEmbedding k σ n) g).val x) j = _
  rw [Matrix.toLin'_apply]
  rfl

/-- Upper unipotents use the upper-triangular natural-matrix convention. -/
theorem naturalTwist_uni (n : ℕ) (t : F) (x : Fin 2 → k) :
    naturalTwist k σ n (SLTwo.uni t) x =
      ![x 0 + (σ t) ^ (2 ^ n) * x 1, x 1] := by
  funext j
  fin_cases j <;> simp [naturalTwist_apply, SLTwo.uni_val, Fin.sum_univ_two]

/-- The two natural basis weights are inverse torus characters. -/
theorem naturalTwist_tor (n : ℕ) (r : Fˣ) (x : Fin 2 → k) :
    naturalTwist k σ n (SLTwo.tor r) x =
      ![(σ (r : F)) ^ (2 ^ n) * x 0,
        (σ ((r⁻¹ : Fˣ) : F)) ^ (2 ^ n) * x 1] := by
  funext j
  fin_cases j <;> simp [naturalTwist_apply, SLTwo.tor_val, Fin.sum_univ_two]

/-- Tensor the actual natural twists, using the functorial tensor map. -/
def tensorRepresentation : Representation k (SLTwo.SL2 F) (TensorSpace k I) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun i : I => naturalTwist k σ i.val.val)

theorem tensorRepresentation_tprod (g : SLTwo.SL2 F) (x : I → (Fin 2 → k)) :
    tensorRepresentation k σ I g (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i : I => naturalTwist k σ i.val.val g (x i)) := by
  exact PiTensorProduct.map_tprod _ _

/-- Transfer this actual tensor representation to the coefficient module. -/
def representation : Representation k (SLTwo.SL2 F) (BinaryTensorCoefficient.Carrier k I) :=
  (tensorEquiv k I).conjRingEquiv.toMonoidHom.comp (tensorRepresentation k σ I)

theorem representation_apply (g : SLTwo.SL2 F) (v : BinaryTensorCoefficient.Carrier k I) :
    representation k σ I g v = tensorEquiv k I
      (tensorRepresentation k σ I g ((tensorEquiv k I).symm v)) := rfl

/-- The tensor/exterior identification intertwines the full SL2 action by construction. -/
theorem representation_tensorEquiv (g : SLTwo.SL2 F) (v : TensorSpace k I) :
    representation k σ I g (tensorEquiv k I v) =
      tensorEquiv k I (tensorRepresentation k σ I g v) := by
  rw [representation_apply, LinearEquiv.symm_apply_apply]

end Representation

end Kourovka2135.BinaryTensorSLTwo
