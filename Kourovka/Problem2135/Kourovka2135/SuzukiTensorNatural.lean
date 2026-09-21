import Kourovka2135.SuzukiTorusMovingRank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RepresentationTheory.Basic

/-! Actual tensors of the natural Frobenius twists of the concrete Suzuki
matrix group. These are genuine tensor representations, with their actual
pure tensor basis; no irreducible-module classification is assumed. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.SuzukiTensorNatural

open SuzukiTorusMovingRank BenderSuzuki.MatrixGroups
open scoped Matrix MatrixGroups TensorProduct PiTensorProduct

variable (k : Type u) [Field k] [CharP k 2] (m : ℕ)

def twistEmbedding (σ : K m →+* k) (n : ℕ) : K m →+* k :=
  (iterateFrobenius k 2 n).comp σ

@[simp] theorem twistEmbedding_apply (σ : K m →+* k) (n : ℕ) (a : K m) :
    twistEmbedding k m σ n a = (σ a) ^ (2 ^ n) := rfl

def matrixHom : G m →* Matrix (Fin 4) (Fin 4) (K m) :=
  (Units.coeHom _).comp (SuzukiMatrixSubgroup m).subtype

def naturalTwist (σ : K m →+* k) (n : ℕ) :
    Representation k (G m) (Fin 4 → k) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) k ≃ₐ[k]
    Module.End k (Fin 4 → k)).toMonoidHom.comp
      ((twistEmbedding k m σ n).mapMatrix.toMonoidHom.comp (matrixHom m))

theorem naturalTwist_apply (σ : K m →+* k) (n : ℕ) (g : G m)
    (v : Fin 4 → k) (i : Fin 4) :
    naturalTwist k m σ n g v i =
      ∑ j : Fin 4, (σ (matrixHom m g i j)) ^ (2 ^ n) * v j := by
  change (Matrix.toLin' _ v) i = _
  rw [Matrix.toLin'_apply]
  rfl

def rootElement (a b : K m) : G m :=
  ⟨SuzukiRootGL m a b, Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩

def weyl : G m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem naturalTwist_root_first (σ : K m →+* k) (n : ℕ) (a b : K m) :
    naturalTwist k m σ n (rootElement m a b) (Pi.basisFun k (Fin 4) 0) =
      Pi.basisFun k (Fin 4) 0 := by
  ext i
  fin_cases i <;>
    simp [naturalTwist_apply, matrixHom, rootElement, SuzukiRootGL,
      SuzukiRootMatrix, Fin.sum_univ_four, Pi.basisFun_apply]

theorem naturalTwist_torus_first (σ : K m →+* k) (n : ℕ) (x : (K m)ˣ) :
    naturalTwist k m σ n (torusHom m x) (Pi.basisFun k (Fin 4) 0) =
      (σ ((x : K m) ^ (1 + 2 ^ m))) ^ (2 ^ n) • Pi.basisFun k (Fin 4) 0 := by
  ext i
  fin_cases i <;>
    simp [naturalTwist_apply, matrixHom, torusHom, SuzukiTorusGL,
      SuzukiTorusMatrix, Fin.sum_univ_four, Pi.basisFun_apply]

theorem naturalTwist_weyl_first (σ : K m →+* k) (n : ℕ) :
    naturalTwist k m σ n (weyl m) (Pi.basisFun k (Fin 4) 0) =
      Pi.basisFun k (Fin 4) 3 := by
  ext i
  fin_cases i <;>
    simp [naturalTwist_apply, matrixHom, weyl, SuzukiWeylGL,
      SuzukiWeylMatrix, Fin.sum_univ_four, Pi.basisFun_apply]

variable (I : Finset (Fin (2 * m + 1)))

abbrev TensorSpace := ⨂[k] _i : I, (Fin 4 → k)

def tensorBasis : Module.Basis (I → Fin 4) k (TensorSpace k m I) :=
  Basis.piTensorProduct fun _ : I => Pi.basisFun k (Fin 4)

instance tensorFinite : Module.Finite k (TensorSpace k m I) :=
  (tensorBasis k m I).finiteDimensional_of_finite

omit [CharP k 2] in
theorem finrank_tensor : Module.finrank k (TensorSpace k m I) = 4 ^ I.card := by
  rw [Module.finrank_eq_card_basis (tensorBasis k m I)]
  simp

def representation (σ : K m →+* k) : Representation k (G m) (TensorSpace k m I) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun i : I => naturalTwist k m σ i.val.val)

theorem representation_tprod (σ : K m →+* k) (g : G m) (v : I → (Fin 4 → k)) :
    representation k m I σ g (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (fun i : I => naturalTwist k m σ i.val.val g (v i)) :=
  PiTensorProduct.map_tprod _ _

def highest : TensorSpace k m I := tensorBasis k m I (fun _ => 0)
def lowest : TensorSpace k m I := tensorBasis k m I (fun _ => 3)

omit [CharP k 2] in
theorem highest_eq_tprod : highest k m I =
    PiTensorProduct.tprod k (fun _ : I => Pi.basisFun k (Fin 4) 0) := by
  simp [highest, tensorBasis]

omit [CharP k 2] in
theorem lowest_eq_tprod : lowest k m I =
    PiTensorProduct.tprod k (fun _ : I => Pi.basisFun k (Fin 4) 3) := by
  simp [lowest, tensorBasis]

omit [CharP k 2] in
theorem highest_ne_zero : highest k m I ≠ 0 := (tensorBasis k m I).ne_zero _

omit [CharP k 2] in
theorem highest_ne_lowest (hI : I.Nonempty) : highest k m I ≠ lowest k m I := by
  intro h
  have he := (tensorBasis k m I).injective h
  obtain ⟨i, hi⟩ := hI
  have := congrFun he (⟨i, hi⟩ : I)
  exact (by decide : (0 : Fin 4) ≠ 3) this

theorem representation_root_highest (σ : K m →+* k) (a b : K m) :
    representation k m I σ (rootElement m a b) (highest k m I) = highest k m I := by
  simp only [highest_eq_tprod, representation_tprod, naturalTwist_root_first]

theorem representation_weyl_highest (σ : K m →+* k) :
    representation k m I σ (weyl m) (highest k m I) = lowest k m I := by
  simp only [highest_eq_tprod, lowest_eq_tprod, representation_tprod,
    naturalTwist_weyl_first]

theorem representation_torus_highest (σ : K m →+* k) (x : (K m)ˣ) :
    representation k m I σ (torusHom m x) (highest k m I) =
      (∏ i : I, (σ ((x : K m) ^ (1 + 2 ^ m))) ^ (2 ^ i.val.val)) • highest k m I := by
  simp only [highest_eq_tprod, representation_tprod, naturalTwist_torus_first]
  exact (PiTensorProduct.tprod k).map_smul_univ _ _

end Kourovka2135.SuzukiTensorNatural
