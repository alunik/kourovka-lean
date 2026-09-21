import Kourovka2135.PSL27Generation
import Kourovka2135.SubrepresentationCertificate
import Kourovka2135.RepresentationDensityBaseChange

/-! Two genuine absolutely irreducible three-dimensional summands of the
actual binary PSL2(7) permutation heart. Explicit inclusions and projections
split the six coordinates. Generator equations establish invariant images
using proved generation of the actual group. Checked operator spans then
prove full endomorphism-algebra image, also after every field extension. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace Kourovka2135.PSL27BinaryHeartDecomposition
open PSL27BinaryHeartCoordinates PSL27BinaryHeartData
open scoped Matrix
abbrev k := ZMod 2
abbrev V3 := Fin 3 → k

/-- `false` selects the first block and `true` the second block. -/
def blockIndex (b : Bool) (i : Fin 3) : Fin 6 :=
  if b then ⟨i.val + 3, by omega⟩ else ⟨i.val, by omega⟩

def inclusionMatrix (b : Bool) : Matrix (Fin 6) (Fin 3) k :=
  fun i j => splitting i (blockIndex b j)

def projectionMatrix (b : Bool) : Matrix (Fin 3) (Fin 6) k :=
  fun i j => splittingInverse (blockIndex b i) j

def componentU (b : Bool) : Matrix (Fin 3) (Fin 3) k := if b then U2 else U1
def componentW (b : Bool) : Matrix (Fin 3) (Fin 3) k := if b then W2 else W1

private theorem projection_inclusion : ∀ b : Bool,
    projectionMatrix b * inclusionMatrix b = 1 := by decide +kernel
private theorem projection_cross : ∀ b : Bool,
    projectionMatrix b * inclusionMatrix (!b) = 0 := by decide +kernel
private theorem sum_projections :
    inclusionMatrix false * projectionMatrix false +
      inclusionMatrix true * projectionMatrix true = 1 := by decide +kernel
private theorem inclusion_U : ∀ b : Bool,
    heartU * inclusionMatrix b = inclusionMatrix b * componentU b := by decide +kernel
private theorem inclusion_W : ∀ b : Bool,
    heartW * inclusionMatrix b = inclusionMatrix b * componentW b := by decide +kernel
private theorem componentU_inverse : ∀ b : Bool,
    componentU b * componentU b ^ 6 = 1 ∧ componentU b ^ 6 * componentU b = 1 :=
  by decide +kernel
private theorem componentW_inverse : ∀ b : Bool,
    componentW b * componentW b = 1 := by decide +kernel

private def matrixEquiv {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (hAB : A * B = 1) (hBA : B * A = 1) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one])

def inclusion (b : Bool) : V3 →ₗ[k] V := (inclusionMatrix b).mulVecLin
def projection (b : Bool) : V →ₗ[k] V3 := (projectionMatrix b).mulVecLin

@[simp] theorem projection_inclusion_apply (b : Bool) (v : V3) :
    projection b (inclusion b v) = v := by
  change projectionMatrix b *ᵥ (inclusionMatrix b *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, projection_inclusion, Matrix.one_mulVec]

@[simp] theorem projection_cross_apply (b : Bool) (v : V3) :
    projection b (inclusion (!b) v) = 0 := by
  change projectionMatrix b *ᵥ (inclusionMatrix (!b) *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, projection_cross, Matrix.zero_mulVec]

theorem sum_projections_apply (v : V) :
    inclusion false (projection false v) + inclusion true (projection true v) = v := by
  change inclusionMatrix false *ᵥ (projectionMatrix false *ᵥ v) +
    inclusionMatrix true *ᵥ (projectionMatrix true *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    sum_projections, Matrix.one_mulVec]

theorem inclusion_injective (b : Bool) : Function.Injective (inclusion b) :=
  Function.LeftInverse.injective (projection_inclusion_apply b)

private theorem action_U (b : Bool) (v : V3) :
    representation U (inclusion b v) = inclusion b ((componentU b).mulVecLin v) := by
  have h : representation U = heartU.mulVecLin := by
    apply LinearMap.toMatrix'.injective
    rw [toMatrix_U]
    exact (LinearMap.toMatrix'_toLin' heartU).symm
  rw [h]
  change heartU *ᵥ (inclusionMatrix b *ᵥ v) = inclusionMatrix b *ᵥ (componentU b *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, inclusion_U]

private theorem action_W (b : Bool) (v : V3) :
    representation W (inclusion b v) = inclusion b ((componentW b).mulVecLin v) := by
  have h : representation W = heartW.mulVecLin := by
    apply LinearMap.toMatrix'.injective
    rw [toMatrix_W]
    exact (LinearMap.toMatrix'_toLin' heartW).symm
  rw [h]
  change heartW *ᵥ (inclusionMatrix b *ᵥ v) = inclusionMatrix b *ᵥ (componentW b *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, inclusion_W]

private theorem generator_actions (b : Bool) (g : G) (hg : g ∈ ({U, W} : Set G)) :
    ∃ A : V3 ≃ₗ[k] V3, ∀ v, representation g (inclusion b v) = inclusion b (A v) := by
  rcases (show g = U ∨ g = W by simpa using hg) with rfl | rfl
  · exact ⟨matrixEquiv (componentU b) (componentU b ^ 6)
      (componentU_inverse b).1 (componentU_inverse b).2, action_U b⟩
  · exact ⟨matrixEquiv (componentW b) (componentW b)
      (componentW_inverse b) (componentW_inverse b), action_W b⟩

/-- The actual action restricted to the corresponding invariant image. -/
def component (b : Bool) : Representation k G V3 :=
  SubrepresentationCertificate.representation representation (inclusion b)
    (inclusion_injective b) {U, W} PSL27Generation.closure_U_W (generator_actions b)

theorem component_intertwines (b : Bool) (g : G) (v : V3) :
    inclusion b (component b g v) = representation g (inclusion b v) :=
  SubrepresentationCertificate.representation_intertwines _ _ (inclusion_injective b)
    _ PSL27Generation.closure_U_W (generator_actions b) g v

theorem toMatrix_component_U (b : Bool) :
    LinearMap.toMatrix' (component b U) = componentU b := by
  have h : component b U = (componentU b).mulVecLin :=
    SubrepresentationCertificate.representation_eq_of_intertwines _ _ (inclusion_injective b)
      _ PSL27Generation.closure_U_W (generator_actions b) _ _ (action_U b)
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

theorem toMatrix_component_W (b : Bool) :
    LinearMap.toMatrix' (component b W) = componentW b := by
  have h : component b W = (componentW b).mulVecLin :=
    SubrepresentationCertificate.representation_eq_of_intertwines _ _ (inclusion_injective b)
      _ PSL27Generation.closure_U_W (generator_actions b) _ _ (action_W b)
  rw [h]
  exact LinearMap.toMatrix'_toLin' _

/-- The actual direct-sum coordinate equivalence. -/
def sumEquiv : (V3 × V3) ≃ₗ[k] V where
  toFun v := inclusion false v.1 + inclusion true v.2
  invFun v := (projection false v, projection true v)
  left_inv v := by
    apply Prod.ext
    · simp only [map_add, projection_inclusion_apply]
      rw [show projection false (inclusion true v.2) = 0 from projection_cross_apply false v.2]
      exact add_zero _
    · simp only [map_add, projection_inclusion_apply]
      rw [show projection true (inclusion false v.1) = 0 from projection_cross_apply true v.1]
      exact zero_add _
  right_inv := sum_projections_apply
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' c v := by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

/-- The two stable three-dimensional components recover the full genuine heart action. -/
def sumRepresentationEquiv : ((component false).prod (component true)).Equiv representation :=
  Representation.Equiv.mk sumEquiv (fun g => LinearMap.ext (fun v => by
    change inclusion false (component false g v.1) + inclusion true (component true g v.2) =
      representation g (inclusion false v.1 + inclusion true v.2)
    rw [component_intertwines, component_intertwines, map_add]))

/-- The same decomposition on the original augmentation quotient. -/
def heartDecomposition : heartRepresentation.Equiv
    ((component false).prod (component true)) := heartEquiv.trans sumRepresentationEquiv.symm

private def wordValue : List Bool → G
  | [] => 1
  | false :: w => U * wordValue w
  | true :: w => W * wordValue w

private def wordMatrix (b : Bool) : List Bool → Matrix (Fin 3) (Fin 3) k
  | [] => 1
  | false :: w => componentU b * wordMatrix b w
  | true :: w => componentW b * wordMatrix b w

private theorem word_matrix (b : Bool) (w : List Bool) :
    LinearMap.toMatrix' (component b (wordValue w)) = wordMatrix b w := by
  induction w with
  | nil => rw [wordValue, map_one, LinearMap.toMatrix'_one, wordMatrix]
  | cons c w ih =>
    cases c
    · rw [wordValue, map_mul, LinearMap.toMatrix'_mul, toMatrix_component_U, ih, wordMatrix]
    · rw [wordValue, map_mul, LinearMap.toMatrix'_mul, toMatrix_component_W, ih, wordMatrix]

private theorem wordMatrix_false (w : List Bool) : wordMatrix false w = wordMatrix1 w := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp only [wordMatrix, wordMatrix1, componentU, componentW, Bool.false_eq_true, ↓reduceIte, ih]

private theorem wordMatrix_true (w : List Bool) : wordMatrix true w = wordMatrix2 w := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp only [wordMatrix, wordMatrix2, componentU, componentW, ↓reduceIte, ih]

/-- The nine actual group operators span all endomorphisms on each summand. -/
theorem asAlgebraHom_surjective (b : Bool) : Function.Surjective (component b).asAlgebraHom := by
  cases b
  · apply MatrixOperatorSpanCertificate.asAlgebraHom_surjective_of_right_inverse
      (component false) (fun i => wordValue (words1 i)) coordinateMatrix1 coordinateInverse1
      _ coordinate_inverse1
    intro i
    rw [word_matrix, wordMatrix_false, operators1_checked]
    rfl
  · apply MatrixOperatorSpanCertificate.asAlgebraHom_surjective_of_right_inverse
      (component true) (fun i => wordValue (words2 i)) coordinateMatrix2 coordinateInverse2
      _ coordinate_inverse2
    intro i
    rw [word_matrix, wordMatrix_true, operators2_checked]
    rfl

theorem isIrreducible (b : Bool) : (component b).IsIrreducible :=
  RepresentationDensityBaseChange.isIrreducible_of_asAlgebraHom_surjective
    (component b) (asAlgebraHom_surjective b)

theorem baseChange_asAlgebraHom_surjective (L : Type*) [Field L] [Algebra k L] (b : Bool) :
    Function.Surjective (RepresentationDensityBaseChange.baseChange L (component b)).asAlgebraHom :=
  RepresentationDensityBaseChange.baseChange_asAlgebraHom_surjective (component b)
    (asAlgebraHom_surjective b)

theorem baseChange_isIrreducible (L : Type*) [Field L] [Algebra k L] (b : Bool) :
    (RepresentationDensityBaseChange.baseChange L (component b)).IsIrreducible :=
  RepresentationDensityBaseChange.baseChange_isIrreducible L (component b)
    (asAlgebraHom_surjective b)

end Kourovka2135.PSL27BinaryHeartDecomposition
