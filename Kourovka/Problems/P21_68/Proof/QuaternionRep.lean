import Kourovka.Problems.P21_68.Proof.Groups
import Kourovka.Problems.P21_68.Proof.QuaternionRep.Matrices

/-!
# The irreducible two-dimensional representation of `H`

The quaternion matrices extend across the automorphism of order three. We prove
irreducibility from the exact character norm, using mathlib's ordinary complex
representation theory.
-/

noncomputable section

namespace Kourovka.P21_68

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix CategoryTheory

/-- The order-three matrix representation of the cyclic complement. -/
def cyclicMatrix : C3 → Mat2 := fun c => matU ^ c.toAdd.val

lemma cyclicMatrix_mul (a b : C3) : cyclicMatrix (a * b) = cyclicMatrix a * cyclicMatrix b := by
  change matU ^ (a.toAdd + b.toAdd).val = matU ^ a.toAdd.val * matU ^ b.toAdd.val
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ matU_cube).symm

def cyclicMatrixHom : C3 →* Mat2 where
  toFun := cyclicMatrix
  map_one' := by rfl
  map_mul' := cyclicMatrix_mul

/-- Twice the order-three intertwining matrix has Gaussian-integer entries. -/
def integralCycleMatrix : Matrix (Fin 2) (Fin 2) GaussianInt :=
  !![⟨-1, -1⟩, ⟨-1, -1⟩; ⟨1, -1⟩, ⟨-1, 1⟩]

lemma integralCycleMatrix_compat (q : Q) :
    integralCycleMatrix * quaternionIntegralMatrix q =
      quaternionIntegralMatrix (qCycle q) * integralCycleMatrix := by
  revert q
  decide +kernel

lemma matU_eq_integralCycleMatrix :
    matU = (1 / 2 : ℂ) • integralCycleMatrix.map GaussianInt.toComplex := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matU, integralCycleMatrix, GaussianInt.toComplex_def,
      GaussianInt.toComplex, Complex.ext_iff]

lemma matU_quaternion_compat (q : Q) :
    matU * quaternionMatrix q = quaternionMatrix (qCycle q) * matU := by
  rw [quaternionMatrix_eq_integral q, quaternionMatrix_eq_integral (qCycle q),
    matU_eq_integralCycleMatrix, smul_mul_assoc, mul_smul_comm]
  congr 1
  have h := congrArg (fun M => GaussianInt.toComplex.mapMatrix M)
    (integralCycleMatrix_compat q)
  rw [map_mul, map_mul] at h
  exact h

lemma matU_pow_quaternion_compat (n : ℕ) (q : Q) :
    matU ^ n * quaternionMatrix q = quaternionMatrix ((qCycle ^ n) q) * matU ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      matU ^ (n + 1) * quaternionMatrix q = matU * (matU ^ n * quaternionMatrix q) := by
        rw [pow_succ', mul_assoc]
      _ = matU * (quaternionMatrix ((qCycle ^ n) q) * matU ^ n) := by rw [ih]
      _ = (matU * quaternionMatrix ((qCycle ^ n) q)) * matU ^ n := by rw [mul_assoc]
      _ = (quaternionMatrix (qCycle ((qCycle ^ n) q)) * matU) * matU ^ n := by
        rw [matU_quaternion_compat]
      _ = quaternionMatrix ((qCycle ^ (n + 1)) q) * matU ^ (n + 1) := by
        simp only [pow_succ', mul_assoc]
        rfl

lemma matrix_action_compat (c : C3) (q : Q) :
    cyclicMatrixHom c * quaternionMatrixHom q =
      quaternionMatrixHom (qAction c q) * cyclicMatrixHom c :=
  matU_pow_quaternion_compat c.toAdd.val q

/-- The explicit matrix representation of `Q₈ ⋊ C₃`. -/
def tetrahedralMatrix : H →* Mat2 where
  toFun h := quaternionMatrixHom h.left * cyclicMatrixHom h.right
  map_one' := by simp
  map_mul' a b := by
    change quaternionMatrixHom (a.left * qAction a.right b.left) *
      cyclicMatrixHom (a.right * b.right) = _
    rw [map_mul, map_mul]
    calc
      (quaternionMatrixHom a.left * quaternionMatrixHom (qAction a.right b.left)) *
          (cyclicMatrixHom a.right * cyclicMatrixHom b.right) =
        quaternionMatrixHom a.left *
          (quaternionMatrixHom (qAction a.right b.left) * cyclicMatrixHom a.right) *
            cyclicMatrixHom b.right := by simp only [mul_assoc]
      _ = quaternionMatrixHom a.left *
          (cyclicMatrixHom a.right * quaternionMatrixHom b.left) *
            cyclicMatrixHom b.right := by rw [matrix_action_compat]
      _ = _ := by simp only [mul_assoc]

/-- The unbundled two-dimensional representation. -/
def quaternionRepresentation : Representation ℂ H (Fin 2 → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp tetrahedralMatrix

/-- The ordinary complex representation used in the counterexample. -/
def quaternionRep : FDRep ℂ H := FDRep.of quaternionRepresentation

@[simp] lemma finrank_quaternionRep : Module.finrank ℂ quaternionRep = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

lemma quaternionRep_character (h : H) :
    quaternionRep.character h = (tetrahedralMatrix h).trace := by
  change LinearMap.trace ℂ (Fin 2 → ℂ) (Matrix.toLin' (tetrahedralMatrix h)) = _
  exact Matrix.trace_toLin'_eq _

/-- The integer-valued character, written in the eight quaternion coordinates. -/
def quaternionCharacterValue (h : H) : ℤ :=
  match h.left with
  | .a q => ![![2, 0, -2, 0], ![-1, 1, 1, -1], ![-1, -1, 1, 1]] h.right.toAdd q
  | .xa q => ![![0, 0, 0, 0], ![1, -1, -1, 1], ![-1, 1, 1, -1]] h.right.toAdd q

set_option maxHeartbeats 1000000 in
lemma quaternionRep_character_value (h : H) :
    quaternionRep.character h = (quaternionCharacterValue h : ℂ) := by
  rw [quaternionRep_character]
  rcases h with ⟨q, c⟩
  rcases q with q | q <;>
    dsimp only [tetrahedralMatrix, quaternionMatrixHom, quaternionMatrix,
      cyclicMatrixHom, cyclicMatrix, quaternionCharacterValue,
      MonoidHom.coe_mk, OneHom.coe_mk] <;>
    fin_cases q <;> fin_cases c <;>
    norm_num [tetrahedralMatrix, quaternionMatrixHom, quaternionMatrix,
      cyclicMatrixHom, cyclicMatrix, quaternionCharacterValue, matIPow, matI,
      matJ, matU, pow_succ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff, toAdd_ofAdd, ZMod.val, QuaternionGroup.one_def]

/-- The exact character norm before embedding the integers into the complex numbers. -/
lemma quaternionCharacterValue_norm :
    ∑ h : H, quaternionCharacterValue h * quaternionCharacterValue h⁻¹ = 24 := by
  decide +kernel

/-- The displayed two-dimensional complex representation is irreducible. -/
instance simple_quaternionRep : Simple quaternionRep := by
  apply (FDRep.simple_iff_char_is_norm_one quaternionRep).2
  simp_rw [quaternionRep_character_value, ← Int.cast_mul]
  rw [← Int.cast_sum, quaternionCharacterValue_norm, Nat.card_eq_fintype_card, card_H]
  norm_num

end Kourovka.P21_68
