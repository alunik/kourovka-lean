import Kourovka2135.PSL33ModuleTwelve
import Kourovka2135.CocycleWordConcatenation

/-! Short, literal append/doubling certificates for four actual relations and
cocycle-derivative matrices. Every multiplication is checked by ordinary
kernel reduction; no finite-presentation assertion is used. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Kourovka2135.PSL33ModuleTwelveCohomology
open PSL33ModuleTwelve SL33ProjectiveData
open CocycleGeneratorEvaluation CocycleWordConcatenation

def gens : Fin 2 → Q := ![PSL33GoodSets.q a, PSL33GoodSets.q b]
def lifts : Fin 2 → S := ![a, b]
def ops : Fin 2 → Module.End k V := ![leftA.mulVecLin, leftB.mulVecLin]

theorem generators_generate : Subgroup.closure (Set.range gens) = ⊤ := by
  have he : Set.range gens = {PSL33GoodSets.q a, PSL33GoodSets.q b} := by
    exact Matrix.range_cons_cons_empty _ _ _
  rw [he]
  exact generating_projective

theorem generator_operators (i : Fin 2) : representation (gens i) = ops i := by
  fin_cases i
  · change representation (PSL33GoodSets.q a) = leftA.mulVecLin
    have h := congrArg Matrix.toLin' toMatrix_a
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_apply'] at h
    exact h
  · change representation (PSL33GoodSets.q b) = leftB.mulVecLin
    have h := congrArg Matrix.toLin' toMatrix_b
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_apply'] at h
    exact h

theorem wordValue_map (word : List (Fin 2)) :
    wordValue gens word = PSL33GoodSets.q (wordValue lifts word) := by
  induction word with
  | nil => exact (map_one _).symm
  | cons i word ih =>
      change gens i * wordValue gens word = PSL33GoodSets.q (lifts i * wordValue lifts word)
      rw [map_mul, ih]
      congr 1
      fin_cases i <;> rfl

def word0 : List (Fin 2) := [0]
def group0 : S := a
def matrix0 : Matrix (Fin 12) (Fin 12) k := leftA
def derivative0Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def derivative0 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative0Rows i j.1 j.2

theorem value0 : wordValue lifts word0 = group0 := by
  simp [word0, group0, wordValue, lifts]
theorem operator0 : operatorMatrix representation gens word0 = matrix0 := by
  simpa [operatorMatrix, word0, wordValue, gens, matrix0] using toMatrix_a
theorem jacobian0 : derivativeMatrix representation gens word0 = derivative0 := by
  ext i t
  rw [derivativeMatrix_entry]
  simp only [word0, wordDerivative, LinearMap.comp_zero, zero_add,
    LinearMap.proj_apply]
  change (Pi.single t.1 (Pi.single t.2 (1 : k)) : Fin 2 → Fin 12 → k) (0 : Fin 2) i = derivative0 i t
  rcases t with ⟨t, j⟩
  fin_cases i <;> fin_cases t <;> fin_cases j <;> decide

def word1 : List (Fin 2) := [1]
def group1 : S := b
def matrix1 : Matrix (Fin 12) (Fin 12) k := leftB
def derivative1Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]
def derivative1 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative1Rows i j.1 j.2

theorem value1 : wordValue lifts word1 = group1 := by
  simp [word1, group1, wordValue, lifts]
theorem operator1 : operatorMatrix representation gens word1 = matrix1 := by
  simpa [operatorMatrix, word1, wordValue, gens, matrix1] using toMatrix_b
theorem jacobian1 : derivativeMatrix representation gens word1 = derivative1 := by
  ext i t
  rw [derivativeMatrix_entry]
  simp only [word1, wordDerivative, LinearMap.comp_zero, zero_add,
    LinearMap.proj_apply]
  change (Pi.single t.1 (Pi.single t.2 (1 : k)) : Fin 2 → Fin 12 → k) (1 : Fin 2) i = derivative1 i t
  rcases t with ⟨t, j⟩
  fin_cases i <;> fin_cases t <;> fin_cases j <;> decide

def word2 : List (Fin 2) := word0 ++ word0
def group2 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide⟩
def matrix2 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative2Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def derivative2 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative2Rows i j.1 j.2

theorem value2 : wordValue lifts word2 = group2 := by
  rw [word2, wordValue_append, value0]
  decide

theorem operator2 : operatorMatrix representation gens word2 = matrix2 := by
  rw [word2, operatorMatrix_append, operator0]
  decide

theorem jacobian2 : derivativeMatrix representation gens word2 = derivative2 := by
  rw [word2, derivativeMatrix_append, operator0, jacobian0]
  decide

def word3 : List (Fin 2) := word1 ++ word1
def group3 : S := ⟨!![1, 1, 0;
    1, 2, 1;
    2, 1, 0], by decide⟩
def matrix3 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
def derivative3Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]]]
def derivative3 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative3Rows i j.1 j.2

theorem value3 : wordValue lifts word3 = group3 := by
  rw [word3, wordValue_append, value1]
  decide

theorem operator3 : operatorMatrix representation gens word3 = matrix3 := by
  rw [word3, operatorMatrix_append, operator1]
  decide

theorem jacobian3 : derivativeMatrix representation gens word3 = derivative3 := by
  rw [word3, derivativeMatrix_append, operator1, jacobian1]
  decide

def word4 : List (Fin 2) := word3 ++ word1
def group4 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide⟩
def matrix4 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative4Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def derivative4 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative4Rows i j.1 j.2

theorem value4 : wordValue lifts word4 = group4 := by
  rw [word4, wordValue_append, value3, value1]
  decide

theorem operator4 : operatorMatrix representation gens word4 = matrix4 := by
  rw [word4, operatorMatrix_append, operator3, operator1]
  decide

theorem jacobian4 : derivativeMatrix representation gens word4 = derivative4 := by
  rw [word4, derivativeMatrix_append, operator3, jacobian1, jacobian3]
  decide

def word5 : List (Fin 2) := word0 ++ word1
def group5 : S := ⟨!![1, 0, 1;
    1, 0, 2;
    0, 2, 0], by decide⟩
def matrix5 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
def derivative5Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]
def derivative5 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative5Rows i j.1 j.2

theorem value5 : wordValue lifts word5 = group5 := by
  rw [word5, wordValue_append, value0, value1]
  decide

theorem operator5 : operatorMatrix representation gens word5 = matrix5 := by
  rw [word5, operatorMatrix_append, operator0, operator1]
  decide

theorem jacobian5 : derivativeMatrix representation gens word5 = derivative5 := by
  rw [word5, derivativeMatrix_append, operator0, jacobian1, jacobian0]
  decide

def word6 : List (Fin 2) := word5 ++ word0
def group6 : S := ⟨!![2, 0, 2;
    1, 1, 1;
    1, 0, 0], by decide⟩
def matrix6 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
def derivative6Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]]
def derivative6 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative6Rows i j.1 j.2

theorem value6 : wordValue lifts word6 = group6 := by
  rw [word6, wordValue_append, value5, value0]
  decide

theorem operator6 : operatorMatrix representation gens word6 = matrix6 := by
  rw [word6, operatorMatrix_append, operator5, operator0]
  decide

theorem jacobian6 : derivativeMatrix representation gens word6 = derivative6 := by
  rw [word6, derivativeMatrix_append, operator5, jacobian0, jacobian5]
  decide

def word7 : List (Fin 2) := word6 ++ word1
def group7 : S := ⟨!![1, 2, 1;
    1, 1, 1;
    2, 0, 1], by decide⟩
def matrix7 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
def derivative7Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]]]
def derivative7 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative7Rows i j.1 j.2

theorem value7 : wordValue lifts word7 = group7 := by
  rw [word7, wordValue_append, value6, value1]
  decide

theorem operator7 : operatorMatrix representation gens word7 = matrix7 := by
  rw [word7, operatorMatrix_append, operator6, operator1]
  decide

theorem jacobian7 : derivativeMatrix representation gens word7 = derivative7 := by
  rw [word7, derivativeMatrix_append, operator6, jacobian1, jacobian6]
  decide

def word8 : List (Fin 2) := word7 ++ word1
def group8 : S := ⟨!![0, 1, 0;
    1, 1, 1;
    1, 1, 0], by decide⟩
def matrix8 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]
def derivative8Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]],
    ![![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1]]]
def derivative8 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative8Rows i j.1 j.2

theorem value8 : wordValue lifts word8 = group8 := by
  rw [word8, wordValue_append, value7, value1]
  decide

theorem operator8 : operatorMatrix representation gens word8 = matrix8 := by
  rw [word8, operatorMatrix_append, operator7, operator1]
  decide

theorem jacobian8 : derivativeMatrix representation gens word8 = derivative8 := by
  rw [word8, derivativeMatrix_append, operator7, jacobian1, jacobian7]
  decide

def word9 : List (Fin 2) := word8 ++ word8
def group9 : S := ⟨!![1, 1, 1;
    2, 0, 1;
    1, 2, 1], by decide⟩
def matrix9 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative9Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0], ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1]],
    ![![1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1]],
    ![![0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]],
    ![![1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0], ![1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1]],
    ![![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0], ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0], ![1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1]]]
def derivative9 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative9Rows i j.1 j.2

theorem value9 : wordValue lifts word9 = group9 := by
  rw [word9, wordValue_append, value8]
  decide

theorem operator9 : operatorMatrix representation gens word9 = matrix9 := by
  rw [word9, operatorMatrix_append, operator8]
  decide

theorem jacobian9 : derivativeMatrix representation gens word9 = derivative9 := by
  rw [word9, derivativeMatrix_append, operator8, jacobian8]
  decide

def word10 : List (Fin 2) := word9 ++ word9
def group10 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide⟩
def matrix10 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative10Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0]],
    ![![1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0]],
    ![![1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0]],
    ![![1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def derivative10 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative10Rows i j.1 j.2

theorem value10 : wordValue lifts word10 = group10 := by
  rw [word10, wordValue_append, value9]
  decide

theorem operator10 : operatorMatrix representation gens word10 = matrix10 := by
  rw [word10, operatorMatrix_append, operator9]
  decide

theorem jacobian10 : derivativeMatrix representation gens word10 = derivative10 := by
  rw [word10, derivativeMatrix_append, operator9, jacobian9]
  decide

def word11 : List (Fin 2) := word7 ++ word0
def group11 : S := ⟨!![0, 0, 2;
    1, 0, 2;
    2, 2, 2], by decide⟩
def matrix11 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
def derivative11Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]]]
def derivative11 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative11Rows i j.1 j.2

theorem value11 : wordValue lifts word11 = group11 := by
  rw [word11, wordValue_append, value7, value0]
  decide

theorem operator11 : operatorMatrix representation gens word11 = matrix11 := by
  rw [word11, operatorMatrix_append, operator7, operator0]
  decide

theorem jacobian11 : derivativeMatrix representation gens word11 = derivative11 := by
  rw [word11, derivativeMatrix_append, operator7, jacobian0, jacobian7]
  decide

def word12 : List (Fin 2) := word11 ++ word1
def group12 : S := ⟨!![0, 2, 2;
    2, 2, 0;
    2, 2, 2], by decide⟩
def matrix12 : Matrix (Fin 12) (Fin 12) k :=
  !![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
def derivative12Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0], ![1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0]],
    ![![0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]]]
def derivative12 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative12Rows i j.1 j.2

theorem value12 : wordValue lifts word12 = group12 := by
  rw [word12, wordValue_append, value11, value1]
  decide

theorem operator12 : operatorMatrix representation gens word12 = matrix12 := by
  rw [word12, operatorMatrix_append, operator11, operator1]
  decide

theorem jacobian12 : derivativeMatrix representation gens word12 = derivative12 := by
  rw [word12, derivativeMatrix_append, operator11, jacobian1, jacobian11]
  decide

def word13 : List (Fin 2) := word12 ++ word1
def group13 : S := ⟨!![1, 2, 0;
    2, 0, 0;
    2, 2, 2], by decide⟩
def matrix13 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
def derivative13Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0], ![1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0]],
    ![![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]],
    ![![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0], ![1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1]]]
def derivative13 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative13Rows i j.1 j.2

theorem value13 : wordValue lifts word13 = group13 := by
  rw [word13, wordValue_append, value12, value1]
  decide

theorem operator13 : operatorMatrix representation gens word13 = matrix13 := by
  rw [word13, operatorMatrix_append, operator12, operator1]
  decide

theorem jacobian13 : derivativeMatrix representation gens word13 = derivative13 := by
  rw [word13, derivativeMatrix_append, operator12, jacobian1, jacobian12]
  decide

def word14 : List (Fin 2) := word13 ++ word13
def group14 : S := ⟨!![2, 2, 0;
    2, 1, 0;
    1, 2, 1], by decide⟩
def matrix14 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
def derivative14Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]],
    ![![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]],
    ![![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1]],
    ![![1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0]],
    ![![0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0]],
    ![![1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0], ![1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1]],
    ![![1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0]],
    ![![0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0]],
    ![![1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1], ![1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0], ![1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0]],
    ![![1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0], ![1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0], ![1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0]]]
def derivative14 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative14Rows i j.1 j.2

theorem value14 : wordValue lifts word14 = group14 := by
  rw [word14, wordValue_append, value13]
  decide

theorem operator14 : operatorMatrix representation gens word14 = matrix14 := by
  rw [word14, operatorMatrix_append, operator13]
  decide

theorem jacobian14 : derivativeMatrix representation gens word14 = derivative14 := by
  rw [word14, derivativeMatrix_append, operator13, jacobian13]
  decide

def word15 : List (Fin 2) := word14 ++ word14
def group15 : S := ⟨!![2, 0, 0;
    0, 2, 0;
    1, 0, 1], by decide⟩
def matrix15 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative15Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1]],
    ![![1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0], ![1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1]],
    ![![0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1]],
    ![![1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0], ![1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1]],
    ![![1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0], ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0]],
    ![![0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1], ![0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]]]
def derivative15 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative15Rows i j.1 j.2

theorem value15 : wordValue lifts word15 = group15 := by
  rw [word15, wordValue_append, value14]
  decide

theorem operator15 : operatorMatrix representation gens word15 = matrix15 := by
  rw [word15, operatorMatrix_append, operator14]
  decide

theorem jacobian15 : derivativeMatrix representation gens word15 = derivative15 := by
  rw [word15, derivativeMatrix_append, operator14, jacobian14]
  decide

def word16 : List (Fin 2) := word15 ++ word15
def group16 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide⟩
def matrix16 : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def derivative16Rows : Fin 12 → Fin 2 → Fin 12 → k :=
  ![![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def derivative16 : Matrix (Fin 12) (Fin 2 × Fin 12) k :=
  fun i j => derivative16Rows i j.1 j.2

theorem value16 : wordValue lifts word16 = group16 := by
  rw [word16, wordValue_append, value15]
  decide

theorem operator16 : operatorMatrix representation gens word16 = matrix16 := by
  rw [word16, operatorMatrix_append, operator15]
  decide

theorem jacobian16 : derivativeMatrix representation gens word16 = derivative16 := by
  rw [word16, derivativeMatrix_append, operator15, jacobian15]
  decide

def words : Fin 4 → List (Fin 2) := ![word2, word4, word10, word16]
def certifiedDerivatives : Fin 4 → Matrix (Fin 12) (Fin 2 × Fin 12) k := ![derivative2, derivative4, derivative10, derivative16]

theorem actual_relations (i : Fin 4) : wordValue gens (words i) = 1 := by
  rw [wordValue_map]
  fin_cases i
  · change PSL33GoodSets.q (wordValue lifts word2) = 1
    rw [value2, show group2 = 1 from by decide, map_one]
  · change PSL33GoodSets.q (wordValue lifts word4) = 1
    rw [value4, show group4 = 1 from by decide, map_one]
  · change PSL33GoodSets.q (wordValue lifts word10) = 1
    rw [value10, show group10 = 1 from by decide, map_one]
  · change PSL33GoodSets.q (wordValue lifts word16) = 1
    rw [value16, show group16 = 1 from by decide, map_one]

theorem certified_derivative (i : Fin 4) :
    derivativeMatrix representation gens (words i) = certifiedDerivatives i := by
  fin_cases i
  · exact jacobian2
  · exact jacobian4
  · exact jacobian10
  · exact jacobian16

end Kourovka2135.PSL33ModuleTwelveCohomology
