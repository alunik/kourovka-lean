import Kourovka2135.MatrixOperatorSpanCertificate
import Mathlib.Data.ZMod.Basic

/-! Exact finite data for the binary six-dimensional PSL2(7) heart.
These identities do not by themselves identify the actual projective action.
The untrusted producer supplies matrices; ordinary Lean kernel reduction
checks the splitting, generator actions and full operator spans. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace Kourovka2135.PSL27BinaryHeartData
open scoped Matrix
abbrev k := ZMod 2

def heartU : Matrix (Fin 6) (Fin 6) k :=
  !![0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 1;
    0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 1]

def heartW : Matrix (Fin 6) (Fin 6) k :=
  !![1, 0, 1, 1, 1, 1;
    0, 1, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1;
    0, 1, 0, 0, 1, 0]

def splitting : Matrix (Fin 6) (Fin 6) k :=
  !![1, 1, 1, 1, 0, 1;
    0, 1, 1, 1, 1, 1;
    1, 1, 0, 0, 1, 1;
    1, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1]

def splittingInverse : Matrix (Fin 6) (Fin 6) k :=
  !![0, 1, 0, 1, 1, 1;
    1, 0, 0, 1, 0, 1;
    0, 1, 1, 1, 0, 0;
    0, 1, 0, 0, 1, 1;
    1, 0, 0, 1, 1, 1;
    0, 1, 1, 1, 0, 1]

theorem splitting_inverse : splitting * splittingInverse = 1 := by decide +kernel
theorem inverse_splitting : splittingInverse * splitting = 1 := by decide +kernel

def blockU : Matrix (Fin 6) (Fin 6) k :=
  !![1, 1, 1, 0, 0, 0;
    1, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 1]

theorem split_U : heartU * splitting = splitting * blockU :=
  by decide +kernel

def blockW : Matrix (Fin 6) (Fin 6) k :=
  !![1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 1, 0;
    0, 0, 0, 1, 0, 1]

theorem split_W : heartW * splitting = splitting * blockW :=
  by decide +kernel

def U1 : Matrix (Fin 3) (Fin 3) k :=
  !![1, 1, 1;
    1, 0, 1;
    0, 1, 1]

def W1 : Matrix (Fin 3) (Fin 3) k :=
  !![1, 0, 1;
    0, 1, 0;
    0, 0, 1]

theorem polynomial1 : U1 ^ 3 + U1 + 1 = 0 := by decide +kernel
def words1 : Fin 9 → List Bool :=
  ![[], [false], [true], [false, false], [false, true], [true, false], [false, false, true], [false, true, false], [false, false, true, false]]

def operators1 : Fin 9 → Matrix (Fin 3) (Fin 3) k :=
  ![!![1, 0, 0;
    0, 1, 0;
    0, 0, 1],
  !![1, 1, 1;
    1, 0, 1;
    0, 1, 1],
  !![1, 0, 1;
    0, 1, 0;
    0, 0, 1],
  !![0, 0, 1;
    1, 0, 0;
    1, 1, 0],
  !![1, 1, 0;
    1, 0, 0;
    0, 1, 1],
  !![1, 0, 0;
    1, 0, 1;
    0, 1, 1],
  !![0, 0, 1;
    1, 0, 1;
    1, 1, 1],
  !![0, 1, 0;
    1, 1, 1;
    1, 1, 0],
  !![0, 1, 1;
    1, 0, 0;
    0, 0, 1]]

def wordMatrix1 : List Bool → Matrix (Fin 3) (Fin 3) k
  | [] => 1
  | false :: xs => U1 * wordMatrix1 xs
  | true :: xs => W1 * wordMatrix1 xs

theorem operators1_checked : ∀ i : Fin 9,
    wordMatrix1 (words1 i) = operators1 i := by decide +kernel

def coordinateMatrix1 : Matrix (Fin 3 × Fin 3) (Fin 9) k :=
  fun p i => operators1 i p.1 p.2

def inverseMatrix1 : Matrix (Fin 9) (Fin 9) k :=
  !![1, 1, 0, 1, 1, 0, 1, 1, 1;
    1, 0, 1, 1, 0, 1, 0, 1, 1;
    0, 1, 1, 1, 1, 1, 1, 1, 1;
    0, 1, 0, 0, 1, 0, 0, 0, 1;
    0, 1, 0, 0, 1, 1, 0, 1, 1;
    1, 1, 0, 1, 1, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 1, 0, 0, 1;
    1, 0, 1, 0, 1, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0]

def coordinateInverse1 : Matrix (Fin 9) (Fin 3 × Fin 3) k :=
  fun i p => inverseMatrix1 i ⟨p.1.val + 3 * p.2.val, by omega⟩

theorem coordinate_inverse1 : coordinateMatrix1 * coordinateInverse1 = 1 :=
  by decide +kernel

def U2 : Matrix (Fin 3) (Fin 3) k :=
  !![0, 1, 0;
    1, 0, 1;
    0, 1, 1]

def W2 : Matrix (Fin 3) (Fin 3) k :=
  !![1, 0, 0;
    1, 1, 0;
    1, 0, 1]

theorem polynomial2 : U2 ^ 3 + U2 ^ 2 + 1 = 0 := by decide +kernel
def words2 : Fin 9 → List Bool :=
  ![[], [false], [true], [false, false], [false, true], [true, false], [false, false, true], [false, true, false], [false, false, true, false]]

def operators2 : Fin 9 → Matrix (Fin 3) (Fin 3) k :=
  ![!![1, 0, 0;
    0, 1, 0;
    0, 0, 1],
  !![0, 1, 0;
    1, 0, 1;
    0, 1, 1],
  !![1, 0, 0;
    1, 1, 0;
    1, 0, 1],
  !![1, 0, 1;
    0, 0, 1;
    1, 1, 0],
  !![1, 1, 0;
    0, 0, 1;
    0, 1, 1],
  !![0, 1, 0;
    1, 1, 1;
    0, 0, 1],
  !![0, 0, 1;
    1, 0, 1;
    0, 1, 0],
  !![1, 1, 1;
    0, 1, 1;
    1, 1, 0],
  !![0, 1, 1;
    0, 0, 1;
    1, 0, 1]]

def wordMatrix2 : List Bool → Matrix (Fin 3) (Fin 3) k
  | [] => 1
  | false :: xs => U2 * wordMatrix2 xs
  | true :: xs => W2 * wordMatrix2 xs

theorem operators2_checked : ∀ i : Fin 9,
    wordMatrix2 (words2 i) = operators2 i := by decide +kernel

def coordinateMatrix2 : Matrix (Fin 3 × Fin 3) (Fin 9) k :=
  fun p i => operators2 i p.1 p.2

def inverseMatrix2 : Matrix (Fin 9) (Fin 9) k :=
  !![1, 1, 0, 1, 1, 1, 0, 0, 1;
    0, 1, 1, 1, 1, 0, 1, 0, 1;
    1, 1, 0, 0, 0, 0, 1, 0, 1;
    1, 1, 1, 1, 0, 0, 0, 1, 1;
    0, 1, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 0, 0, 1;
    1, 1, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 1, 1, 0, 1;
    0, 0, 0, 1, 1, 1, 0, 1, 1]

def coordinateInverse2 : Matrix (Fin 9) (Fin 3 × Fin 3) k :=
  fun i p => inverseMatrix2 i ⟨p.1.val + 3 * p.2.val, by omega⟩

theorem coordinate_inverse2 : coordinateMatrix2 * coordinateInverse2 = 1 :=
  by decide +kernel

end Kourovka2135.PSL27BinaryHeartData
