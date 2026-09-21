import Kourovka2135.PSL33SingerCosetData
import Kourovka2135.BinaryFieldSixteen
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite generator and surjectivity certificates for an actual quotient of
the Singer-coset permutation module. Entries are polynomial-basis F16 bits,
not natural-number casts. The producer supplies data only. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace Kourovka2135.PSL33SingerSixteenData
abbrev k := BinaryFieldSixteen.K
open scoped Matrix

def leftA : Matrix (Fin 16) (Fin 16) k :=
  (!![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 9, 0, 2, 13; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 15, 0, 0, 8; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 10, 0, 11, 14; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 12, 0, 13, 10; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 6, 0, 6, 5; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 3, 9; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 10, 0, 12, 14; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 8, 0, 1, 4; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 12, 0, 8, 3; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 8, 0, 5, 5; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0, 12; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 1, 11, 2; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 10, 11; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 11, 0, 14, 14; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 3; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 13] : Matrix (Fin 16) (Fin 16) ℕ).map BinaryFieldSixteen.ofBits

def leftB : Matrix (Fin 16) (Fin 16) k :=
  (!![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 11, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 15, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 11, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 10, 0, 0] : Matrix (Fin 16) (Fin 16) ℕ).map BinaryFieldSixteen.ofBits

def leftBInv : Matrix (Fin 16) (Fin 16) k :=
  (!![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 15, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 1; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 15, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 10, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 15, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : Matrix (Fin 16) (Fin 16) ℕ).map BinaryFieldSixteen.ofBits

def quotient : Matrix (Fin 16) (Fin 144) k :=
  (!![8, 13, 12, 6, 0, 4, 3, 6, 7, 9, 11, 9, 2, 15, 11, 3, 7, 13, 1, 7, 0, 6, 5, 6, 4, 11, 0, 1, 11, 3, 8, 13, 13, 11, 5, 4, 12, 12, 6, 13, 15, 11, 6, 5, 7, 14, 2, 14, 10, 9, 4, 12, 14, 9, 8, 6, 4, 1, 8, 9, 8, 9, 14, 10, 3, 6, 8, 13, 10, 15, 6, 13, 0, 10, 14, 8, 10, 15, 7, 7, 12, 9, 14, 0, 6, 0, 9, 0, 14, 6, 10, 12, 15, 11, 13, 3, 5, 6, 13, 9, 12, 13, 6, 14, 0, 1, 14, 4, 13, 10, 1, 5, 5, 9, 10, 11, 6, 14, 8, 8, 8, 10, 15, 0, 13, 6, 4, 8, 4, 6, 12, 9, 5, 5, 14, 11, 4, 13, 15, 1, 13, 4, 6, 4; 5, 5, 5, 3, 3, 8, 3, 8, 6, 14, 8, 6, 14, 11, 11, 6, 7, 14, 11, 9, 7, 0, 5, 9, 1, 7, 0, 5, 0, 9, 1, 9, 10, 0, 5, 0, 9, 1, 10, 4, 6, 7, 0, 9, 14, 5, 10, 4, 6, 7, 7, 9, 14, 5, 14, 4, 6, 10, 7, 12, 14, 10, 5, 14, 12, 6, 10, 4, 12, 10, 10, 15, 6, 14, 12, 6, 0, 10, 4, 3, 12, 10, 11, 10, 15, 6, 2, 12, 15, 6, 0, 10, 3, 4, 3, 15, 10, 11, 2, 10, 15, 0, 6, 15, 15, 15, 0, 10, 15, 15, 0, 0, 11, 2, 14, 0, 9, 15, 14, 15, 0, 15, 14, 15, 0, 11, 14, 0, 14, 0, 9, 15, 14, 0, 11, 0, 14, 14, 0, 14, 11, 0, 0, 14; 0, 4, 1, 5, 0, 10, 6, 5, 8, 5, 7, 12, 1, 15, 1, 2, 0, 10, 5, 8, 12, 6, 1, 12, 13, 11, 11, 1, 15, 13, 5, 9, 1, 13, 5, 2, 0, 9, 14, 7, 3, 5, 13, 0, 7, 2, 5, 12, 8, 6, 7, 9, 8, 2, 12, 15, 13, 3, 4, 15, 1, 5, 5, 14, 1, 8, 13, 14, 10, 12, 12, 4, 6, 12, 2, 8, 0, 4, 8, 9, 9, 6, 3, 3, 5, 0, 6, 15, 1, 6, 4, 2, 11, 2, 1, 6, 0, 8, 6, 15, 14, 6, 0, 15, 7, 0, 4, 7, 8, 5, 12, 4, 0, 2, 0, 3, 9, 0, 2, 9, 14, 12, 4, 12, 8, 3, 14, 5, 7, 3, 9, 11, 10, 13, 8, 15, 0, 11, 4, 0, 0, 11, 0, 14; 8, 2, 9, 2, 6, 13, 7, 10, 3, 11, 6, 10, 12, 3, 3, 0, 4, 0, 1, 4, 10, 8, 9, 7, 9, 14, 1, 0, 4, 15, 11, 8, 6, 4, 13, 4, 5, 7, 4, 14, 10, 11, 4, 11, 9, 15, 1, 7, 15, 12, 3, 8, 13, 6, 10, 10, 2, 8, 1, 0, 9, 1, 15, 8, 3, 9, 0, 12, 9, 12, 5, 5, 11, 13, 14, 15, 14, 8, 6, 3, 2, 5, 10, 9, 6, 8, 10, 8, 2, 3, 8, 12, 4, 6, 7, 5, 7, 13, 10, 1, 13, 12, 7, 2, 3, 5, 0, 13, 1, 6, 12, 1, 9, 4, 1, 11, 9, 3, 13, 2, 11, 12, 11, 9, 11, 6, 5, 5, 10, 11, 7, 8, 3, 14, 9, 2, 6, 10, 5, 10, 14, 7, 9, 9; 7, 12, 13, 13, 12, 14, 9, 2, 0, 10, 9, 10, 6, 14, 12, 9, 0, 13, 14, 13, 4, 0, 3, 5, 15, 14, 5, 14, 6, 14, 3, 11, 8, 9, 10, 6, 14, 13, 13, 3, 0, 13, 6, 13, 4, 3, 10, 14, 13, 0, 15, 0, 0, 10, 3, 10, 5, 5, 10, 5, 0, 2, 10, 6, 10, 2, 13, 1, 14, 7, 14, 0, 8, 1, 12, 14, 5, 13, 1, 12, 12, 5, 6, 6, 11, 7, 3, 7, 1, 4, 13, 7, 8, 11, 15, 13, 14, 2, 13, 6, 3, 6, 11, 14, 0, 15, 3, 11, 8, 2, 9, 14, 1, 3, 6, 8, 0, 8, 3, 0, 1, 12, 4, 14, 3, 4, 5, 1, 3, 4, 0, 5, 13, 1, 3, 7, 2, 4, 2, 12, 11, 5, 2, 7; 3, 5, 10, 13, 14, 8, 8, 11, 12, 9, 4, 11, 15, 2, 0, 11, 0, 6, 13, 6, 4, 7, 14, 6, 15, 4, 5, 11, 0, 11, 13, 14, 9, 14, 0, 1, 1, 11, 14, 15, 0, 10, 12, 8, 7, 0, 7, 9, 9, 5, 10, 12, 8, 13, 8, 8, 12, 5, 3, 5, 9, 13, 10, 3, 9, 4, 10, 4, 13, 3, 2, 11, 11, 11, 15, 6, 15, 11, 11, 2, 2, 11, 12, 2, 14, 14, 6, 1, 4, 14, 13, 13, 6, 15, 6, 11, 0, 14, 14, 1, 14, 9, 0, 10, 0, 12, 13, 1, 12, 15, 1, 8, 3, 15, 2, 8, 1, 4, 8, 6, 13, 8, 3, 6, 4, 14, 11, 15, 0, 1, 0, 13, 2, 12, 2, 11, 12, 11, 2, 1, 6, 12, 13, 7; 0, 1, 11, 10, 15, 3, 11, 8, 1, 14, 15, 2, 5, 2, 0, 11, 15, 2, 0, 14, 5, 8, 10, 5, 2, 11, 4, 14, 15, 6, 12, 15, 14, 13, 7, 15, 1, 14, 9, 15, 10, 13, 15, 12, 15, 6, 11, 11, 2, 7, 12, 2, 15, 6, 0, 2, 7, 1, 0, 13, 11, 11, 15, 7, 13, 0, 1, 4, 15, 12, 3, 3, 7, 5, 6, 10, 3, 9, 14, 9, 6, 7, 4, 7, 11, 11, 2, 11, 9, 12, 13, 0, 10, 4, 14, 4, 14, 7, 12, 12, 8, 6, 8, 6, 9, 0, 11, 13, 13, 8, 10, 0, 0, 12, 1, 15, 15, 1, 12, 8, 15, 4, 8, 11, 7, 13, 6, 8, 11, 10, 5, 9, 9, 10, 5, 5, 2, 12, 7, 1, 10, 2, 4, 13; 5, 10, 3, 14, 8, 11, 13, 4, 11, 15, 8, 11, 6, 0, 13, 12, 4, 9, 2, 6, 4, 5, 11, 11, 13, 0, 14, 0, 1, 6, 11, 14, 14, 7, 14, 12, 8, 15, 7, 9, 9, 5, 0, 12, 8, 13, 9, 8, 12, 3, 10, 1, 9, 10, 3, 15, 0, 10, 10, 13, 7, 2, 0, 11, 15, 6, 11, 11, 2, 11, 2, 14, 14, 8, 1, 14, 13, 5, 15, 6, 5, 0, 14, 13, 14, 0, 14, 9, 0, 4, 13, 1, 2, 4, 6, 15, 3, 3, 15, 13, 11, 8, 11, 4, 6, 10, 15, 1, 8, 6, 4, 1, 12, 6, 11, 15, 1, 12, 0, 4, 1, 13, 2, 11, 8, 2, 12, 9, 11, 12, 0, 12, 1, 13, 6, 12, 2, 8, 11, 3, 14, 2, 13, 7; 9, 10, 7, 1, 9, 3, 5, 15, 9, 12, 7, 5, 12, 2, 15, 10, 4, 1, 13, 10, 14, 6, 8, 0, 11, 0, 10, 11, 8, 10, 7, 6, 8, 10, 15, 11, 14, 14, 4, 9, 7, 1, 4, 14, 13, 12, 5, 6, 4, 12, 1, 12, 1, 8, 9, 0, 3, 9, 12, 7, 5, 11, 7, 2, 13, 12, 11, 6, 6, 6, 14, 1, 4, 13, 8, 9, 6, 12, 14, 5, 3, 12, 4, 7, 15, 7, 1, 11, 2, 10, 5, 14, 12, 7, 4, 1, 9, 7, 2, 15, 10, 5, 7, 6, 9, 14, 5, 11, 3, 12, 7, 4, 0, 11, 10, 14, 3, 2, 6, 5, 10, 14, 4, 11, 0, 15, 3, 2, 2, 14, 6, 10, 7, 9, 15, 12, 12, 2, 7, 9, 13, 6, 14, 9; 9, 13, 4, 10, 9, 4, 4, 3, 9, 0, 1, 2, 4, 3, 15, 5, 3, 12, 11, 10, 1, 1, 4, 8, 8, 5, 12, 2, 6, 11, 11, 7, 6, 15, 15, 9, 13, 13, 0, 3, 0, 0, 7, 2, 14, 10, 13, 1, 15, 4, 4, 13, 15, 4, 11, 2, 4, 9, 5, 4, 3, 3, 15, 6, 8, 14, 11, 5, 5, 4, 14, 3, 10, 0, 1, 15, 6, 1, 13, 10, 3, 12, 11, 0, 12, 7, 7, 0, 10, 2, 0, 4, 14, 14, 13, 12, 9, 0, 1, 8, 12, 6, 6, 10, 4, 10, 12, 13, 2, 3, 7, 10, 9, 3, 9, 7, 4, 5, 0, 12, 5, 6, 15, 5, 8, 8, 7, 1, 2, 5, 5, 14, 14, 5, 14, 0, 0, 10, 8, 10, 14, 7, 10, 7; 4, 13, 11, 15, 10, 2, 9, 14, 4, 3, 13, 3, 12, 15, 0, 4, 11, 10, 2, 4, 15, 6, 11, 9, 13, 11, 15, 5, 15, 9, 9, 5, 13, 13, 0, 3, 2, 11, 3, 14, 13, 11, 2, 15, 13, 4, 4, 9, 1, 2, 0, 6, 3, 14, 12, 15, 8, 5, 13, 8, 12, 15, 3, 15, 7, 12, 11, 2, 15, 3, 0, 11, 0, 4, 15, 6, 15, 4, 9, 1, 7, 0, 4, 15, 14, 11, 11, 9, 5, 4, 13, 14, 1, 6, 5, 1, 8, 11, 2, 14, 11, 13, 14, 14, 7, 6, 15, 2, 11, 12, 11, 7, 9, 10, 7, 11, 5, 8, 15, 3, 3, 10, 12, 8, 2, 4, 9, 10, 12, 2, 13, 14, 14, 14, 12, 2, 0, 4, 12, 15, 0, 11, 10, 14; 8, 5, 11, 8, 4, 8, 0, 0, 1, 1, 4, 14, 12, 3, 1, 13, 10, 1, 14, 4, 4, 15, 4, 14, 0, 0, 15, 0, 1, 14, 9, 9, 13, 3, 7, 14, 12, 12, 12, 1, 2, 9, 2, 14, 10, 10, 1, 7, 5, 9, 8, 12, 14, 5, 3, 14, 1, 9, 4, 15, 6, 6, 14, 12, 15, 5, 14, 6, 10, 6, 15, 2, 7, 8, 12, 6, 9, 11, 15, 5, 14, 3, 6, 3, 7, 7, 9, 10, 3, 0, 9, 15, 4, 14, 13, 13, 12, 1, 0, 10, 12, 2, 4, 14, 15, 10, 10, 11, 9, 10, 10, 13, 5, 10, 12, 14, 8, 2, 9, 8, 10, 13, 15, 0, 14, 3, 3, 9, 9, 13, 14, 4, 1, 14, 1, 6, 5, 13, 12, 12, 3, 7, 15, 10; 8, 1, 12, 2, 15, 7, 1, 5, 8, 2, 0, 15, 10, 2, 6, 3, 11, 6, 14, 2, 15, 13, 1, 1, 15, 9, 14, 12, 11, 0, 9, 4, 12, 0, 7, 5, 7, 12, 1, 5, 0, 5, 4, 8, 6, 1, 10, 6, 11, 4, 8, 8, 10, 10, 13, 7, 15, 14, 1, 9, 7, 9, 15, 11, 5, 2, 4, 10, 15, 14, 7, 10, 7, 0, 4, 15, 13, 12, 9, 6, 8, 11, 11, 4, 10, 6, 8, 12, 6, 3, 1, 7, 1, 2, 5, 8, 6, 2, 10, 14, 5, 10, 10, 8, 14, 7, 11, 2, 2, 14, 10, 5, 0, 14, 4, 12, 13, 7, 11, 8, 15, 10, 9, 7, 8, 3, 3, 11, 3, 15, 2, 6, 13, 15, 3, 7, 10, 9, 0, 8, 5, 8, 1, 9; 9, 9, 9, 13, 13, 5, 13, 5, 1, 14, 5, 1, 14, 3, 3, 1, 1, 14, 3, 1, 1, 12, 7, 1, 5, 1, 12, 7, 11, 1, 5, 7, 15, 12, 7, 11, 9, 5, 15, 5, 8, 12, 11, 9, 6, 9, 15, 5, 8, 12, 15, 9, 6, 9, 13, 5, 8, 9, 12, 15, 6, 2, 9, 13, 5, 3, 9, 2, 15, 11, 2, 14, 0, 13, 5, 3, 3, 9, 2, 13, 15, 11, 13, 2, 14, 0, 6, 5, 11, 3, 3, 1, 13, 2, 13, 13, 11, 13, 6, 1, 14, 3, 0, 3, 11, 3, 3, 1, 5, 13, 11, 11, 13, 6, 7, 3, 6, 3, 6, 11, 1, 5, 2, 13, 11, 3, 7, 3, 6, 1, 2, 5, 2, 1, 3, 0, 7, 6, 0, 2, 3, 0, 13, 4; 11, 5, 6, 3, 7, 6, 15, 2, 1, 9, 14, 2, 4, 3, 12, 14, 11, 4, 1, 1, 15, 7, 11, 1, 15, 5, 11, 12, 13, 11, 10, 2, 6, 7, 15, 1, 0, 6, 11, 1, 4, 1, 2, 2, 10, 11, 7, 8, 0, 12, 2, 2, 2, 0, 11, 7, 3, 0, 1, 0, 14, 2, 4, 15, 10, 4, 5, 2, 4, 0, 14, 2, 7, 4, 12, 2, 11, 7, 3, 10, 5, 15, 6, 11, 9, 4, 4, 9, 12, 7, 8, 4, 2, 11, 3, 13, 5, 2, 14, 0, 7, 12, 7, 0, 11, 12, 11, 5, 11, 7, 13, 9, 1, 13, 8, 11, 12, 8, 13, 0, 2, 2, 12, 10, 14, 3, 14, 0, 9, 1, 3, 15, 1, 5, 1, 7, 7, 13, 6, 2, 1, 12, 8, 3; 1, 12, 8, 15, 1, 5, 2, 0, 15, 10, 7, 3, 6, 6, 14, 8, 15, 2, 2, 1, 9, 14, 12, 0, 9, 11, 0, 7, 5, 2, 12, 4, 1, 13, 1, 4, 8, 15, 10, 6, 11, 4, 11, 8, 10, 10, 12, 7, 15, 1, 8, 7, 7, 15, 11, 5, 0, 4, 5, 15, 6, 7, 1, 0, 4, 15, 12, 9, 8, 11, 4, 10, 6, 13, 12, 3, 1, 14, 2, 5, 9, 6, 2, 9, 5, 10, 10, 5, 14, 2, 11, 2, 6, 10, 1, 14, 14, 0, 14, 7, 10, 12, 7, 7, 8, 8, 13, 14, 10, 7, 8, 10, 11, 8, 3, 11, 13, 7, 3, 6, 15, 6, 13, 8, 5, 3, 10, 10, 9, 15, 2, 2, 8, 15, 5, 8, 4, 11, 7, 9, 3, 0, 1, 9] : Matrix (Fin 16) (Fin 144) ℕ).map BinaryFieldSixteen.ofBits

def minorInverse : Matrix (Fin 16) (Fin 16) k :=
  (!![6, 7, 11, 8, 15, 6, 9, 8, 12, 9, 4, 15, 11, 13, 2, 11; 7, 6, 8, 11, 6, 15, 12, 9, 9, 8, 3, 13, 4, 15, 5, 1; 3, 3, 8, 4, 4, 6, 14, 4, 5, 10, 7, 9, 13, 8, 13, 5; 3, 3, 4, 8, 6, 4, 5, 10, 14, 4, 0, 8, 13, 9, 9, 11; 14, 3, 0, 7, 11, 15, 6, 3, 11, 5, 15, 3, 13, 14, 8, 5; 3, 14, 7, 0, 15, 11, 11, 5, 6, 3, 8, 14, 2, 3, 1, 11; 15, 6, 15, 13, 5, 4, 13, 12, 1, 13, 15, 4, 5, 2, 15, 6; 14, 11, 4, 6, 3, 13, 15, 15, 14, 10, 11, 0, 15, 2, 7, 10; 6, 15, 13, 15, 4, 5, 1, 13, 13, 12, 8, 2, 2, 4, 1, 8; 11, 14, 6, 4, 13, 3, 14, 10, 15, 15, 13, 2, 5, 0, 11, 3; 4, 7, 5, 9, 8, 12, 8, 11, 11, 8, 14, 11, 3, 2, 14, 1; 3, 5, 4, 2, 11, 7, 1, 13, 6, 1, 9, 0, 3, 0, 8, 15; 11, 0, 6, 0, 9, 6, 10, 15, 6, 9, 8, 11, 3, 10, 2, 5; 7, 4, 9, 5, 12, 8, 11, 8, 8, 11, 2, 2, 4, 11, 8, 13; 5, 3, 2, 4, 7, 11, 6, 1, 1, 13, 14, 0, 11, 0, 11, 15; 0, 11, 0, 6, 6, 9, 6, 9, 10, 15, 9, 10, 15, 11, 10, 15] : Matrix (Fin 16) (Fin 16) ℕ).map BinaryFieldSixteen.ofBits

def minorColumns : Fin 16 → Fin 144 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16]

def minor : Matrix (Fin 16) (Fin 16) k := fun i j => quotient i (minorColumns j)

theorem leftA_inverse : leftA * leftA = 1 := by decide +kernel
theorem leftB_inverse : leftB * leftBInv = 1 ∧ leftBInv * leftB = 1 := by decide +kernel
theorem minor_inverse : minor * minorInverse = 1 := by decide +kernel

private theorem column_a_0 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 0) =
    (leftA *ᵥ (fun h => quotient h 0)) i := by decide +kernel
private theorem column_a_1 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 1) =
    (leftA *ᵥ (fun h => quotient h 1)) i := by decide +kernel
private theorem column_a_2 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 2) =
    (leftA *ᵥ (fun h => quotient h 2)) i := by decide +kernel
private theorem column_a_3 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 3) =
    (leftA *ᵥ (fun h => quotient h 3)) i := by decide +kernel
private theorem column_a_4 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 4) =
    (leftA *ᵥ (fun h => quotient h 4)) i := by decide +kernel
private theorem column_a_5 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 5) =
    (leftA *ᵥ (fun h => quotient h 5)) i := by decide +kernel
private theorem column_a_6 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 6) =
    (leftA *ᵥ (fun h => quotient h 6)) i := by decide +kernel
private theorem column_a_7 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 7) =
    (leftA *ᵥ (fun h => quotient h 7)) i := by decide +kernel
private theorem column_a_8 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 8) =
    (leftA *ᵥ (fun h => quotient h 8)) i := by decide +kernel
private theorem column_a_9 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 9) =
    (leftA *ᵥ (fun h => quotient h 9)) i := by decide +kernel
private theorem column_a_10 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 10) =
    (leftA *ᵥ (fun h => quotient h 10)) i := by decide +kernel
private theorem column_a_11 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 11) =
    (leftA *ᵥ (fun h => quotient h 11)) i := by decide +kernel
private theorem column_a_12 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 12) =
    (leftA *ᵥ (fun h => quotient h 12)) i := by decide +kernel
private theorem column_a_13 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 13) =
    (leftA *ᵥ (fun h => quotient h 13)) i := by decide +kernel
private theorem column_a_14 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 14) =
    (leftA *ᵥ (fun h => quotient h 14)) i := by decide +kernel
private theorem column_a_15 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 15) =
    (leftA *ᵥ (fun h => quotient h 15)) i := by decide +kernel
private theorem column_a_16 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 16) =
    (leftA *ᵥ (fun h => quotient h 16)) i := by decide +kernel
private theorem column_a_17 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 17) =
    (leftA *ᵥ (fun h => quotient h 17)) i := by decide +kernel
private theorem column_a_18 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 18) =
    (leftA *ᵥ (fun h => quotient h 18)) i := by decide +kernel
private theorem column_a_19 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 19) =
    (leftA *ᵥ (fun h => quotient h 19)) i := by decide +kernel
private theorem column_a_20 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 20) =
    (leftA *ᵥ (fun h => quotient h 20)) i := by decide +kernel
private theorem column_a_21 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 21) =
    (leftA *ᵥ (fun h => quotient h 21)) i := by decide +kernel
private theorem column_a_22 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 22) =
    (leftA *ᵥ (fun h => quotient h 22)) i := by decide +kernel
private theorem column_a_23 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 23) =
    (leftA *ᵥ (fun h => quotient h 23)) i := by decide +kernel
private theorem column_a_24 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 24) =
    (leftA *ᵥ (fun h => quotient h 24)) i := by decide +kernel
private theorem column_a_25 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 25) =
    (leftA *ᵥ (fun h => quotient h 25)) i := by decide +kernel
private theorem column_a_26 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 26) =
    (leftA *ᵥ (fun h => quotient h 26)) i := by decide +kernel
private theorem column_a_27 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 27) =
    (leftA *ᵥ (fun h => quotient h 27)) i := by decide +kernel
private theorem column_a_28 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 28) =
    (leftA *ᵥ (fun h => quotient h 28)) i := by decide +kernel
private theorem column_a_29 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 29) =
    (leftA *ᵥ (fun h => quotient h 29)) i := by decide +kernel
private theorem column_a_30 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 30) =
    (leftA *ᵥ (fun h => quotient h 30)) i := by decide +kernel
private theorem column_a_31 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 31) =
    (leftA *ᵥ (fun h => quotient h 31)) i := by decide +kernel
private theorem column_a_32 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 32) =
    (leftA *ᵥ (fun h => quotient h 32)) i := by decide +kernel
private theorem column_a_33 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 33) =
    (leftA *ᵥ (fun h => quotient h 33)) i := by decide +kernel
private theorem column_a_34 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 34) =
    (leftA *ᵥ (fun h => quotient h 34)) i := by decide +kernel
private theorem column_a_35 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 35) =
    (leftA *ᵥ (fun h => quotient h 35)) i := by decide +kernel
private theorem column_a_36 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 36) =
    (leftA *ᵥ (fun h => quotient h 36)) i := by decide +kernel
private theorem column_a_37 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 37) =
    (leftA *ᵥ (fun h => quotient h 37)) i := by decide +kernel
private theorem column_a_38 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 38) =
    (leftA *ᵥ (fun h => quotient h 38)) i := by decide +kernel
private theorem column_a_39 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 39) =
    (leftA *ᵥ (fun h => quotient h 39)) i := by decide +kernel
private theorem column_a_40 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 40) =
    (leftA *ᵥ (fun h => quotient h 40)) i := by decide +kernel
private theorem column_a_41 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 41) =
    (leftA *ᵥ (fun h => quotient h 41)) i := by decide +kernel
private theorem column_a_42 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 42) =
    (leftA *ᵥ (fun h => quotient h 42)) i := by decide +kernel
private theorem column_a_43 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 43) =
    (leftA *ᵥ (fun h => quotient h 43)) i := by decide +kernel
private theorem column_a_44 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 44) =
    (leftA *ᵥ (fun h => quotient h 44)) i := by decide +kernel
private theorem column_a_45 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 45) =
    (leftA *ᵥ (fun h => quotient h 45)) i := by decide +kernel
private theorem column_a_46 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 46) =
    (leftA *ᵥ (fun h => quotient h 46)) i := by decide +kernel
private theorem column_a_47 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 47) =
    (leftA *ᵥ (fun h => quotient h 47)) i := by decide +kernel
private theorem column_a_48 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 48) =
    (leftA *ᵥ (fun h => quotient h 48)) i := by decide +kernel
private theorem column_a_49 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 49) =
    (leftA *ᵥ (fun h => quotient h 49)) i := by decide +kernel
private theorem column_a_50 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 50) =
    (leftA *ᵥ (fun h => quotient h 50)) i := by decide +kernel
private theorem column_a_51 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 51) =
    (leftA *ᵥ (fun h => quotient h 51)) i := by decide +kernel
private theorem column_a_52 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 52) =
    (leftA *ᵥ (fun h => quotient h 52)) i := by decide +kernel
private theorem column_a_53 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 53) =
    (leftA *ᵥ (fun h => quotient h 53)) i := by decide +kernel
private theorem column_a_54 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 54) =
    (leftA *ᵥ (fun h => quotient h 54)) i := by decide +kernel
private theorem column_a_55 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 55) =
    (leftA *ᵥ (fun h => quotient h 55)) i := by decide +kernel
private theorem column_a_56 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 56) =
    (leftA *ᵥ (fun h => quotient h 56)) i := by decide +kernel
private theorem column_a_57 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 57) =
    (leftA *ᵥ (fun h => quotient h 57)) i := by decide +kernel
private theorem column_a_58 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 58) =
    (leftA *ᵥ (fun h => quotient h 58)) i := by decide +kernel
private theorem column_a_59 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 59) =
    (leftA *ᵥ (fun h => quotient h 59)) i := by decide +kernel
private theorem column_a_60 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 60) =
    (leftA *ᵥ (fun h => quotient h 60)) i := by decide +kernel
private theorem column_a_61 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 61) =
    (leftA *ᵥ (fun h => quotient h 61)) i := by decide +kernel
private theorem column_a_62 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 62) =
    (leftA *ᵥ (fun h => quotient h 62)) i := by decide +kernel
private theorem column_a_63 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 63) =
    (leftA *ᵥ (fun h => quotient h 63)) i := by decide +kernel
private theorem column_a_64 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 64) =
    (leftA *ᵥ (fun h => quotient h 64)) i := by decide +kernel
private theorem column_a_65 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 65) =
    (leftA *ᵥ (fun h => quotient h 65)) i := by decide +kernel
private theorem column_a_66 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 66) =
    (leftA *ᵥ (fun h => quotient h 66)) i := by decide +kernel
private theorem column_a_67 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 67) =
    (leftA *ᵥ (fun h => quotient h 67)) i := by decide +kernel
private theorem column_a_68 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 68) =
    (leftA *ᵥ (fun h => quotient h 68)) i := by decide +kernel
private theorem column_a_69 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 69) =
    (leftA *ᵥ (fun h => quotient h 69)) i := by decide +kernel
private theorem column_a_70 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 70) =
    (leftA *ᵥ (fun h => quotient h 70)) i := by decide +kernel
private theorem column_a_71 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 71) =
    (leftA *ᵥ (fun h => quotient h 71)) i := by decide +kernel
private theorem column_a_72 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 72) =
    (leftA *ᵥ (fun h => quotient h 72)) i := by decide +kernel
private theorem column_a_73 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 73) =
    (leftA *ᵥ (fun h => quotient h 73)) i := by decide +kernel
private theorem column_a_74 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 74) =
    (leftA *ᵥ (fun h => quotient h 74)) i := by decide +kernel
private theorem column_a_75 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 75) =
    (leftA *ᵥ (fun h => quotient h 75)) i := by decide +kernel
private theorem column_a_76 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 76) =
    (leftA *ᵥ (fun h => quotient h 76)) i := by decide +kernel
private theorem column_a_77 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 77) =
    (leftA *ᵥ (fun h => quotient h 77)) i := by decide +kernel
private theorem column_a_78 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 78) =
    (leftA *ᵥ (fun h => quotient h 78)) i := by decide +kernel
private theorem column_a_79 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 79) =
    (leftA *ᵥ (fun h => quotient h 79)) i := by decide +kernel
private theorem column_a_80 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 80) =
    (leftA *ᵥ (fun h => quotient h 80)) i := by decide +kernel
private theorem column_a_81 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 81) =
    (leftA *ᵥ (fun h => quotient h 81)) i := by decide +kernel
private theorem column_a_82 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 82) =
    (leftA *ᵥ (fun h => quotient h 82)) i := by decide +kernel
private theorem column_a_83 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 83) =
    (leftA *ᵥ (fun h => quotient h 83)) i := by decide +kernel
private theorem column_a_84 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 84) =
    (leftA *ᵥ (fun h => quotient h 84)) i := by decide +kernel
private theorem column_a_85 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 85) =
    (leftA *ᵥ (fun h => quotient h 85)) i := by decide +kernel
private theorem column_a_86 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 86) =
    (leftA *ᵥ (fun h => quotient h 86)) i := by decide +kernel
private theorem column_a_87 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 87) =
    (leftA *ᵥ (fun h => quotient h 87)) i := by decide +kernel
private theorem column_a_88 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 88) =
    (leftA *ᵥ (fun h => quotient h 88)) i := by decide +kernel
private theorem column_a_89 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 89) =
    (leftA *ᵥ (fun h => quotient h 89)) i := by decide +kernel
private theorem column_a_90 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 90) =
    (leftA *ᵥ (fun h => quotient h 90)) i := by decide +kernel
private theorem column_a_91 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 91) =
    (leftA *ᵥ (fun h => quotient h 91)) i := by decide +kernel
private theorem column_a_92 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 92) =
    (leftA *ᵥ (fun h => quotient h 92)) i := by decide +kernel
private theorem column_a_93 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 93) =
    (leftA *ᵥ (fun h => quotient h 93)) i := by decide +kernel
private theorem column_a_94 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 94) =
    (leftA *ᵥ (fun h => quotient h 94)) i := by decide +kernel
private theorem column_a_95 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 95) =
    (leftA *ᵥ (fun h => quotient h 95)) i := by decide +kernel
private theorem column_a_96 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 96) =
    (leftA *ᵥ (fun h => quotient h 96)) i := by decide +kernel
private theorem column_a_97 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 97) =
    (leftA *ᵥ (fun h => quotient h 97)) i := by decide +kernel
private theorem column_a_98 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 98) =
    (leftA *ᵥ (fun h => quotient h 98)) i := by decide +kernel
private theorem column_a_99 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 99) =
    (leftA *ᵥ (fun h => quotient h 99)) i := by decide +kernel
private theorem column_a_100 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 100) =
    (leftA *ᵥ (fun h => quotient h 100)) i := by decide +kernel
private theorem column_a_101 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 101) =
    (leftA *ᵥ (fun h => quotient h 101)) i := by decide +kernel
private theorem column_a_102 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 102) =
    (leftA *ᵥ (fun h => quotient h 102)) i := by decide +kernel
private theorem column_a_103 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 103) =
    (leftA *ᵥ (fun h => quotient h 103)) i := by decide +kernel
private theorem column_a_104 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 104) =
    (leftA *ᵥ (fun h => quotient h 104)) i := by decide +kernel
private theorem column_a_105 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 105) =
    (leftA *ᵥ (fun h => quotient h 105)) i := by decide +kernel
private theorem column_a_106 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 106) =
    (leftA *ᵥ (fun h => quotient h 106)) i := by decide +kernel
private theorem column_a_107 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 107) =
    (leftA *ᵥ (fun h => quotient h 107)) i := by decide +kernel
private theorem column_a_108 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 108) =
    (leftA *ᵥ (fun h => quotient h 108)) i := by decide +kernel
private theorem column_a_109 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 109) =
    (leftA *ᵥ (fun h => quotient h 109)) i := by decide +kernel
private theorem column_a_110 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 110) =
    (leftA *ᵥ (fun h => quotient h 110)) i := by decide +kernel
private theorem column_a_111 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 111) =
    (leftA *ᵥ (fun h => quotient h 111)) i := by decide +kernel
private theorem column_a_112 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 112) =
    (leftA *ᵥ (fun h => quotient h 112)) i := by decide +kernel
private theorem column_a_113 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 113) =
    (leftA *ᵥ (fun h => quotient h 113)) i := by decide +kernel
private theorem column_a_114 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 114) =
    (leftA *ᵥ (fun h => quotient h 114)) i := by decide +kernel
private theorem column_a_115 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 115) =
    (leftA *ᵥ (fun h => quotient h 115)) i := by decide +kernel
private theorem column_a_116 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 116) =
    (leftA *ᵥ (fun h => quotient h 116)) i := by decide +kernel
private theorem column_a_117 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 117) =
    (leftA *ᵥ (fun h => quotient h 117)) i := by decide +kernel
private theorem column_a_118 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 118) =
    (leftA *ᵥ (fun h => quotient h 118)) i := by decide +kernel
private theorem column_a_119 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 119) =
    (leftA *ᵥ (fun h => quotient h 119)) i := by decide +kernel
private theorem column_a_120 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 120) =
    (leftA *ᵥ (fun h => quotient h 120)) i := by decide +kernel
private theorem column_a_121 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 121) =
    (leftA *ᵥ (fun h => quotient h 121)) i := by decide +kernel
private theorem column_a_122 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 122) =
    (leftA *ᵥ (fun h => quotient h 122)) i := by decide +kernel
private theorem column_a_123 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 123) =
    (leftA *ᵥ (fun h => quotient h 123)) i := by decide +kernel
private theorem column_a_124 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 124) =
    (leftA *ᵥ (fun h => quotient h 124)) i := by decide +kernel
private theorem column_a_125 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 125) =
    (leftA *ᵥ (fun h => quotient h 125)) i := by decide +kernel
private theorem column_a_126 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 126) =
    (leftA *ᵥ (fun h => quotient h 126)) i := by decide +kernel
private theorem column_a_127 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 127) =
    (leftA *ᵥ (fun h => quotient h 127)) i := by decide +kernel
private theorem column_a_128 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 128) =
    (leftA *ᵥ (fun h => quotient h 128)) i := by decide +kernel
private theorem column_a_129 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 129) =
    (leftA *ᵥ (fun h => quotient h 129)) i := by decide +kernel
private theorem column_a_130 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 130) =
    (leftA *ᵥ (fun h => quotient h 130)) i := by decide +kernel
private theorem column_a_131 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 131) =
    (leftA *ᵥ (fun h => quotient h 131)) i := by decide +kernel
private theorem column_a_132 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 132) =
    (leftA *ᵥ (fun h => quotient h 132)) i := by decide +kernel
private theorem column_a_133 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 133) =
    (leftA *ᵥ (fun h => quotient h 133)) i := by decide +kernel
private theorem column_a_134 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 134) =
    (leftA *ᵥ (fun h => quotient h 134)) i := by decide +kernel
private theorem column_a_135 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 135) =
    (leftA *ᵥ (fun h => quotient h 135)) i := by decide +kernel
private theorem column_a_136 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 136) =
    (leftA *ᵥ (fun h => quotient h 136)) i := by decide +kernel
private theorem column_a_137 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 137) =
    (leftA *ᵥ (fun h => quotient h 137)) i := by decide +kernel
private theorem column_a_138 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 138) =
    (leftA *ᵥ (fun h => quotient h 138)) i := by decide +kernel
private theorem column_a_139 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 139) =
    (leftA *ᵥ (fun h => quotient h 139)) i := by decide +kernel
private theorem column_a_140 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 140) =
    (leftA *ᵥ (fun h => quotient h 140)) i := by decide +kernel
private theorem column_a_141 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 141) =
    (leftA *ᵥ (fun h => quotient h 141)) i := by decide +kernel
private theorem column_a_142 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 142) =
    (leftA *ᵥ (fun h => quotient h 142)) i := by decide +kernel
private theorem column_a_143 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permA 143) =
    (leftA *ᵥ (fun h => quotient h 143)) i := by decide +kernel
theorem column_a (j : Fin 144) :
    (fun i => quotient i (PSL33SingerCosetData.permA j)) = leftA *ᵥ (fun i => quotient i j) := by
  funext i
  fin_cases j
  · exact column_a_0 i
  · exact column_a_1 i
  · exact column_a_2 i
  · exact column_a_3 i
  · exact column_a_4 i
  · exact column_a_5 i
  · exact column_a_6 i
  · exact column_a_7 i
  · exact column_a_8 i
  · exact column_a_9 i
  · exact column_a_10 i
  · exact column_a_11 i
  · exact column_a_12 i
  · exact column_a_13 i
  · exact column_a_14 i
  · exact column_a_15 i
  · exact column_a_16 i
  · exact column_a_17 i
  · exact column_a_18 i
  · exact column_a_19 i
  · exact column_a_20 i
  · exact column_a_21 i
  · exact column_a_22 i
  · exact column_a_23 i
  · exact column_a_24 i
  · exact column_a_25 i
  · exact column_a_26 i
  · exact column_a_27 i
  · exact column_a_28 i
  · exact column_a_29 i
  · exact column_a_30 i
  · exact column_a_31 i
  · exact column_a_32 i
  · exact column_a_33 i
  · exact column_a_34 i
  · exact column_a_35 i
  · exact column_a_36 i
  · exact column_a_37 i
  · exact column_a_38 i
  · exact column_a_39 i
  · exact column_a_40 i
  · exact column_a_41 i
  · exact column_a_42 i
  · exact column_a_43 i
  · exact column_a_44 i
  · exact column_a_45 i
  · exact column_a_46 i
  · exact column_a_47 i
  · exact column_a_48 i
  · exact column_a_49 i
  · exact column_a_50 i
  · exact column_a_51 i
  · exact column_a_52 i
  · exact column_a_53 i
  · exact column_a_54 i
  · exact column_a_55 i
  · exact column_a_56 i
  · exact column_a_57 i
  · exact column_a_58 i
  · exact column_a_59 i
  · exact column_a_60 i
  · exact column_a_61 i
  · exact column_a_62 i
  · exact column_a_63 i
  · exact column_a_64 i
  · exact column_a_65 i
  · exact column_a_66 i
  · exact column_a_67 i
  · exact column_a_68 i
  · exact column_a_69 i
  · exact column_a_70 i
  · exact column_a_71 i
  · exact column_a_72 i
  · exact column_a_73 i
  · exact column_a_74 i
  · exact column_a_75 i
  · exact column_a_76 i
  · exact column_a_77 i
  · exact column_a_78 i
  · exact column_a_79 i
  · exact column_a_80 i
  · exact column_a_81 i
  · exact column_a_82 i
  · exact column_a_83 i
  · exact column_a_84 i
  · exact column_a_85 i
  · exact column_a_86 i
  · exact column_a_87 i
  · exact column_a_88 i
  · exact column_a_89 i
  · exact column_a_90 i
  · exact column_a_91 i
  · exact column_a_92 i
  · exact column_a_93 i
  · exact column_a_94 i
  · exact column_a_95 i
  · exact column_a_96 i
  · exact column_a_97 i
  · exact column_a_98 i
  · exact column_a_99 i
  · exact column_a_100 i
  · exact column_a_101 i
  · exact column_a_102 i
  · exact column_a_103 i
  · exact column_a_104 i
  · exact column_a_105 i
  · exact column_a_106 i
  · exact column_a_107 i
  · exact column_a_108 i
  · exact column_a_109 i
  · exact column_a_110 i
  · exact column_a_111 i
  · exact column_a_112 i
  · exact column_a_113 i
  · exact column_a_114 i
  · exact column_a_115 i
  · exact column_a_116 i
  · exact column_a_117 i
  · exact column_a_118 i
  · exact column_a_119 i
  · exact column_a_120 i
  · exact column_a_121 i
  · exact column_a_122 i
  · exact column_a_123 i
  · exact column_a_124 i
  · exact column_a_125 i
  · exact column_a_126 i
  · exact column_a_127 i
  · exact column_a_128 i
  · exact column_a_129 i
  · exact column_a_130 i
  · exact column_a_131 i
  · exact column_a_132 i
  · exact column_a_133 i
  · exact column_a_134 i
  · exact column_a_135 i
  · exact column_a_136 i
  · exact column_a_137 i
  · exact column_a_138 i
  · exact column_a_139 i
  · exact column_a_140 i
  · exact column_a_141 i
  · exact column_a_142 i
  · exact column_a_143 i

private theorem column_b_0 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 0) =
    (leftB *ᵥ (fun h => quotient h 0)) i := by decide +kernel
private theorem column_b_1 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 1) =
    (leftB *ᵥ (fun h => quotient h 1)) i := by decide +kernel
private theorem column_b_2 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 2) =
    (leftB *ᵥ (fun h => quotient h 2)) i := by decide +kernel
private theorem column_b_3 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 3) =
    (leftB *ᵥ (fun h => quotient h 3)) i := by decide +kernel
private theorem column_b_4 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 4) =
    (leftB *ᵥ (fun h => quotient h 4)) i := by decide +kernel
private theorem column_b_5 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 5) =
    (leftB *ᵥ (fun h => quotient h 5)) i := by decide +kernel
private theorem column_b_6 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 6) =
    (leftB *ᵥ (fun h => quotient h 6)) i := by decide +kernel
private theorem column_b_7 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 7) =
    (leftB *ᵥ (fun h => quotient h 7)) i := by decide +kernel
private theorem column_b_8 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 8) =
    (leftB *ᵥ (fun h => quotient h 8)) i := by decide +kernel
private theorem column_b_9 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 9) =
    (leftB *ᵥ (fun h => quotient h 9)) i := by decide +kernel
private theorem column_b_10 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 10) =
    (leftB *ᵥ (fun h => quotient h 10)) i := by decide +kernel
private theorem column_b_11 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 11) =
    (leftB *ᵥ (fun h => quotient h 11)) i := by decide +kernel
private theorem column_b_12 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 12) =
    (leftB *ᵥ (fun h => quotient h 12)) i := by decide +kernel
private theorem column_b_13 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 13) =
    (leftB *ᵥ (fun h => quotient h 13)) i := by decide +kernel
private theorem column_b_14 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 14) =
    (leftB *ᵥ (fun h => quotient h 14)) i := by decide +kernel
private theorem column_b_15 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 15) =
    (leftB *ᵥ (fun h => quotient h 15)) i := by decide +kernel
private theorem column_b_16 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 16) =
    (leftB *ᵥ (fun h => quotient h 16)) i := by decide +kernel
private theorem column_b_17 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 17) =
    (leftB *ᵥ (fun h => quotient h 17)) i := by decide +kernel
private theorem column_b_18 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 18) =
    (leftB *ᵥ (fun h => quotient h 18)) i := by decide +kernel
private theorem column_b_19 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 19) =
    (leftB *ᵥ (fun h => quotient h 19)) i := by decide +kernel
private theorem column_b_20 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 20) =
    (leftB *ᵥ (fun h => quotient h 20)) i := by decide +kernel
private theorem column_b_21 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 21) =
    (leftB *ᵥ (fun h => quotient h 21)) i := by decide +kernel
private theorem column_b_22 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 22) =
    (leftB *ᵥ (fun h => quotient h 22)) i := by decide +kernel
private theorem column_b_23 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 23) =
    (leftB *ᵥ (fun h => quotient h 23)) i := by decide +kernel
private theorem column_b_24 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 24) =
    (leftB *ᵥ (fun h => quotient h 24)) i := by decide +kernel
private theorem column_b_25 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 25) =
    (leftB *ᵥ (fun h => quotient h 25)) i := by decide +kernel
private theorem column_b_26 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 26) =
    (leftB *ᵥ (fun h => quotient h 26)) i := by decide +kernel
private theorem column_b_27 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 27) =
    (leftB *ᵥ (fun h => quotient h 27)) i := by decide +kernel
private theorem column_b_28 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 28) =
    (leftB *ᵥ (fun h => quotient h 28)) i := by decide +kernel
private theorem column_b_29 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 29) =
    (leftB *ᵥ (fun h => quotient h 29)) i := by decide +kernel
private theorem column_b_30 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 30) =
    (leftB *ᵥ (fun h => quotient h 30)) i := by decide +kernel
private theorem column_b_31 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 31) =
    (leftB *ᵥ (fun h => quotient h 31)) i := by decide +kernel
private theorem column_b_32 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 32) =
    (leftB *ᵥ (fun h => quotient h 32)) i := by decide +kernel
private theorem column_b_33 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 33) =
    (leftB *ᵥ (fun h => quotient h 33)) i := by decide +kernel
private theorem column_b_34 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 34) =
    (leftB *ᵥ (fun h => quotient h 34)) i := by decide +kernel
private theorem column_b_35 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 35) =
    (leftB *ᵥ (fun h => quotient h 35)) i := by decide +kernel
private theorem column_b_36 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 36) =
    (leftB *ᵥ (fun h => quotient h 36)) i := by decide +kernel
private theorem column_b_37 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 37) =
    (leftB *ᵥ (fun h => quotient h 37)) i := by decide +kernel
private theorem column_b_38 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 38) =
    (leftB *ᵥ (fun h => quotient h 38)) i := by decide +kernel
private theorem column_b_39 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 39) =
    (leftB *ᵥ (fun h => quotient h 39)) i := by decide +kernel
private theorem column_b_40 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 40) =
    (leftB *ᵥ (fun h => quotient h 40)) i := by decide +kernel
private theorem column_b_41 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 41) =
    (leftB *ᵥ (fun h => quotient h 41)) i := by decide +kernel
private theorem column_b_42 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 42) =
    (leftB *ᵥ (fun h => quotient h 42)) i := by decide +kernel
private theorem column_b_43 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 43) =
    (leftB *ᵥ (fun h => quotient h 43)) i := by decide +kernel
private theorem column_b_44 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 44) =
    (leftB *ᵥ (fun h => quotient h 44)) i := by decide +kernel
private theorem column_b_45 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 45) =
    (leftB *ᵥ (fun h => quotient h 45)) i := by decide +kernel
private theorem column_b_46 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 46) =
    (leftB *ᵥ (fun h => quotient h 46)) i := by decide +kernel
private theorem column_b_47 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 47) =
    (leftB *ᵥ (fun h => quotient h 47)) i := by decide +kernel
private theorem column_b_48 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 48) =
    (leftB *ᵥ (fun h => quotient h 48)) i := by decide +kernel
private theorem column_b_49 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 49) =
    (leftB *ᵥ (fun h => quotient h 49)) i := by decide +kernel
private theorem column_b_50 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 50) =
    (leftB *ᵥ (fun h => quotient h 50)) i := by decide +kernel
private theorem column_b_51 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 51) =
    (leftB *ᵥ (fun h => quotient h 51)) i := by decide +kernel
private theorem column_b_52 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 52) =
    (leftB *ᵥ (fun h => quotient h 52)) i := by decide +kernel
private theorem column_b_53 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 53) =
    (leftB *ᵥ (fun h => quotient h 53)) i := by decide +kernel
private theorem column_b_54 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 54) =
    (leftB *ᵥ (fun h => quotient h 54)) i := by decide +kernel
private theorem column_b_55 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 55) =
    (leftB *ᵥ (fun h => quotient h 55)) i := by decide +kernel
private theorem column_b_56 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 56) =
    (leftB *ᵥ (fun h => quotient h 56)) i := by decide +kernel
private theorem column_b_57 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 57) =
    (leftB *ᵥ (fun h => quotient h 57)) i := by decide +kernel
private theorem column_b_58 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 58) =
    (leftB *ᵥ (fun h => quotient h 58)) i := by decide +kernel
private theorem column_b_59 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 59) =
    (leftB *ᵥ (fun h => quotient h 59)) i := by decide +kernel
private theorem column_b_60 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 60) =
    (leftB *ᵥ (fun h => quotient h 60)) i := by decide +kernel
private theorem column_b_61 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 61) =
    (leftB *ᵥ (fun h => quotient h 61)) i := by decide +kernel
private theorem column_b_62 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 62) =
    (leftB *ᵥ (fun h => quotient h 62)) i := by decide +kernel
private theorem column_b_63 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 63) =
    (leftB *ᵥ (fun h => quotient h 63)) i := by decide +kernel
private theorem column_b_64 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 64) =
    (leftB *ᵥ (fun h => quotient h 64)) i := by decide +kernel
private theorem column_b_65 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 65) =
    (leftB *ᵥ (fun h => quotient h 65)) i := by decide +kernel
private theorem column_b_66 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 66) =
    (leftB *ᵥ (fun h => quotient h 66)) i := by decide +kernel
private theorem column_b_67 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 67) =
    (leftB *ᵥ (fun h => quotient h 67)) i := by decide +kernel
private theorem column_b_68 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 68) =
    (leftB *ᵥ (fun h => quotient h 68)) i := by decide +kernel
private theorem column_b_69 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 69) =
    (leftB *ᵥ (fun h => quotient h 69)) i := by decide +kernel
private theorem column_b_70 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 70) =
    (leftB *ᵥ (fun h => quotient h 70)) i := by decide +kernel
private theorem column_b_71 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 71) =
    (leftB *ᵥ (fun h => quotient h 71)) i := by decide +kernel
private theorem column_b_72 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 72) =
    (leftB *ᵥ (fun h => quotient h 72)) i := by decide +kernel
private theorem column_b_73 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 73) =
    (leftB *ᵥ (fun h => quotient h 73)) i := by decide +kernel
private theorem column_b_74 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 74) =
    (leftB *ᵥ (fun h => quotient h 74)) i := by decide +kernel
private theorem column_b_75 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 75) =
    (leftB *ᵥ (fun h => quotient h 75)) i := by decide +kernel
private theorem column_b_76 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 76) =
    (leftB *ᵥ (fun h => quotient h 76)) i := by decide +kernel
private theorem column_b_77 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 77) =
    (leftB *ᵥ (fun h => quotient h 77)) i := by decide +kernel
private theorem column_b_78 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 78) =
    (leftB *ᵥ (fun h => quotient h 78)) i := by decide +kernel
private theorem column_b_79 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 79) =
    (leftB *ᵥ (fun h => quotient h 79)) i := by decide +kernel
private theorem column_b_80 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 80) =
    (leftB *ᵥ (fun h => quotient h 80)) i := by decide +kernel
private theorem column_b_81 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 81) =
    (leftB *ᵥ (fun h => quotient h 81)) i := by decide +kernel
private theorem column_b_82 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 82) =
    (leftB *ᵥ (fun h => quotient h 82)) i := by decide +kernel
private theorem column_b_83 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 83) =
    (leftB *ᵥ (fun h => quotient h 83)) i := by decide +kernel
private theorem column_b_84 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 84) =
    (leftB *ᵥ (fun h => quotient h 84)) i := by decide +kernel
private theorem column_b_85 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 85) =
    (leftB *ᵥ (fun h => quotient h 85)) i := by decide +kernel
private theorem column_b_86 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 86) =
    (leftB *ᵥ (fun h => quotient h 86)) i := by decide +kernel
private theorem column_b_87 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 87) =
    (leftB *ᵥ (fun h => quotient h 87)) i := by decide +kernel
private theorem column_b_88 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 88) =
    (leftB *ᵥ (fun h => quotient h 88)) i := by decide +kernel
private theorem column_b_89 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 89) =
    (leftB *ᵥ (fun h => quotient h 89)) i := by decide +kernel
private theorem column_b_90 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 90) =
    (leftB *ᵥ (fun h => quotient h 90)) i := by decide +kernel
private theorem column_b_91 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 91) =
    (leftB *ᵥ (fun h => quotient h 91)) i := by decide +kernel
private theorem column_b_92 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 92) =
    (leftB *ᵥ (fun h => quotient h 92)) i := by decide +kernel
private theorem column_b_93 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 93) =
    (leftB *ᵥ (fun h => quotient h 93)) i := by decide +kernel
private theorem column_b_94 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 94) =
    (leftB *ᵥ (fun h => quotient h 94)) i := by decide +kernel
private theorem column_b_95 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 95) =
    (leftB *ᵥ (fun h => quotient h 95)) i := by decide +kernel
private theorem column_b_96 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 96) =
    (leftB *ᵥ (fun h => quotient h 96)) i := by decide +kernel
private theorem column_b_97 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 97) =
    (leftB *ᵥ (fun h => quotient h 97)) i := by decide +kernel
private theorem column_b_98 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 98) =
    (leftB *ᵥ (fun h => quotient h 98)) i := by decide +kernel
private theorem column_b_99 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 99) =
    (leftB *ᵥ (fun h => quotient h 99)) i := by decide +kernel
private theorem column_b_100 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 100) =
    (leftB *ᵥ (fun h => quotient h 100)) i := by decide +kernel
private theorem column_b_101 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 101) =
    (leftB *ᵥ (fun h => quotient h 101)) i := by decide +kernel
private theorem column_b_102 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 102) =
    (leftB *ᵥ (fun h => quotient h 102)) i := by decide +kernel
private theorem column_b_103 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 103) =
    (leftB *ᵥ (fun h => quotient h 103)) i := by decide +kernel
private theorem column_b_104 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 104) =
    (leftB *ᵥ (fun h => quotient h 104)) i := by decide +kernel
private theorem column_b_105 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 105) =
    (leftB *ᵥ (fun h => quotient h 105)) i := by decide +kernel
private theorem column_b_106 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 106) =
    (leftB *ᵥ (fun h => quotient h 106)) i := by decide +kernel
private theorem column_b_107 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 107) =
    (leftB *ᵥ (fun h => quotient h 107)) i := by decide +kernel
private theorem column_b_108 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 108) =
    (leftB *ᵥ (fun h => quotient h 108)) i := by decide +kernel
private theorem column_b_109 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 109) =
    (leftB *ᵥ (fun h => quotient h 109)) i := by decide +kernel
private theorem column_b_110 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 110) =
    (leftB *ᵥ (fun h => quotient h 110)) i := by decide +kernel
private theorem column_b_111 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 111) =
    (leftB *ᵥ (fun h => quotient h 111)) i := by decide +kernel
private theorem column_b_112 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 112) =
    (leftB *ᵥ (fun h => quotient h 112)) i := by decide +kernel
private theorem column_b_113 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 113) =
    (leftB *ᵥ (fun h => quotient h 113)) i := by decide +kernel
private theorem column_b_114 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 114) =
    (leftB *ᵥ (fun h => quotient h 114)) i := by decide +kernel
private theorem column_b_115 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 115) =
    (leftB *ᵥ (fun h => quotient h 115)) i := by decide +kernel
private theorem column_b_116 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 116) =
    (leftB *ᵥ (fun h => quotient h 116)) i := by decide +kernel
private theorem column_b_117 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 117) =
    (leftB *ᵥ (fun h => quotient h 117)) i := by decide +kernel
private theorem column_b_118 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 118) =
    (leftB *ᵥ (fun h => quotient h 118)) i := by decide +kernel
private theorem column_b_119 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 119) =
    (leftB *ᵥ (fun h => quotient h 119)) i := by decide +kernel
private theorem column_b_120 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 120) =
    (leftB *ᵥ (fun h => quotient h 120)) i := by decide +kernel
private theorem column_b_121 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 121) =
    (leftB *ᵥ (fun h => quotient h 121)) i := by decide +kernel
private theorem column_b_122 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 122) =
    (leftB *ᵥ (fun h => quotient h 122)) i := by decide +kernel
private theorem column_b_123 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 123) =
    (leftB *ᵥ (fun h => quotient h 123)) i := by decide +kernel
private theorem column_b_124 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 124) =
    (leftB *ᵥ (fun h => quotient h 124)) i := by decide +kernel
private theorem column_b_125 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 125) =
    (leftB *ᵥ (fun h => quotient h 125)) i := by decide +kernel
private theorem column_b_126 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 126) =
    (leftB *ᵥ (fun h => quotient h 126)) i := by decide +kernel
private theorem column_b_127 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 127) =
    (leftB *ᵥ (fun h => quotient h 127)) i := by decide +kernel
private theorem column_b_128 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 128) =
    (leftB *ᵥ (fun h => quotient h 128)) i := by decide +kernel
private theorem column_b_129 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 129) =
    (leftB *ᵥ (fun h => quotient h 129)) i := by decide +kernel
private theorem column_b_130 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 130) =
    (leftB *ᵥ (fun h => quotient h 130)) i := by decide +kernel
private theorem column_b_131 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 131) =
    (leftB *ᵥ (fun h => quotient h 131)) i := by decide +kernel
private theorem column_b_132 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 132) =
    (leftB *ᵥ (fun h => quotient h 132)) i := by decide +kernel
private theorem column_b_133 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 133) =
    (leftB *ᵥ (fun h => quotient h 133)) i := by decide +kernel
private theorem column_b_134 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 134) =
    (leftB *ᵥ (fun h => quotient h 134)) i := by decide +kernel
private theorem column_b_135 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 135) =
    (leftB *ᵥ (fun h => quotient h 135)) i := by decide +kernel
private theorem column_b_136 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 136) =
    (leftB *ᵥ (fun h => quotient h 136)) i := by decide +kernel
private theorem column_b_137 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 137) =
    (leftB *ᵥ (fun h => quotient h 137)) i := by decide +kernel
private theorem column_b_138 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 138) =
    (leftB *ᵥ (fun h => quotient h 138)) i := by decide +kernel
private theorem column_b_139 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 139) =
    (leftB *ᵥ (fun h => quotient h 139)) i := by decide +kernel
private theorem column_b_140 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 140) =
    (leftB *ᵥ (fun h => quotient h 140)) i := by decide +kernel
private theorem column_b_141 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 141) =
    (leftB *ᵥ (fun h => quotient h 141)) i := by decide +kernel
private theorem column_b_142 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 142) =
    (leftB *ᵥ (fun h => quotient h 142)) i := by decide +kernel
private theorem column_b_143 : ∀ i : Fin 16, quotient i (PSL33SingerCosetData.permB 143) =
    (leftB *ᵥ (fun h => quotient h 143)) i := by decide +kernel
theorem column_b (j : Fin 144) :
    (fun i => quotient i (PSL33SingerCosetData.permB j)) = leftB *ᵥ (fun i => quotient i j) := by
  funext i
  fin_cases j
  · exact column_b_0 i
  · exact column_b_1 i
  · exact column_b_2 i
  · exact column_b_3 i
  · exact column_b_4 i
  · exact column_b_5 i
  · exact column_b_6 i
  · exact column_b_7 i
  · exact column_b_8 i
  · exact column_b_9 i
  · exact column_b_10 i
  · exact column_b_11 i
  · exact column_b_12 i
  · exact column_b_13 i
  · exact column_b_14 i
  · exact column_b_15 i
  · exact column_b_16 i
  · exact column_b_17 i
  · exact column_b_18 i
  · exact column_b_19 i
  · exact column_b_20 i
  · exact column_b_21 i
  · exact column_b_22 i
  · exact column_b_23 i
  · exact column_b_24 i
  · exact column_b_25 i
  · exact column_b_26 i
  · exact column_b_27 i
  · exact column_b_28 i
  · exact column_b_29 i
  · exact column_b_30 i
  · exact column_b_31 i
  · exact column_b_32 i
  · exact column_b_33 i
  · exact column_b_34 i
  · exact column_b_35 i
  · exact column_b_36 i
  · exact column_b_37 i
  · exact column_b_38 i
  · exact column_b_39 i
  · exact column_b_40 i
  · exact column_b_41 i
  · exact column_b_42 i
  · exact column_b_43 i
  · exact column_b_44 i
  · exact column_b_45 i
  · exact column_b_46 i
  · exact column_b_47 i
  · exact column_b_48 i
  · exact column_b_49 i
  · exact column_b_50 i
  · exact column_b_51 i
  · exact column_b_52 i
  · exact column_b_53 i
  · exact column_b_54 i
  · exact column_b_55 i
  · exact column_b_56 i
  · exact column_b_57 i
  · exact column_b_58 i
  · exact column_b_59 i
  · exact column_b_60 i
  · exact column_b_61 i
  · exact column_b_62 i
  · exact column_b_63 i
  · exact column_b_64 i
  · exact column_b_65 i
  · exact column_b_66 i
  · exact column_b_67 i
  · exact column_b_68 i
  · exact column_b_69 i
  · exact column_b_70 i
  · exact column_b_71 i
  · exact column_b_72 i
  · exact column_b_73 i
  · exact column_b_74 i
  · exact column_b_75 i
  · exact column_b_76 i
  · exact column_b_77 i
  · exact column_b_78 i
  · exact column_b_79 i
  · exact column_b_80 i
  · exact column_b_81 i
  · exact column_b_82 i
  · exact column_b_83 i
  · exact column_b_84 i
  · exact column_b_85 i
  · exact column_b_86 i
  · exact column_b_87 i
  · exact column_b_88 i
  · exact column_b_89 i
  · exact column_b_90 i
  · exact column_b_91 i
  · exact column_b_92 i
  · exact column_b_93 i
  · exact column_b_94 i
  · exact column_b_95 i
  · exact column_b_96 i
  · exact column_b_97 i
  · exact column_b_98 i
  · exact column_b_99 i
  · exact column_b_100 i
  · exact column_b_101 i
  · exact column_b_102 i
  · exact column_b_103 i
  · exact column_b_104 i
  · exact column_b_105 i
  · exact column_b_106 i
  · exact column_b_107 i
  · exact column_b_108 i
  · exact column_b_109 i
  · exact column_b_110 i
  · exact column_b_111 i
  · exact column_b_112 i
  · exact column_b_113 i
  · exact column_b_114 i
  · exact column_b_115 i
  · exact column_b_116 i
  · exact column_b_117 i
  · exact column_b_118 i
  · exact column_b_119 i
  · exact column_b_120 i
  · exact column_b_121 i
  · exact column_b_122 i
  · exact column_b_123 i
  · exact column_b_124 i
  · exact column_b_125 i
  · exact column_b_126 i
  · exact column_b_127 i
  · exact column_b_128 i
  · exact column_b_129 i
  · exact column_b_130 i
  · exact column_b_131 i
  · exact column_b_132 i
  · exact column_b_133 i
  · exact column_b_134 i
  · exact column_b_135 i
  · exact column_b_136 i
  · exact column_b_137 i
  · exact column_b_138 i
  · exact column_b_139 i
  · exact column_b_140 i
  · exact column_b_141 i
  · exact column_b_142 i
  · exact column_b_143 i

end Kourovka2135.PSL33SingerSixteenData
