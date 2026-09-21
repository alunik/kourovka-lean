import Kourovka2135.SL33FlagData
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Finite coordinate certificates for a27-dimensional invariant subspace
of the actual52-flag permutation module and its26-dimensional quotient.
Rows are binary polynomial bits; all identities are ordinary Lean decisions. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Kourovka2135.PSL33CycleData
abbrev k := ZMod 2

def bitMatrix {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) k :=
  fun i j => if (rows i).testBit j.val then 1 else 0

def embedding : Matrix (Fin 52) (Fin 27) k :=
  bitMatrix ![48801279, 511, 14721024, 34079744, 69566097, 32257, 2359312, 67174528, 23040586, 229896, 1839168, 20971522, 127027492, 117456928, 1179652, 8390912, 7, 1, 2, 4, 56, 8, 16, 32, 448, 64, 128, 256, 3584, 512, 1024, 2048, 28672, 4096, 8192, 16384, 229376, 32768, 65536, 131072, 1835008, 262144, 524288, 1048576, 14680064, 2097152, 4194304, 8388608, 117440512, 16777216, 33554432, 67108864]

def leftInverse : Matrix (Fin 27) (Fin 52) k :=
  bitMatrix ![131072, 262144, 524288, 2097152, 4194304, 8388608, 33554432, 67108864, 134217728, 536870912, 1073741824, 2147483648, 8589934592, 17179869184, 34359738368, 137438953472, 274877906944, 549755813888, 2199023255552, 4398046511104, 8796093022208, 35184372088832, 70368744177664, 140737488355328, 562949953421312, 1125899906842624, 2251799813685248]

def quotient : Matrix (Fin 26) (Fin 27) k :=
  bitMatrix ![67108865, 67108866, 67108868, 67108872, 67108880, 67108896, 67108928, 67108992, 67109120, 67109376, 67109888, 67110912, 67112960, 67117056, 67125248, 67141632, 67174400, 67239936, 67371008, 67633152, 68157440, 69206016, 71303168, 75497472, 83886080, 100663296]

def sectionMatrix : Matrix (Fin 27) (Fin 26) k :=
  bitMatrix ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 0]

def cycleA : Matrix (Fin 27) (Fin 27) k :=
  bitMatrix ![7, 2, 4, 4096, 8192, 16384, 512, 1024, 2048, 64, 128, 256, 8, 16, 32, 262144, 524288, 1048576, 32768, 65536, 131072, 14680064, 4194304, 8388608, 16777216, 67108864, 33554432]

def cycleB : Matrix (Fin 27) (Fin 27) k :=
  bitMatrix ![3584, 1024, 2048, 23040586, 20971522, 1839168, 32768, 131072, 65536, 69566097, 2359312, 67174528, 8192, 16384, 4096, 117456928, 1179652, 8390912, 4194304, 2097152, 8388608, 16777216, 33554432, 67108864, 524288, 262144, 1048576]

def cycleBInv : Matrix (Fin 27) (Fin 27) k :=
  bitMatrix ![32257, 2359312, 67174528, 511, 34079744, 14721024, 117456928, 8390912, 1179652, 7, 2, 4, 16384, 4096, 8192, 64, 256, 128, 33554432, 16777216, 67108864, 524288, 262144, 1048576, 2097152, 4194304, 8388608]

def targetA : Matrix (Fin 26) (Fin 26) k :=
  bitMatrix ![33554439, 33554434, 33554436, 33558528, 33562624, 33570816, 33554944, 33555456, 33556480, 33554496, 33554560, 33554688, 33554440, 33554448, 33554464, 33816576, 34078720, 34603008, 33587200, 33619968, 33685504, 48234496, 37748736, 41943040, 50331648, 33554432]

def targetB : Matrix (Fin 26) (Fin 26) k :=
  bitMatrix ![1052160, 1049600, 1050624, 21992010, 22020098, 790592, 1081344, 1179648, 1114112, 3505809, 3407888, 1114240, 1056768, 1064960, 1052672, 51396640, 131076, 9439488, 5242880, 3145728, 9437184, 17825792, 34603008, 1048576, 1572864, 1310720]

def targetBInv : Matrix (Fin 26) (Fin 26) k :=
  bitMatrix ![8420865, 10747920, 8454272, 8389119, 42468352, 6332416, 58736672, 2304, 9568260, 8388615, 8388610, 8388612, 8404992, 8392704, 8396800, 8388672, 8388864, 8388736, 41943040, 25165824, 8388608, 8912896, 8650752, 9437184, 10485760, 12582912]

theorem leftInverse_embedding : leftInverse * embedding = 1 := by decide +kernel

theorem quotient_section : quotient * sectionMatrix = 1 := by decide +kernel

theorem cycleA_inverse : cycleA * cycleA = 1 := by decide +kernel

theorem cycleB_inverse : cycleB * cycleBInv = 1 ∧ cycleBInv * cycleB = 1 := by decide +kernel

/-- Actual flag action on the columns of the embedding. -/
theorem embedding_a :
    (fun i j => embedding (SL33FlagData.permA.symm i) j) = embedding * cycleA := by decide +kernel

theorem embedding_b :
    (fun i j => embedding (SL33FlagData.permB.symm i) j) = embedding * cycleB := by decide +kernel

theorem targetA_inverse : targetA * targetA = 1 := by decide +kernel

theorem targetB_inverse : targetB * targetBInv = 1 ∧ targetBInv * targetB = 1 := by decide +kernel

theorem quotient_a : quotient * cycleA = targetA * quotient := by decide +kernel

theorem quotient_b : quotient * cycleB = targetB * quotient := by decide +kernel

end Kourovka2135.PSL33CycleData
