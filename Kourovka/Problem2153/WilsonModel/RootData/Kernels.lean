import Kourovka.Problem2153.WilsonModel.RootData.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8 F8

/-- A generator for the kernel of each root's torus weight; indices are field codes minus one. -/
def kernelParameters : Fin 12 → Fin 7 × Fin 7 :=
  ![(4, 4), (6, 2), (5, 3), (5, 1), (2, 0), (1, 2), (0, 5), (4, 2), (5, 4), (2, 5), (1, 0), (0, 4)]

/-- Canonical exponent sections supplied by the exact torus-orbit reduction. -/
def sectionExponents : Fin 12 → Fin 7 × Fin 7 :=
  ![(0, 6), (0, 3), (0, 2), (0, 2), (0, 5), (0, 1), (5, 0), (0, 6), (0, 2), (0, 5), (0, 1), (1, 0)]

def kernelLeft (i : Fin 12) : Mat := fun j k =>
  rootMatrix i 1 j k * torusDiag (kernelParameters i).1 (kernelParameters i).2 k

def kernelRight (i : Fin 12) : Mat := fun j k =>
  torusDiag (kernelParameters i).1 (kernelParameters i).2 j * rootMatrix i 1 j k

theorem kernel_matrix_0 : kernelLeft 0 = kernelRight 0 := by decide +kernel

theorem kernel_matrix_1 : kernelLeft 1 = kernelRight 1 := by decide +kernel

theorem kernel_matrix_2 : kernelLeft 2 = kernelRight 2 := by decide +kernel

theorem kernel_matrix_3 : kernelLeft 3 = kernelRight 3 := by decide +kernel

theorem kernel_matrix_4 : kernelLeft 4 = kernelRight 4 := by decide +kernel

theorem kernel_matrix_5 : kernelLeft 5 = kernelRight 5 := by decide +kernel

theorem kernel_matrix_6 : kernelLeft 6 = kernelRight 6 := by decide +kernel

theorem kernel_matrix_7 : kernelLeft 7 = kernelRight 7 := by decide +kernel

theorem kernel_matrix_8 : kernelLeft 8 = kernelRight 8 := by decide +kernel

theorem kernel_matrix_9 : kernelLeft 9 = kernelRight 9 := by decide +kernel

theorem kernel_matrix_10 : kernelLeft 10 = kernelRight 10 := by decide +kernel

theorem kernel_matrix_11 : kernelLeft 11 = kernelRight 11 := by decide +kernel

theorem kernel_matrix (i : Fin 12) : kernelLeft i = kernelRight i := by
  fin_cases i
  · exact kernel_matrix_0
  · exact kernel_matrix_1
  · exact kernel_matrix_2
  · exact kernel_matrix_3
  · exact kernel_matrix_4
  · exact kernel_matrix_5
  · exact kernel_matrix_6
  · exact kernel_matrix_7
  · exact kernel_matrix_8
  · exact kernel_matrix_9
  · exact kernel_matrix_10
  · exact kernel_matrix_11

/-- Actual root-base/kernel commutation in the concrete generated ambient group. -/
theorem rootBase_kernel_commute (i : Fin 12) :
    Commute (RootSystem.rootBase i)
      (RootSystem.torus (kernelParameters i).1 (kernelParameters i).2) := by
  apply matrixHom_injective
  simp only [map_mul, rootBase_alignment]
  change rootMatrix i 1 * Matrix.diagonal (torusDiag (kernelParameters i).1
    (kernelParameters i).2) = Matrix.diagonal (torusDiag (kernelParameters i).1
    (kernelParameters i).2) * rootMatrix i 1
  ext j k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact congrFun (congrFun (kernel_matrix i) j) k

end Kourovka.Problem2153.WilsonModel.RootData
