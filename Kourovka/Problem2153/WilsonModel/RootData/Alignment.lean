import Kourovka.Problem2153.WilsonModel.RootData.Tables
import Kourovka.Problem2153.WilsonModel.SparseBenchmark
import Kourovka.Problem2153.RootSystem
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8 F8

/-- The actual matrix homomorphism of the concrete ambient subgroup. -/
def matrixHom : RootSystem.G →* Mat := (Units.coeHom Mat).comp ambient.subtype

theorem matrix_conj_r (g : RootSystem.G) :
    matrixHom (rightConj g RootSystem.r) = rho * matrixHom g * rho := rfl

theorem matrix_conj_s (g : RootSystem.G) :
    matrixHom (rightConj g RootSystem.s) = sigma * matrixHom g * sigma := rfl

def baseLeft2Rows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(0, e1)],
    [(1, e1), (2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(5, e1), (7, e1)],
    [(6, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(8, e1), (10, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(14, e1)],
    [(10, e1), (12, e1), (13, e1)],
    [(10, e1), (13, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(14, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(21, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (18, e1)],
    [(21, e1), (22, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(21, e1), (22, e1), (23, e1)],
    [(25, e1)],
    [(21, e1), (23, e1), (24, e1)]]
def baseLeft2 : Mat := Sparse.eval baseLeft2Rows
theorem baseLeft2_eq : sigma * rootMatrix 1 1 = baseLeft2 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment
  decide +kernel

theorem baseRight2_eq : baseLeft2 * sigma = rootMatrix 2 1 := by
  apply Sparse.mul_eq_of_check baseLeft2Rows
  decide +kernel

def baseLeft4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(0, e1), (2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(3, e1), (6, e1)],
    [(4, e1), (9, e1)],
    [(17, e1)],
    [(7, e1)],
    [(11, e1), (15, e1)],
    [(0, e1), (2, e1), (5, e1)],
    [(9, e1), (12, e1)],
    [(9, e1), (13, e1)],
    [(17, e1), (20, e1)],
    [(3, e1), (6, e1), (10, e1)],
    [(18, e1)],
    [(0, e1), (5, e1), (8, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(11, e1), (15, e1), (19, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(17, e1), (23, e1), (25, e1)]]
def baseLeft4 : Mat := Sparse.eval baseLeft4Rows
theorem baseLeft4_eq : rho * rootMatrix 2 1 = baseLeft4 := by
  apply Sparse.mul_eq_of_check_alignment rho rhoSparse _ _ rho_alignment
  decide +kernel

theorem baseRight4_eq : baseLeft4 * rho = rootMatrix 4 1 := by
  apply Sparse.mul_eq_of_check baseLeft4Rows
  decide +kernel

def baseLeft5Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(0, e1), (1, e1)],
    [(11, e1)],
    [(4, e1), (6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(4, e1), (7, e1)],
    [(15, e1)],
    [(3, e1), (5, e1)],
    [(11, e1), (12, e1)],
    [(13, e1)],
    [(20, e1)],
    [(9, e1), (10, e1)],
    [(17, e1), (18, e1)],
    [(4, e1), (6, e1), (7, e1), (8, e1)],
    [(15, e1), (16, e1)],
    [(17, e1), (19, e1)],
    [(11, e1), (13, e1), (14, e1)],
    [(24, e1)],
    [(23, e1)],
    [(20, e1), (22, e1)],
    [(17, e1), (18, e1), (19, e1), (21, e1)],
    [(24, e1), (25, e1)]]
def baseLeft5 : Mat := Sparse.eval baseLeft5Rows
theorem baseLeft5_eq : rho * rootMatrix 0 1 = baseLeft5 := by
  apply Sparse.mul_eq_of_check_alignment rho rhoSparse _ _ rho_alignment
  decide +kernel

theorem baseRight5_eq : baseLeft5 * rho = rootMatrix 5 1 := by
  apply Sparse.mul_eq_of_check baseLeft5Rows
  decide +kernel

def baseLeft6Rows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(0, e1), (3, e1)],
    [(1, e1), (7, e1)],
    [(2, e1), (6, e1)],
    [(4, e1)],
    [(5, e1), (10, e1)],
    [(9, e1)],
    [(8, e1), (14, e1)],
    [(12, e1), (13, e1)],
    [(7, e1), (13, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(16, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(21, e1)],
    [(5, e1), (10, e1), (19, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (18, e1)],
    [(8, e1), (14, e1), (22, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(5, e1), (19, e1), (23, e1)],
    [(8, e1), (22, e1), (25, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)]]
def baseLeft6 : Mat := Sparse.eval baseLeft6Rows
theorem baseLeft6_eq : sigma * rootMatrix 4 1 = baseLeft6 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment
  decide +kernel

theorem baseRight6_eq : baseLeft6 * sigma = rootMatrix 6 1 := by
  apply Sparse.mul_eq_of_check baseLeft6Rows
  decide +kernel

def baseLeft7Rows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(1, e1), (3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(10, e1)],
    [(5, e1), (9, e1)],
    [(14, e1)],
    [(8, e1), (12, e1), (13, e1)],
    [(8, e1), (13, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(16, e1)],
    [(8, e1), (15, e1)],
    [(21, e1)],
    [(19, e1)],
    [(14, e1), (18, e1)],
    [(22, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(21, e1), (23, e1)],
    [(25, e1)],
    [(21, e1), (22, e1), (24, e1)]]
def baseLeft7 : Mat := Sparse.eval baseLeft7Rows
theorem baseLeft7_eq : sigma * rootMatrix 3 1 = baseLeft7 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment
  decide +kernel

theorem baseRight7_eq : baseLeft7 * sigma = rootMatrix 7 1 := by
  apply Sparse.mul_eq_of_check baseLeft7Rows
  decide +kernel

def baseLeft8Rows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(1, e1), (6, e1)],
    [(0, e1), (4, e1)],
    [(10, e1)],
    [(1, e1), (9, e1)],
    [(14, e1)],
    [(5, e1), (12, e1), (13, e1)],
    [(13, e1)],
    [(2, e1), (11, e1)],
    [(8, e1), (16, e1)],
    [(7, e1), (15, e1)],
    [(21, e1)],
    [(8, e1), (19, e1)],
    [(10, e1), (18, e1)],
    [(22, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(14, e1), (23, e1)],
    [(21, e1), (25, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)]]
def baseLeft8 : Mat := Sparse.eval baseLeft8Rows
theorem baseLeft8_eq : sigma * rootMatrix 5 1 = baseLeft8 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment
  decide +kernel

theorem baseRight8_eq : baseLeft8 * sigma = rootMatrix 8 1 := by
  apply Sparse.mul_eq_of_check baseLeft8Rows
  decide +kernel

def baseLeft9Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(0, e1), (7, e1)],
    [(4, e1), (15, e1)],
    [(5, e1)],
    [(3, e1), (12, e1)],
    [(13, e1)],
    [(20, e1)],
    [(0, e1), (10, e1)],
    [(4, e1), (18, e1)],
    [(1, e1), (8, e1)],
    [(6, e1), (16, e1)],
    [(9, e1), (19, e1)],
    [(2, e1), (14, e1)],
    [(17, e1), (24, e1)],
    [(11, e1), (23, e1)],
    [(3, e1), (13, e1), (22, e1)],
    [(0, e1), (7, e1), (10, e1), (21, e1)],
    [(4, e1), (15, e1), (18, e1), (25, e1)]]
def baseLeft9 : Mat := Sparse.eval baseLeft9Rows
theorem baseLeft9_eq : rho * rootMatrix 8 1 = baseLeft9 := by
  apply Sparse.mul_eq_of_check_alignment rho rhoSparse _ _ rho_alignment
  decide +kernel

theorem baseRight9_eq : baseLeft9 * rho = rootMatrix 9 1 := by
  apply Sparse.mul_eq_of_check baseLeft9Rows
  decide +kernel

def baseLeft10Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(4, e1)],
    [(3, e1)],
    [(2, e1)],
    [(1, e1)],
    [(11, e1)],
    [(6, e1)],
    [(9, e1)],
    [(17, e1)],
    [(7, e1)],
    [(15, e1)],
    [(0, e1), (5, e1)],
    [(4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(20, e1)],
    [(3, e1), (10, e1)],
    [(18, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(4, e1), (16, e1)],
    [(11, e1), (19, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(24, e1)],
    [(17, e1), (23, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(17, e1), (20, e1), (25, e1)]]
def baseLeft10 : Mat := Sparse.eval baseLeft10Rows
theorem baseLeft10_eq : rho * rootMatrix 7 1 = baseLeft10 := by
  apply Sparse.mul_eq_of_check_alignment rho rhoSparse _ _ rho_alignment
  decide +kernel

theorem baseRight10_eq : baseLeft10 * rho = rootMatrix 10 1 := by
  apply Sparse.mul_eq_of_check baseLeft10Rows
  decide +kernel

def baseLeft11Rows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(0, e1)],
    [(2, e1)],
    [(5, e1)],
    [(8, e1)],
    [(3, e1)],
    [(7, e1)],
    [(6, e1)],
    [(4, e1)],
    [(10, e1)],
    [(9, e1)],
    [(14, e1)],
    [(12, e1), (13, e1)],
    [(1, e1), (13, e1)],
    [(0, e1), (11, e1)],
    [(16, e1)],
    [(2, e1), (15, e1)],
    [(21, e1)],
    [(5, e1), (19, e1)],
    [(1, e1), (18, e1)],
    [(8, e1), (22, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(8, e1), (14, e1), (25, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)]]
def baseLeft11 : Mat := Sparse.eval baseLeft11Rows
theorem baseLeft11_eq : sigma * rootMatrix 10 1 = baseLeft11 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse _ _ sigma_alignment
  decide +kernel

theorem baseRight11_eq : baseLeft11 * sigma = rootMatrix 11 1 := by
  apply Sparse.mul_eq_of_check baseLeft11Rows
  decide +kernel

theorem base_alignment_0 : matrixHom (RootSystem.rootBase 0) = rootMatrix 0 1 := by
  change wilsonT = rootMatrix 0 1
  decide +kernel

theorem base_alignment_1 : matrixHom (RootSystem.rootBase 1) = rootMatrix 1 1 := by
  change wilsonX = rootMatrix 1 1
  decide +kernel

theorem base_alignment_3 : matrixHom (RootSystem.rootBase 3) = rootMatrix 3 1 := by
  change wilsonX ^ 2 = rootMatrix 3 1
  rw [pow_two, x2_eq]
  decide +kernel

theorem base_alignment_2 : matrixHom (RootSystem.rootBase 2) = rootMatrix 2 1 := by
  change matrixHom (rightConj RootSystem.x RootSystem.s) = rootMatrix 2 1
  rw [matrix_conj_s]
  change sigma * matrixHom (RootSystem.rootBase 1) * sigma = rootMatrix 2 1
  rw [base_alignment_1, baseLeft2_eq, baseRight2_eq]

theorem base_alignment_4 : matrixHom (RootSystem.rootBase 4) = rootMatrix 4 1 := by
  change matrixHom (rightConj RootSystem.x (RootSystem.s * RootSystem.r)) = rootMatrix 4 1
  rw [rightConj_mul]
  rw [matrix_conj_r]
  change rho * matrixHom (RootSystem.rootBase 2) * rho = rootMatrix 4 1
  rw [base_alignment_2, baseLeft4_eq, baseRight4_eq]

theorem base_alignment_5 : matrixHom (RootSystem.rootBase 5) = rootMatrix 5 1 := by
  change matrixHom (rightConj RootSystem.t RootSystem.r) = rootMatrix 5 1
  rw [matrix_conj_r]
  change rho * matrixHom (RootSystem.rootBase 0) * rho = rootMatrix 5 1
  rw [base_alignment_0, baseLeft5_eq, baseRight5_eq]

theorem base_alignment_6 : matrixHom (RootSystem.rootBase 6) = rootMatrix 6 1 := by
  change matrixHom (rightConj RootSystem.x (RootSystem.s * RootSystem.r * RootSystem.s)) = rootMatrix 6 1
  rw [rightConj_mul]
  rw [matrix_conj_s]
  change sigma * matrixHom (RootSystem.rootBase 4) * sigma = rootMatrix 6 1
  rw [base_alignment_4, baseLeft6_eq, baseRight6_eq]

theorem base_alignment_7 : matrixHom (RootSystem.rootBase 7) = rootMatrix 7 1 := by
  change matrixHom (rightConj (RootSystem.x ^ 2) RootSystem.s) = rootMatrix 7 1
  rw [matrix_conj_s]
  change sigma * matrixHom (RootSystem.rootBase 3) * sigma = rootMatrix 7 1
  rw [base_alignment_3, baseLeft7_eq, baseRight7_eq]

theorem base_alignment_8 : matrixHom (RootSystem.rootBase 8) = rootMatrix 8 1 := by
  change matrixHom (rightConj RootSystem.t (RootSystem.r * RootSystem.s)) = rootMatrix 8 1
  rw [rightConj_mul]
  rw [matrix_conj_s]
  change sigma * matrixHom (RootSystem.rootBase 5) * sigma = rootMatrix 8 1
  rw [base_alignment_5, baseLeft8_eq, baseRight8_eq]

theorem base_alignment_9 : matrixHom (RootSystem.rootBase 9) = rootMatrix 9 1 := by
  change matrixHom (rightConj RootSystem.t (RootSystem.r * RootSystem.s * RootSystem.r)) = rootMatrix 9 1
  rw [rightConj_mul]
  rw [matrix_conj_r]
  change rho * matrixHom (RootSystem.rootBase 8) * rho = rootMatrix 9 1
  rw [base_alignment_8, baseLeft9_eq, baseRight9_eq]

theorem base_alignment_10 : matrixHom (RootSystem.rootBase 10) = rootMatrix 10 1 := by
  change matrixHom (rightConj (RootSystem.x ^ 2) (RootSystem.s * RootSystem.r)) = rootMatrix 10 1
  rw [rightConj_mul]
  rw [matrix_conj_r]
  change rho * matrixHom (RootSystem.rootBase 7) * rho = rootMatrix 10 1
  rw [base_alignment_7, baseLeft10_eq, baseRight10_eq]

theorem base_alignment_11 : matrixHom (RootSystem.rootBase 11) = rootMatrix 11 1 := by
  change matrixHom (rightConj (RootSystem.x ^ 2) (RootSystem.s * RootSystem.r * RootSystem.s)) = rootMatrix 11 1
  rw [rightConj_mul]
  rw [matrix_conj_s]
  change sigma * matrixHom (RootSystem.rootBase 10) * sigma = rootMatrix 11 1
  rw [base_alignment_10, baseLeft11_eq, baseRight11_eq]

theorem rootBase_alignment (i : Fin 12) :
    matrixHom (RootSystem.rootBase i) = rootMatrix i 1 := by
  fin_cases i
  · exact base_alignment_0
  · exact base_alignment_1
  · exact base_alignment_2
  · exact base_alignment_3
  · exact base_alignment_4
  · exact base_alignment_5
  · exact base_alignment_6
  · exact base_alignment_7
  · exact base_alignment_8
  · exact base_alignment_9
  · exact base_alignment_10
  · exact base_alignment_11

def diagonalConj (d : Fin 26 → F8) (m : Mat) : Mat :=
  fun i j => (d i)⁻¹ * m i j * d j

theorem matrix_conj_torus (g : RootSystem.G) (a b : Fin 7) :
    matrixHom (rightConj g (RootSystem.torus a b)) =
      diagonalConj (torusDiag a b) (matrixHom g) := by
  ext i j
  change (Matrix.diagonal (fun k => (torusDiag a b k)⁻¹) * matrixHom g *
    Matrix.diagonal (torusDiag a b)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

def transported (i : Fin 12) (a : Fin 8) : Mat :=
  if a = 0 then 1 else
    diagonalConj (torusDiag (RootSystem.sectionParameters i a).1
      (RootSystem.sectionParameters i a).2) (rootMatrix i 1)

theorem curve_equation_0 : rootMatrix 0 = transported 0 := by decide +kernel

theorem curve_equation_1 : rootMatrix 1 = transported 1 := by decide +kernel

theorem curve_equation_2 : rootMatrix 2 = transported 2 := by decide +kernel

theorem curve_equation_3 : rootMatrix 3 = transported 3 := by decide +kernel

theorem curve_equation_4 : rootMatrix 4 = transported 4 := by decide +kernel

theorem curve_equation_5 : rootMatrix 5 = transported 5 := by decide +kernel

theorem curve_equation_6 : rootMatrix 6 = transported 6 := by decide +kernel

theorem curve_equation_7 : rootMatrix 7 = transported 7 := by decide +kernel

theorem curve_equation_8 : rootMatrix 8 = transported 8 := by decide +kernel

theorem curve_equation_9 : rootMatrix 9 = transported 9 := by decide +kernel

theorem curve_equation_10 : rootMatrix 10 = transported 10 := by decide +kernel

theorem curve_equation_11 : rootMatrix 11 = transported 11 := by decide +kernel

theorem curve_equation (i : Fin 12) : rootMatrix i = transported i := by
  fin_cases i
  · exact curve_equation_0
  · exact curve_equation_1
  · exact curve_equation_2
  · exact curve_equation_3
  · exact curve_equation_4
  · exact curve_equation_5
  · exact curve_equation_6
  · exact curve_equation_7
  · exact curve_equation_8
  · exact curve_equation_9
  · exact curve_equation_10
  · exact curve_equation_11

/-- All 96 arithmetic tables are identified with actual root elements of the
concrete ambient subgroup; no root-matrix equality is assumed. -/
theorem root_alignment (i : Fin 12) (a : Fin 8) :
    ((RootSystem.root i a).val : Mat) = rootMatrix i a := by
  change matrixHom (RootSystem.root i a) = rootMatrix i a
  rw [congrFun (curve_equation i) a]
  by_cases ha : a = 0
  · subst a
    simp [RootSystem.root_zero, transported]
  · rw [RootSystem.root, if_neg ha, matrix_conj_torus, rootBase_alignment]
    simp only [transported, if_neg ha]

end Kourovka.Problem2153.WilsonModel.RootData
