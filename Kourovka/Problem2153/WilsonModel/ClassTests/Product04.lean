import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e1), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(6, e1)],
    [(2, e1), (16, e1)],
    [(3, e1)],
    [(0, e1), (12, e1), (13, e1)],
    [(0, e1), (13, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(9, e1)],
    [(0, e1), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e1), (18, e1)],
    [(11, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (20, e1)],
    [(17, e1)],
    [(4, e1), (11, e1), (24, e1)]]
private def p0_4q : Mat := Sparse.eval p0_4qRows
private def p0_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(4, e1), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e1), (19, e1)],
    [(20, e1)],
    [(4, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(11, e1), (15, e1), (22, e1)],
    [(17, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (25, e1)]]
private def p0_4r : Mat := Sparse.eval p0_4rRows
private def p0_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (12, e1)],
    [(0, e1), (4, e1), (13, e1)],
    [(1, e1), (3, e1), (6, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (4, e1), (5, e1), (9, e1), (12, e1), (13, e1), (21, e1)],
    [(2, e1), (7, e1), (11, e1), (15, e1), (22, e1)],
    [(3, e1), (9, e1), (17, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e1), (6, e1), (12, e1), (17, e1), (20, e1), (25, e1)]]
private def p0_4p : Mat := Sparse.eval p0_4pRows
private theorem p0_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 1) = p0_4q := by decide +kernel
private theorem p0_4r_check : Sparse.mulEval (p0_4qRows) (WeylData.matrix 4) = p0_4r := by decide +kernel
private theorem p0_4p_check : Sparse.mulEval (rootRows 11 1) (p0_4r) = p0_4p := by decide +kernel
private theorem p0_4_alignment : matrixHom (classProduct 0 4) = p0_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 1 * WeylData.matrix 4) = p0_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p0_4q_check]
  rw [show p0_4q * WeylData.matrix 4 = p0_4r from Sparse.mul_eq_of_check p0_4qRows _ _ p0_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_4p_check
private def p0_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p0_4pow2 : Mat := Sparse.eval p0_4pow2Rows
private theorem p0_4pow2_check : p0_4p * p0_4p = p0_4pow2 := by
  apply Sparse.mul_eq_of_check p0_4pRows
  decide +kernel
private theorem p0_4pow2_eq : p0_4p ^ 2 = p0_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p0_4pow2_check
theorem product_power_0_4 : classProduct 0 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_4_alignment, map_one]
  rw [p0_4pow2_eq]
  decide +kernel

private def p1_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e2), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(6, e1)],
    [(2, e2), (16, e1)],
    [(3, e1)],
    [(0, e2), (12, e1), (13, e1)],
    [(0, e2), (13, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(9, e1)],
    [(0, e6), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e2), (18, e1)],
    [(11, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(4, e2), (20, e1)],
    [(17, e1)],
    [(4, e6), (11, e2), (24, e1)]]
private def p1_4q : Mat := Sparse.eval p1_4qRows
private def p1_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e2), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e6), (2, e2), (8, e1)],
    [(9, e1)],
    [(3, e2), (10, e1)],
    [(11, e1)],
    [(4, e2), (12, e1)],
    [(4, e2), (13, e1)],
    [(3, e6), (6, e2), (14, e1)],
    [(15, e1)],
    [(4, e6), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e2), (19, e1)],
    [(20, e1)],
    [(4, e4), (9, e6), (12, e2), (13, e2), (21, e1)],
    [(11, e6), (15, e2), (22, e1)],
    [(17, e2), (23, e1)],
    [(24, e1)],
    [(17, e6), (20, e2), (25, e1)]]
private def p1_4r : Mat := Sparse.eval p1_4rRows
private def p1_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e2), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e6), (2, e2), (8, e1)],
    [(9, e1)],
    [(3, e2), (10, e1)],
    [(11, e1)],
    [(4, e2), (12, e1)],
    [(0, e1), (4, e2), (13, e1)],
    [(1, e1), (3, e6), (6, e2), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e6), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e2), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e2), (1, e1), (4, e4), (5, e1), (9, e6), (12, e2), (13, e2), (21, e1)],
    [(2, e1), (7, e1), (11, e6), (15, e2), (22, e1)],
    [(3, e1), (9, e1), (17, e2), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e2), (6, e1), (12, e1), (17, e6), (20, e2), (25, e1)]]
private def p1_4p : Mat := Sparse.eval p1_4pRows
private theorem p1_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 2) = p1_4q := by decide +kernel
private theorem p1_4r_check : Sparse.mulEval (p1_4qRows) (WeylData.matrix 4) = p1_4r := by decide +kernel
private theorem p1_4p_check : Sparse.mulEval (rootRows 11 1) (p1_4r) = p1_4p := by decide +kernel
private theorem p1_4_alignment : matrixHom (classProduct 1 4) = p1_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 2 * WeylData.matrix 4) = p1_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p1_4q_check]
  rw [show p1_4q * WeylData.matrix 4 = p1_4r from Sparse.mul_eq_of_check p1_4qRows _ _ p1_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_4p_check
private def p1_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p1_4pow2 : Mat := Sparse.eval p1_4pow2Rows
private theorem p1_4pow2_check : p1_4p * p1_4p = p1_4pow2 := by
  apply Sparse.mul_eq_of_check p1_4pRows
  decide +kernel
private theorem p1_4pow2_eq : p1_4p ^ 2 = p1_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_4pow2_check
theorem product_power_1_4 : classProduct 1 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_4_alignment, map_one]
  rw [p1_4pow2_eq]
  decide +kernel

private def p2_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e3), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(6, e1)],
    [(2, e3), (16, e1)],
    [(3, e1)],
    [(0, e3), (12, e1), (13, e1)],
    [(0, e3), (13, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(9, e1)],
    [(0, e7), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e3), (18, e1)],
    [(11, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(4, e3), (20, e1)],
    [(17, e1)],
    [(4, e7), (11, e3), (24, e1)]]
private def p2_4q : Mat := Sparse.eval p2_4qRows
private def p2_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e3), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e7), (2, e3), (8, e1)],
    [(9, e1)],
    [(3, e3), (10, e1)],
    [(11, e1)],
    [(4, e3), (12, e1)],
    [(4, e3), (13, e1)],
    [(3, e7), (6, e3), (14, e1)],
    [(15, e1)],
    [(4, e7), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e3), (19, e1)],
    [(20, e1)],
    [(4, e5), (9, e7), (12, e3), (13, e3), (21, e1)],
    [(11, e7), (15, e3), (22, e1)],
    [(17, e3), (23, e1)],
    [(24, e1)],
    [(17, e7), (20, e3), (25, e1)]]
private def p2_4r : Mat := Sparse.eval p2_4rRows
private def p2_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e3), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e7), (2, e3), (8, e1)],
    [(9, e1)],
    [(3, e3), (10, e1)],
    [(11, e1)],
    [(4, e3), (12, e1)],
    [(0, e1), (4, e3), (13, e1)],
    [(1, e1), (3, e7), (6, e3), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e7), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e3), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e3), (1, e1), (4, e5), (5, e1), (9, e7), (12, e3), (13, e3), (21, e1)],
    [(2, e1), (7, e1), (11, e7), (15, e3), (22, e1)],
    [(3, e1), (9, e1), (17, e3), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e3), (6, e1), (12, e1), (17, e7), (20, e3), (25, e1)]]
private def p2_4p : Mat := Sparse.eval p2_4pRows
private theorem p2_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 3) = p2_4q := by decide +kernel
private theorem p2_4r_check : Sparse.mulEval (p2_4qRows) (WeylData.matrix 4) = p2_4r := by decide +kernel
private theorem p2_4p_check : Sparse.mulEval (rootRows 11 1) (p2_4r) = p2_4p := by decide +kernel
private theorem p2_4_alignment : matrixHom (classProduct 2 4) = p2_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 3 * WeylData.matrix 4) = p2_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p2_4q_check]
  rw [show p2_4q * WeylData.matrix 4 = p2_4r from Sparse.mul_eq_of_check p2_4qRows _ _ p2_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_4p_check
private def p2_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p2_4pow2 : Mat := Sparse.eval p2_4pow2Rows
private theorem p2_4pow2_check : p2_4p * p2_4p = p2_4pow2 := by
  apply Sparse.mul_eq_of_check p2_4pRows
  decide +kernel
private theorem p2_4pow2_eq : p2_4p ^ 2 = p2_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_4pow2_check
theorem product_power_2_4 : classProduct 2 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_4_alignment, map_one]
  rw [p2_4pow2_eq]
  decide +kernel

private def p3_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e4), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(6, e1)],
    [(2, e4), (16, e1)],
    [(3, e1)],
    [(0, e4), (12, e1), (13, e1)],
    [(0, e4), (13, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(9, e1)],
    [(0, e2), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e4), (18, e1)],
    [(11, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(4, e4), (20, e1)],
    [(17, e1)],
    [(4, e2), (11, e4), (24, e1)]]
private def p3_4q : Mat := Sparse.eval p3_4qRows
private def p3_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e4), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e2), (2, e4), (8, e1)],
    [(9, e1)],
    [(3, e4), (10, e1)],
    [(11, e1)],
    [(4, e4), (12, e1)],
    [(4, e4), (13, e1)],
    [(3, e2), (6, e4), (14, e1)],
    [(15, e1)],
    [(4, e2), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e4), (19, e1)],
    [(20, e1)],
    [(4, e6), (9, e2), (12, e4), (13, e4), (21, e1)],
    [(11, e2), (15, e4), (22, e1)],
    [(17, e4), (23, e1)],
    [(24, e1)],
    [(17, e2), (20, e4), (25, e1)]]
private def p3_4r : Mat := Sparse.eval p3_4rRows
private def p3_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e4), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e2), (2, e4), (8, e1)],
    [(9, e1)],
    [(3, e4), (10, e1)],
    [(11, e1)],
    [(4, e4), (12, e1)],
    [(0, e1), (4, e4), (13, e1)],
    [(1, e1), (3, e2), (6, e4), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e2), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e4), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e4), (1, e1), (4, e6), (5, e1), (9, e2), (12, e4), (13, e4), (21, e1)],
    [(2, e1), (7, e1), (11, e2), (15, e4), (22, e1)],
    [(3, e1), (9, e1), (17, e4), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e4), (6, e1), (12, e1), (17, e2), (20, e4), (25, e1)]]
private def p3_4p : Mat := Sparse.eval p3_4pRows
private theorem p3_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 4) = p3_4q := by decide +kernel
private theorem p3_4r_check : Sparse.mulEval (p3_4qRows) (WeylData.matrix 4) = p3_4r := by decide +kernel
private theorem p3_4p_check : Sparse.mulEval (rootRows 11 1) (p3_4r) = p3_4p := by decide +kernel
private theorem p3_4_alignment : matrixHom (classProduct 3 4) = p3_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 4 * WeylData.matrix 4) = p3_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p3_4q_check]
  rw [show p3_4q * WeylData.matrix 4 = p3_4r from Sparse.mul_eq_of_check p3_4qRows _ _ p3_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_4p_check
private def p3_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p3_4pow2 : Mat := Sparse.eval p3_4pow2Rows
private theorem p3_4pow2_check : p3_4p * p3_4p = p3_4pow2 := by
  apply Sparse.mul_eq_of_check p3_4pRows
  decide +kernel
private theorem p3_4pow2_eq : p3_4p ^ 2 = p3_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_4pow2_check
theorem product_power_3_4 : classProduct 3 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_4_alignment, map_one]
  rw [p3_4pow2_eq]
  decide +kernel

private def p4_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e5), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(6, e1)],
    [(2, e5), (16, e1)],
    [(3, e1)],
    [(0, e5), (12, e1), (13, e1)],
    [(0, e5), (13, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(9, e1)],
    [(0, e3), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e5), (18, e1)],
    [(11, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(4, e5), (20, e1)],
    [(17, e1)],
    [(4, e3), (11, e5), (24, e1)]]
private def p4_4q : Mat := Sparse.eval p4_4qRows
private def p4_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e5), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e3), (2, e5), (8, e1)],
    [(9, e1)],
    [(3, e5), (10, e1)],
    [(11, e1)],
    [(4, e5), (12, e1)],
    [(4, e5), (13, e1)],
    [(3, e3), (6, e5), (14, e1)],
    [(15, e1)],
    [(4, e3), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e5), (19, e1)],
    [(20, e1)],
    [(4, e7), (9, e3), (12, e5), (13, e5), (21, e1)],
    [(11, e3), (15, e5), (22, e1)],
    [(17, e5), (23, e1)],
    [(24, e1)],
    [(17, e3), (20, e5), (25, e1)]]
private def p4_4r : Mat := Sparse.eval p4_4rRows
private def p4_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e5), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e3), (2, e5), (8, e1)],
    [(9, e1)],
    [(3, e5), (10, e1)],
    [(11, e1)],
    [(4, e5), (12, e1)],
    [(0, e1), (4, e5), (13, e1)],
    [(1, e1), (3, e3), (6, e5), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e3), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e5), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e5), (1, e1), (4, e7), (5, e1), (9, e3), (12, e5), (13, e5), (21, e1)],
    [(2, e1), (7, e1), (11, e3), (15, e5), (22, e1)],
    [(3, e1), (9, e1), (17, e5), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e5), (6, e1), (12, e1), (17, e3), (20, e5), (25, e1)]]
private def p4_4p : Mat := Sparse.eval p4_4pRows
private theorem p4_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 5) = p4_4q := by decide +kernel
private theorem p4_4r_check : Sparse.mulEval (p4_4qRows) (WeylData.matrix 4) = p4_4r := by decide +kernel
private theorem p4_4p_check : Sparse.mulEval (rootRows 11 1) (p4_4r) = p4_4p := by decide +kernel
private theorem p4_4_alignment : matrixHom (classProduct 4 4) = p4_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 5 * WeylData.matrix 4) = p4_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p4_4q_check]
  rw [show p4_4q * WeylData.matrix 4 = p4_4r from Sparse.mul_eq_of_check p4_4qRows _ _ p4_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_4p_check
private def p4_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p4_4pow2 : Mat := Sparse.eval p4_4pow2Rows
private theorem p4_4pow2_check : p4_4p * p4_4p = p4_4pow2 := by
  apply Sparse.mul_eq_of_check p4_4pRows
  decide +kernel
private theorem p4_4pow2_eq : p4_4p ^ 2 = p4_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_4pow2_check
theorem product_power_4_4 : classProduct 4 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_4_alignment, map_one]
  rw [p4_4pow2_eq]
  decide +kernel

private def p5_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e6), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(6, e1)],
    [(2, e6), (16, e1)],
    [(3, e1)],
    [(0, e6), (12, e1), (13, e1)],
    [(0, e6), (13, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(9, e1)],
    [(0, e4), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e6), (18, e1)],
    [(11, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(4, e6), (20, e1)],
    [(17, e1)],
    [(4, e4), (11, e6), (24, e1)]]
private def p5_4q : Mat := Sparse.eval p5_4qRows
private def p5_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e6), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e4), (2, e6), (8, e1)],
    [(9, e1)],
    [(3, e6), (10, e1)],
    [(11, e1)],
    [(4, e6), (12, e1)],
    [(4, e6), (13, e1)],
    [(3, e4), (6, e6), (14, e1)],
    [(15, e1)],
    [(4, e4), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e6), (19, e1)],
    [(20, e1)],
    [(4, e2), (9, e4), (12, e6), (13, e6), (21, e1)],
    [(11, e4), (15, e6), (22, e1)],
    [(17, e6), (23, e1)],
    [(24, e1)],
    [(17, e4), (20, e6), (25, e1)]]
private def p5_4r : Mat := Sparse.eval p5_4rRows
private def p5_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e6), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e4), (2, e6), (8, e1)],
    [(9, e1)],
    [(3, e6), (10, e1)],
    [(11, e1)],
    [(4, e6), (12, e1)],
    [(0, e1), (4, e6), (13, e1)],
    [(1, e1), (3, e4), (6, e6), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e4), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e6), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e6), (1, e1), (4, e2), (5, e1), (9, e4), (12, e6), (13, e6), (21, e1)],
    [(2, e1), (7, e1), (11, e4), (15, e6), (22, e1)],
    [(3, e1), (9, e1), (17, e6), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e6), (6, e1), (12, e1), (17, e4), (20, e6), (25, e1)]]
private def p5_4p : Mat := Sparse.eval p5_4pRows
private theorem p5_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 6) = p5_4q := by decide +kernel
private theorem p5_4r_check : Sparse.mulEval (p5_4qRows) (WeylData.matrix 4) = p5_4r := by decide +kernel
private theorem p5_4p_check : Sparse.mulEval (rootRows 11 1) (p5_4r) = p5_4p := by decide +kernel
private theorem p5_4_alignment : matrixHom (classProduct 5 4) = p5_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 6 * WeylData.matrix 4) = p5_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p5_4q_check]
  rw [show p5_4q * WeylData.matrix 4 = p5_4r from Sparse.mul_eq_of_check p5_4qRows _ _ p5_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_4p_check
private def p5_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p5_4pow2 : Mat := Sparse.eval p5_4pow2Rows
private theorem p5_4pow2_check : p5_4p * p5_4p = p5_4pow2 := by
  apply Sparse.mul_eq_of_check p5_4pRows
  decide +kernel
private theorem p5_4pow2_eq : p5_4p ^ 2 = p5_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_4pow2_check
theorem product_power_5_4 : classProduct 5 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_4_alignment, map_one]
  rw [p5_4pow2_eq]
  decide +kernel

private def p6_4qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
    [(8, e1)],
    [(5, e1)],
    [(2, e1)],
    [(0, e1)],
    [(1, e7), (14, e1)],
    [(7, e1)],
    [(10, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(6, e1)],
    [(2, e7), (16, e1)],
    [(3, e1)],
    [(0, e7), (12, e1), (13, e1)],
    [(0, e7), (13, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(9, e1)],
    [(0, e5), (19, e1)],
    [(4, e1)],
    [(15, e1)],
    [(3, e7), (18, e1)],
    [(11, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e7), (20, e1)],
    [(17, e1)],
    [(4, e5), (11, e7), (24, e1)]]
private def p6_4q : Mat := Sparse.eval p6_4qRows
private def p6_4rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e7), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e5), (2, e7), (8, e1)],
    [(9, e1)],
    [(3, e7), (10, e1)],
    [(11, e1)],
    [(4, e7), (12, e1)],
    [(4, e7), (13, e1)],
    [(3, e5), (6, e7), (14, e1)],
    [(15, e1)],
    [(4, e5), (16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(11, e7), (19, e1)],
    [(20, e1)],
    [(4, e3), (9, e5), (12, e7), (13, e7), (21, e1)],
    [(11, e5), (15, e7), (22, e1)],
    [(17, e7), (23, e1)],
    [(24, e1)],
    [(17, e5), (20, e7), (25, e1)]]
private def p6_4r : Mat := Sparse.eval p6_4rRows
private def p6_4pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e7), (5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(0, e5), (2, e7), (8, e1)],
    [(9, e1)],
    [(3, e7), (10, e1)],
    [(11, e1)],
    [(4, e7), (12, e1)],
    [(0, e1), (4, e7), (13, e1)],
    [(1, e1), (3, e5), (6, e7), (14, e1)],
    [(15, e1)],
    [(2, e1), (4, e5), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (11, e7), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e7), (1, e1), (4, e3), (5, e1), (9, e5), (12, e7), (13, e7), (21, e1)],
    [(2, e1), (7, e1), (11, e5), (15, e7), (22, e1)],
    [(3, e1), (9, e1), (17, e7), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (4, e7), (6, e1), (12, e1), (17, e5), (20, e7), (25, e1)]]
private def p6_4p : Mat := Sparse.eval p6_4pRows
private theorem p6_4q_check : Sparse.mulEval (WeylData.rows (inverseIndex 4)) (rootMatrix 11 7) = p6_4q := by decide +kernel
private theorem p6_4r_check : Sparse.mulEval (p6_4qRows) (WeylData.matrix 4) = p6_4r := by decide +kernel
private theorem p6_4p_check : Sparse.mulEval (rootRows 11 1) (p6_4r) = p6_4p := by decide +kernel
private theorem p6_4_alignment : matrixHom (classProduct 6 4) = p6_4p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 4)) * rootMatrix 11 7 * WeylData.matrix 4) = p6_4p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 4)) _ _ p6_4q_check]
  rw [show p6_4q * WeylData.matrix 4 = p6_4r from Sparse.mul_eq_of_check p6_4qRows _ _ p6_4r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_4p_check
private def p6_4pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1)],
    [(10, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(15, e1)],
    [(16, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p6_4pow2 : Mat := Sparse.eval p6_4pow2Rows
private theorem p6_4pow2_check : p6_4p * p6_4p = p6_4pow2 := by
  apply Sparse.mul_eq_of_check p6_4pRows
  decide +kernel
private theorem p6_4pow2_eq : p6_4p ^ 2 = p6_4pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_4pow2_check
theorem product_power_6_4 : classProduct 6 4 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_4_alignment, map_one]
  rw [p6_4pow2_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
