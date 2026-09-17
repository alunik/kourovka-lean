import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(1, e1), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(10, e1)],
    [(2, e1), (16, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(7, e1)],
    [(0, e1), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e1), (13, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(6, e1)],
    [(3, e1), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(4, e1), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p0_8q : Mat := Sparse.eval p0_8qRows
private def p0_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(2, e1), (4, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(7, e1), (11, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(9, e1)],
    [(10, e1), (17, e1)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(15, e1)],
    [(16, e1), (20, e1)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(22, e1), (24, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p0_8r : Mat := Sparse.eval p0_8rRows
private def p0_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(2, e1), (4, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(6, e1)],
    [(7, e1), (11, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(9, e1)],
    [(10, e1), (17, e1)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (14, e1), (18, e1), (20, e1)],
    [(15, e1)],
    [(2, e1), (4, e1), (16, e1), (20, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (9, e1), (11, e1), (21, e1), (23, e1), (24, e1)],
    [(2, e1), (4, e1), (7, e1), (11, e1), (22, e1), (24, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p0_8p : Mat := Sparse.eval p0_8pRows
private theorem p0_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 1) = p0_8q := by decide +kernel
private theorem p0_8r_check : Sparse.mulEval (p0_8qRows) (WeylData.matrix 8) = p0_8r := by decide +kernel
private theorem p0_8p_check : Sparse.mulEval (rootRows 11 1) (p0_8r) = p0_8p := by decide +kernel
private theorem p0_8_alignment : matrixHom (classProduct 0 8) = p0_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 1 * WeylData.matrix 8) = p0_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p0_8q_check]
  rw [show p0_8q * WeylData.matrix 8 = p0_8r from Sparse.mul_eq_of_check p0_8qRows _ _ p0_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_8p_check
private def p0_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p0_8pow2 : Mat := Sparse.eval p0_8pow2Rows
private theorem p0_8pow2_check : p0_8p * p0_8p = p0_8pow2 := by
  apply Sparse.mul_eq_of_check p0_8pRows
  decide +kernel
private theorem p0_8pow2_eq : p0_8p ^ 2 = p0_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p0_8pow2_check
theorem product_power_0_8 : classProduct 0 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_8_alignment, map_one]
  rw [p0_8pow2_eq]
  decide +kernel

private def p1_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(1, e2), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(10, e1)],
    [(2, e2), (16, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)],
    [(7, e1)],
    [(0, e6), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e2), (13, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(6, e1)],
    [(3, e2), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(4, e2), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p1_8q : Mat := Sparse.eval p1_8qRows
private def p1_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e2), (4, e6)],
    [(2, e1), (4, e2)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e2), (11, e6)],
    [(6, e1)],
    [(7, e1), (11, e2)],
    [(8, e1), (12, e2), (15, e6), (17, e4)],
    [(9, e1)],
    [(10, e1), (17, e6)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e2)],
    [(14, e1), (18, e2), (20, e6)],
    [(15, e1)],
    [(16, e1), (20, e2)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e2), (24, e6)],
    [(22, e1), (24, e2)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p1_8r : Mat := Sparse.eval p1_8rRows
private def p1_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e2), (4, e6)],
    [(2, e1), (4, e2)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e2), (11, e6)],
    [(6, e1)],
    [(7, e1), (11, e2)],
    [(8, e1), (12, e2), (15, e6), (17, e4)],
    [(9, e1)],
    [(10, e1), (17, e6)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e2)],
    [(1, e1), (3, e2), (4, e6), (14, e1), (18, e2), (20, e6)],
    [(15, e1)],
    [(2, e1), (4, e2), (16, e1), (20, e2)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e2), (4, e6), (5, e1), (9, e2), (11, e6), (21, e1), (23, e2), (24, e6)],
    [(2, e1), (4, e2), (7, e1), (11, e2), (22, e1), (24, e2)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p1_8p : Mat := Sparse.eval p1_8pRows
private theorem p1_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 2) = p1_8q := by decide +kernel
private theorem p1_8r_check : Sparse.mulEval (p1_8qRows) (WeylData.matrix 8) = p1_8r := by decide +kernel
private theorem p1_8p_check : Sparse.mulEval (rootRows 11 1) (p1_8r) = p1_8p := by decide +kernel
private theorem p1_8_alignment : matrixHom (classProduct 1 8) = p1_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 2 * WeylData.matrix 8) = p1_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p1_8q_check]
  rw [show p1_8q * WeylData.matrix 8 = p1_8r from Sparse.mul_eq_of_check p1_8qRows _ _ p1_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_8p_check
private def p1_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p1_8pow2 : Mat := Sparse.eval p1_8pow2Rows
private theorem p1_8pow2_check : p1_8p * p1_8p = p1_8pow2 := by
  apply Sparse.mul_eq_of_check p1_8pRows
  decide +kernel
private theorem p1_8pow2_eq : p1_8p ^ 2 = p1_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_8pow2_check
theorem product_power_1_8 : classProduct 1 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_8_alignment, map_one]
  rw [p1_8pow2_eq]
  decide +kernel

private def p2_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(1, e3), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(10, e1)],
    [(2, e3), (16, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)],
    [(7, e1)],
    [(0, e7), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e3), (13, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(6, e1)],
    [(3, e3), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(4, e3), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p2_8q : Mat := Sparse.eval p2_8qRows
private def p2_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e3), (4, e7)],
    [(2, e1), (4, e3)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e3), (11, e7)],
    [(6, e1)],
    [(7, e1), (11, e3)],
    [(8, e1), (12, e3), (15, e7), (17, e5)],
    [(9, e1)],
    [(10, e1), (17, e7)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e3)],
    [(14, e1), (18, e3), (20, e7)],
    [(15, e1)],
    [(16, e1), (20, e3)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e3), (24, e7)],
    [(22, e1), (24, e3)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p2_8r : Mat := Sparse.eval p2_8rRows
private def p2_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e3), (4, e7)],
    [(2, e1), (4, e3)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e3), (11, e7)],
    [(6, e1)],
    [(7, e1), (11, e3)],
    [(8, e1), (12, e3), (15, e7), (17, e5)],
    [(9, e1)],
    [(10, e1), (17, e7)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e3)],
    [(1, e1), (3, e3), (4, e7), (14, e1), (18, e3), (20, e7)],
    [(15, e1)],
    [(2, e1), (4, e3), (16, e1), (20, e3)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e3), (4, e7), (5, e1), (9, e3), (11, e7), (21, e1), (23, e3), (24, e7)],
    [(2, e1), (4, e3), (7, e1), (11, e3), (22, e1), (24, e3)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p2_8p : Mat := Sparse.eval p2_8pRows
private theorem p2_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 3) = p2_8q := by decide +kernel
private theorem p2_8r_check : Sparse.mulEval (p2_8qRows) (WeylData.matrix 8) = p2_8r := by decide +kernel
private theorem p2_8p_check : Sparse.mulEval (rootRows 11 1) (p2_8r) = p2_8p := by decide +kernel
private theorem p2_8_alignment : matrixHom (classProduct 2 8) = p2_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 3 * WeylData.matrix 8) = p2_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p2_8q_check]
  rw [show p2_8q * WeylData.matrix 8 = p2_8r from Sparse.mul_eq_of_check p2_8qRows _ _ p2_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_8p_check
private def p2_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p2_8pow2 : Mat := Sparse.eval p2_8pow2Rows
private theorem p2_8pow2_check : p2_8p * p2_8p = p2_8pow2 := by
  apply Sparse.mul_eq_of_check p2_8pRows
  decide +kernel
private theorem p2_8pow2_eq : p2_8p ^ 2 = p2_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_8pow2_check
theorem product_power_2_8 : classProduct 2 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_8_alignment, map_one]
  rw [p2_8pow2_eq]
  decide +kernel

private def p3_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(1, e4), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(10, e1)],
    [(2, e4), (16, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)],
    [(7, e1)],
    [(0, e2), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e4), (13, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(6, e1)],
    [(3, e4), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(4, e4), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p3_8q : Mat := Sparse.eval p3_8qRows
private def p3_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e4), (4, e2)],
    [(2, e1), (4, e4)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e4), (11, e2)],
    [(6, e1)],
    [(7, e1), (11, e4)],
    [(8, e1), (12, e4), (15, e2), (17, e6)],
    [(9, e1)],
    [(10, e1), (17, e2)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e4)],
    [(14, e1), (18, e4), (20, e2)],
    [(15, e1)],
    [(16, e1), (20, e4)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e4), (24, e2)],
    [(22, e1), (24, e4)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p3_8r : Mat := Sparse.eval p3_8rRows
private def p3_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e4), (4, e2)],
    [(2, e1), (4, e4)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e4), (11, e2)],
    [(6, e1)],
    [(7, e1), (11, e4)],
    [(8, e1), (12, e4), (15, e2), (17, e6)],
    [(9, e1)],
    [(10, e1), (17, e2)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e4)],
    [(1, e1), (3, e4), (4, e2), (14, e1), (18, e4), (20, e2)],
    [(15, e1)],
    [(2, e1), (4, e4), (16, e1), (20, e4)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e4), (4, e2), (5, e1), (9, e4), (11, e2), (21, e1), (23, e4), (24, e2)],
    [(2, e1), (4, e4), (7, e1), (11, e4), (22, e1), (24, e4)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p3_8p : Mat := Sparse.eval p3_8pRows
private theorem p3_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 4) = p3_8q := by decide +kernel
private theorem p3_8r_check : Sparse.mulEval (p3_8qRows) (WeylData.matrix 8) = p3_8r := by decide +kernel
private theorem p3_8p_check : Sparse.mulEval (rootRows 11 1) (p3_8r) = p3_8p := by decide +kernel
private theorem p3_8_alignment : matrixHom (classProduct 3 8) = p3_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 4 * WeylData.matrix 8) = p3_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p3_8q_check]
  rw [show p3_8q * WeylData.matrix 8 = p3_8r from Sparse.mul_eq_of_check p3_8qRows _ _ p3_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_8p_check
private def p3_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p3_8pow2 : Mat := Sparse.eval p3_8pow2Rows
private theorem p3_8pow2_check : p3_8p * p3_8p = p3_8pow2 := by
  apply Sparse.mul_eq_of_check p3_8pRows
  decide +kernel
private theorem p3_8pow2_eq : p3_8p ^ 2 = p3_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_8pow2_check
theorem product_power_3_8 : classProduct 3 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_8_alignment, map_one]
  rw [p3_8pow2_eq]
  decide +kernel

private def p4_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(1, e5), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(10, e1)],
    [(2, e5), (16, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)],
    [(7, e1)],
    [(0, e3), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e5), (13, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(6, e1)],
    [(3, e5), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(4, e5), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p4_8q : Mat := Sparse.eval p4_8qRows
private def p4_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e5), (4, e3)],
    [(2, e1), (4, e5)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e5), (11, e3)],
    [(6, e1)],
    [(7, e1), (11, e5)],
    [(8, e1), (12, e5), (15, e3), (17, e7)],
    [(9, e1)],
    [(10, e1), (17, e3)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e5)],
    [(14, e1), (18, e5), (20, e3)],
    [(15, e1)],
    [(16, e1), (20, e5)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e5), (24, e3)],
    [(22, e1), (24, e5)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p4_8r : Mat := Sparse.eval p4_8rRows
private def p4_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e5), (4, e3)],
    [(2, e1), (4, e5)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e5), (11, e3)],
    [(6, e1)],
    [(7, e1), (11, e5)],
    [(8, e1), (12, e5), (15, e3), (17, e7)],
    [(9, e1)],
    [(10, e1), (17, e3)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e5)],
    [(1, e1), (3, e5), (4, e3), (14, e1), (18, e5), (20, e3)],
    [(15, e1)],
    [(2, e1), (4, e5), (16, e1), (20, e5)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e5), (4, e3), (5, e1), (9, e5), (11, e3), (21, e1), (23, e5), (24, e3)],
    [(2, e1), (4, e5), (7, e1), (11, e5), (22, e1), (24, e5)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p4_8p : Mat := Sparse.eval p4_8pRows
private theorem p4_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 5) = p4_8q := by decide +kernel
private theorem p4_8r_check : Sparse.mulEval (p4_8qRows) (WeylData.matrix 8) = p4_8r := by decide +kernel
private theorem p4_8p_check : Sparse.mulEval (rootRows 11 1) (p4_8r) = p4_8p := by decide +kernel
private theorem p4_8_alignment : matrixHom (classProduct 4 8) = p4_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 5 * WeylData.matrix 8) = p4_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p4_8q_check]
  rw [show p4_8q * WeylData.matrix 8 = p4_8r from Sparse.mul_eq_of_check p4_8qRows _ _ p4_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_8p_check
private def p4_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p4_8pow2 : Mat := Sparse.eval p4_8pow2Rows
private theorem p4_8pow2_check : p4_8p * p4_8p = p4_8pow2 := by
  apply Sparse.mul_eq_of_check p4_8pRows
  decide +kernel
private theorem p4_8pow2_eq : p4_8p ^ 2 = p4_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_8pow2_check
theorem product_power_4_8 : classProduct 4 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_8_alignment, map_one]
  rw [p4_8pow2_eq]
  decide +kernel

private def p5_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(1, e6), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(10, e1)],
    [(2, e6), (16, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)],
    [(7, e1)],
    [(0, e4), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e6), (13, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(6, e1)],
    [(3, e6), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(4, e6), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p5_8q : Mat := Sparse.eval p5_8qRows
private def p5_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e6), (4, e4)],
    [(2, e1), (4, e6)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e6), (11, e4)],
    [(6, e1)],
    [(7, e1), (11, e6)],
    [(8, e1), (12, e6), (15, e4), (17, e2)],
    [(9, e1)],
    [(10, e1), (17, e4)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e6)],
    [(14, e1), (18, e6), (20, e4)],
    [(15, e1)],
    [(16, e1), (20, e6)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e6), (24, e4)],
    [(22, e1), (24, e6)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p5_8r : Mat := Sparse.eval p5_8rRows
private def p5_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e6), (4, e4)],
    [(2, e1), (4, e6)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e6), (11, e4)],
    [(6, e1)],
    [(7, e1), (11, e6)],
    [(8, e1), (12, e6), (15, e4), (17, e2)],
    [(9, e1)],
    [(10, e1), (17, e4)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e6)],
    [(1, e1), (3, e6), (4, e4), (14, e1), (18, e6), (20, e4)],
    [(15, e1)],
    [(2, e1), (4, e6), (16, e1), (20, e6)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e6), (4, e4), (5, e1), (9, e6), (11, e4), (21, e1), (23, e6), (24, e4)],
    [(2, e1), (4, e6), (7, e1), (11, e6), (22, e1), (24, e6)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p5_8p : Mat := Sparse.eval p5_8pRows
private theorem p5_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 6) = p5_8q := by decide +kernel
private theorem p5_8r_check : Sparse.mulEval (p5_8qRows) (WeylData.matrix 8) = p5_8r := by decide +kernel
private theorem p5_8p_check : Sparse.mulEval (rootRows 11 1) (p5_8r) = p5_8p := by decide +kernel
private theorem p5_8_alignment : matrixHom (classProduct 5 8) = p5_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 6 * WeylData.matrix 8) = p5_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p5_8q_check]
  rw [show p5_8q * WeylData.matrix 8 = p5_8r from Sparse.mul_eq_of_check p5_8qRows _ _ p5_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_8p_check
private def p5_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p5_8pow2 : Mat := Sparse.eval p5_8pow2Rows
private theorem p5_8pow2_check : p5_8p * p5_8p = p5_8pow2 := by
  apply Sparse.mul_eq_of_check p5_8pRows
  decide +kernel
private theorem p5_8pow2_eq : p5_8p ^ 2 = p5_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_8pow2_check
theorem product_power_5_8 : classProduct 5 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_8_alignment, map_one]
  rw [p5_8pow2_eq]
  decide +kernel

private def p6_8qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(1, e7), (14, e1)],
    [(5, e1)],
    [(1, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(10, e1)],
    [(2, e7), (16, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)],
    [(7, e1)],
    [(0, e5), (19, e1)],
    [(2, e1)],
    [(12, e1)],
    [(0, e7), (13, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(6, e1)],
    [(3, e7), (18, e1)],
    [(0, e1)],
    [(9, e1)],
    [(15, e1)],
    [(3, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(4, e7), (20, e1)],
    [(11, e1)],
    [(4, e1)],
    [(17, e1)]]
private def p6_8q : Mat := Sparse.eval p6_8qRows
private def p6_8rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e7), (4, e5)],
    [(2, e1), (4, e7)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e7), (11, e5)],
    [(6, e1)],
    [(7, e1), (11, e7)],
    [(8, e1), (12, e7), (15, e5), (17, e3)],
    [(9, e1)],
    [(10, e1), (17, e5)],
    [(11, e1)],
    [(12, e1)],
    [(13, e1), (17, e7)],
    [(14, e1), (18, e7), (20, e5)],
    [(15, e1)],
    [(16, e1), (20, e7)],
    [(17, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1)],
    [(21, e1), (23, e7), (24, e5)],
    [(22, e1), (24, e7)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p6_8r : Mat := Sparse.eval p6_8rRows
private def p6_8pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1), (3, e7), (4, e5)],
    [(2, e1), (4, e7)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1), (9, e7), (11, e5)],
    [(6, e1)],
    [(7, e1), (11, e7)],
    [(8, e1), (12, e7), (15, e5), (17, e3)],
    [(9, e1)],
    [(10, e1), (17, e5)],
    [(11, e1)],
    [(12, e1)],
    [(0, e1), (13, e1), (17, e7)],
    [(1, e1), (3, e7), (4, e5), (14, e1), (18, e7), (20, e5)],
    [(15, e1)],
    [(2, e1), (4, e7), (16, e1), (20, e7)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e7), (4, e5), (5, e1), (9, e7), (11, e5), (21, e1), (23, e7), (24, e5)],
    [(2, e1), (4, e7), (7, e1), (11, e7), (22, e1), (24, e7)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p6_8p : Mat := Sparse.eval p6_8pRows
private theorem p6_8q_check : Sparse.mulEval (WeylData.rows (inverseIndex 8)) (rootMatrix 11 7) = p6_8q := by decide +kernel
private theorem p6_8r_check : Sparse.mulEval (p6_8qRows) (WeylData.matrix 8) = p6_8r := by decide +kernel
private theorem p6_8p_check : Sparse.mulEval (rootRows 11 1) (p6_8r) = p6_8p := by decide +kernel
private theorem p6_8_alignment : matrixHom (classProduct 6 8) = p6_8p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 8)) * rootMatrix 11 7 * WeylData.matrix 8) = p6_8p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 8)) _ _ p6_8q_check]
  rw [show p6_8q * WeylData.matrix 8 = p6_8r from Sparse.mul_eq_of_check p6_8qRows _ _ p6_8r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_8p_check
private def p6_8pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p6_8pow2 : Mat := Sparse.eval p6_8pow2Rows
private theorem p6_8pow2_check : p6_8p * p6_8p = p6_8pow2 := by
  apply Sparse.mul_eq_of_check p6_8pRows
  decide +kernel
private theorem p6_8pow2_eq : p6_8p ^ 2 = p6_8pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_8pow2_check
theorem product_power_6_8 : classProduct 6 8 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_8_alignment, map_one]
  rw [p6_8pow2_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
