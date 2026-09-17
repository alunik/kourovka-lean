import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e1), (14, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e1), (16, e1)],
    [(6, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(12, e1)],
    [(0, e1), (13, e1)],
    [(3, e1)],
    [(0, e1), (19, e1)],
    [(9, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(3, e1), (18, e1)],
    [(15, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e1), (20, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(17, e1)]]
private def p0_6q : Mat := Sparse.eval p0_6qRows
private def p0_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e1), (9, e1)],
    [(10, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(12, e1)],
    [(8, e1), (13, e1)],
    [(14, e1)],
    [(8, e1), (15, e1)],
    [(16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(14, e1), (18, e1)],
    [(19, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e1), (23, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(25, e1)]]
private def p0_6r : Mat := Sparse.eval p0_6rRows
private def p0_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e1), (9, e1)],
    [(10, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e1), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(1, e1), (3, e1), (14, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e1), (2, e1), (4, e1), (14, e1), (16, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e1), (3, e1), (5, e1), (9, e1), (21, e1), (23, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (7, e1), (11, e1), (21, e1), (22, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p0_6p : Mat := Sparse.eval p0_6pRows
private theorem p0_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 1) = p0_6q := by decide +kernel
private theorem p0_6r_check : Sparse.mulEval (p0_6qRows) (WeylData.matrix 6) = p0_6r := by decide +kernel
private theorem p0_6p_check : Sparse.mulEval (rootRows 11 1) (p0_6r) = p0_6p := by decide +kernel
private theorem p0_6_alignment : matrixHom (classProduct 0 6) = p0_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 1 * WeylData.matrix 6) = p0_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p0_6q_check]
  rw [show p0_6q * WeylData.matrix 6 = p0_6r from Sparse.mul_eq_of_check p0_6qRows _ _ p0_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_6p_check
private def p0_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p0_6pow2 : Mat := Sparse.eval p0_6pow2Rows
private theorem p0_6pow2_check : p0_6p * p0_6p = p0_6pow2 := by
  apply Sparse.mul_eq_of_check p0_6pRows
  decide +kernel
private theorem p0_6pow2_eq : p0_6p ^ 2 = p0_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p0_6pow2_check
theorem product_power_0_6 : classProduct 0 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_6_alignment, map_one]
  rw [p0_6pow2_eq]
  decide +kernel

private def p1_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e2), (14, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e2), (16, e1)],
    [(6, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(12, e1)],
    [(0, e2), (13, e1)],
    [(3, e1)],
    [(0, e6), (19, e1)],
    [(9, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)],
    [(3, e2), (18, e1)],
    [(15, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e2), (20, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(17, e1)]]
private def p1_6q : Mat := Sparse.eval p1_6qRows
private def p1_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e2), (3, e1)],
    [(1, e6), (2, e2), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e2), (9, e1)],
    [(10, e1)],
    [(5, e6), (7, e2), (11, e1)],
    [(12, e1)],
    [(8, e2), (13, e1)],
    [(14, e1)],
    [(8, e6), (15, e1)],
    [(16, e1)],
    [(8, e4), (10, e6), (12, e2), (17, e1)],
    [(14, e2), (18, e1)],
    [(19, e1)],
    [(14, e6), (16, e2), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e2), (23, e1)],
    [(21, e6), (22, e2), (24, e1)],
    [(25, e1)]]
private def p1_6r : Mat := Sparse.eval p1_6rRows
private def p1_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e2), (3, e1)],
    [(1, e6), (2, e2), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e2), (9, e1)],
    [(10, e1)],
    [(5, e6), (7, e2), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e2), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e6), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e4), (10, e6), (12, e2), (17, e1)],
    [(1, e2), (3, e1), (14, e2), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e6), (2, e2), (4, e1), (14, e6), (16, e2), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e2), (3, e1), (5, e2), (9, e1), (21, e2), (23, e1)],
    [(1, e6), (2, e2), (4, e1), (5, e6), (7, e2), (11, e1), (21, e6), (22, e2), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p1_6p : Mat := Sparse.eval p1_6pRows
private theorem p1_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 2) = p1_6q := by decide +kernel
private theorem p1_6r_check : Sparse.mulEval (p1_6qRows) (WeylData.matrix 6) = p1_6r := by decide +kernel
private theorem p1_6p_check : Sparse.mulEval (rootRows 11 1) (p1_6r) = p1_6p := by decide +kernel
private theorem p1_6_alignment : matrixHom (classProduct 1 6) = p1_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 2 * WeylData.matrix 6) = p1_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p1_6q_check]
  rw [show p1_6q * WeylData.matrix 6 = p1_6r from Sparse.mul_eq_of_check p1_6qRows _ _ p1_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_6p_check
private def p1_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p1_6pow2 : Mat := Sparse.eval p1_6pow2Rows
private theorem p1_6pow2_check : p1_6p * p1_6p = p1_6pow2 := by
  apply Sparse.mul_eq_of_check p1_6pRows
  decide +kernel
private theorem p1_6pow2_eq : p1_6p ^ 2 = p1_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_6pow2_check
theorem product_power_1_6 : classProduct 1 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_6_alignment, map_one]
  rw [p1_6pow2_eq]
  decide +kernel

private def p2_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e3), (14, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e3), (16, e1)],
    [(6, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(12, e1)],
    [(0, e3), (13, e1)],
    [(3, e1)],
    [(0, e7), (19, e1)],
    [(9, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)],
    [(3, e3), (18, e1)],
    [(15, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e3), (20, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(17, e1)]]
private def p2_6q : Mat := Sparse.eval p2_6qRows
private def p2_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e3), (3, e1)],
    [(1, e7), (2, e3), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e3), (9, e1)],
    [(10, e1)],
    [(5, e7), (7, e3), (11, e1)],
    [(12, e1)],
    [(8, e3), (13, e1)],
    [(14, e1)],
    [(8, e7), (15, e1)],
    [(16, e1)],
    [(8, e5), (10, e7), (12, e3), (17, e1)],
    [(14, e3), (18, e1)],
    [(19, e1)],
    [(14, e7), (16, e3), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e3), (23, e1)],
    [(21, e7), (22, e3), (24, e1)],
    [(25, e1)]]
private def p2_6r : Mat := Sparse.eval p2_6rRows
private def p2_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e3), (3, e1)],
    [(1, e7), (2, e3), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e3), (9, e1)],
    [(10, e1)],
    [(5, e7), (7, e3), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e3), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e7), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e5), (10, e7), (12, e3), (17, e1)],
    [(1, e3), (3, e1), (14, e3), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e7), (2, e3), (4, e1), (14, e7), (16, e3), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e3), (3, e1), (5, e3), (9, e1), (21, e3), (23, e1)],
    [(1, e7), (2, e3), (4, e1), (5, e7), (7, e3), (11, e1), (21, e7), (22, e3), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p2_6p : Mat := Sparse.eval p2_6pRows
private theorem p2_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 3) = p2_6q := by decide +kernel
private theorem p2_6r_check : Sparse.mulEval (p2_6qRows) (WeylData.matrix 6) = p2_6r := by decide +kernel
private theorem p2_6p_check : Sparse.mulEval (rootRows 11 1) (p2_6r) = p2_6p := by decide +kernel
private theorem p2_6_alignment : matrixHom (classProduct 2 6) = p2_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 3 * WeylData.matrix 6) = p2_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p2_6q_check]
  rw [show p2_6q * WeylData.matrix 6 = p2_6r from Sparse.mul_eq_of_check p2_6qRows _ _ p2_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_6p_check
private def p2_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p2_6pow2 : Mat := Sparse.eval p2_6pow2Rows
private theorem p2_6pow2_check : p2_6p * p2_6p = p2_6pow2 := by
  apply Sparse.mul_eq_of_check p2_6pRows
  decide +kernel
private theorem p2_6pow2_eq : p2_6p ^ 2 = p2_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_6pow2_check
theorem product_power_2_6 : classProduct 2 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_6_alignment, map_one]
  rw [p2_6pow2_eq]
  decide +kernel

private def p3_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e4), (14, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e4), (16, e1)],
    [(6, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(12, e1)],
    [(0, e4), (13, e1)],
    [(3, e1)],
    [(0, e2), (19, e1)],
    [(9, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)],
    [(3, e4), (18, e1)],
    [(15, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e4), (20, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(17, e1)]]
private def p3_6q : Mat := Sparse.eval p3_6qRows
private def p3_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e4), (3, e1)],
    [(1, e2), (2, e4), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e4), (9, e1)],
    [(10, e1)],
    [(5, e2), (7, e4), (11, e1)],
    [(12, e1)],
    [(8, e4), (13, e1)],
    [(14, e1)],
    [(8, e2), (15, e1)],
    [(16, e1)],
    [(8, e6), (10, e2), (12, e4), (17, e1)],
    [(14, e4), (18, e1)],
    [(19, e1)],
    [(14, e2), (16, e4), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e4), (23, e1)],
    [(21, e2), (22, e4), (24, e1)],
    [(25, e1)]]
private def p3_6r : Mat := Sparse.eval p3_6rRows
private def p3_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e4), (3, e1)],
    [(1, e2), (2, e4), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e4), (9, e1)],
    [(10, e1)],
    [(5, e2), (7, e4), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e4), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e2), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e6), (10, e2), (12, e4), (17, e1)],
    [(1, e4), (3, e1), (14, e4), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e2), (2, e4), (4, e1), (14, e2), (16, e4), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e4), (3, e1), (5, e4), (9, e1), (21, e4), (23, e1)],
    [(1, e2), (2, e4), (4, e1), (5, e2), (7, e4), (11, e1), (21, e2), (22, e4), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p3_6p : Mat := Sparse.eval p3_6pRows
private theorem p3_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 4) = p3_6q := by decide +kernel
private theorem p3_6r_check : Sparse.mulEval (p3_6qRows) (WeylData.matrix 6) = p3_6r := by decide +kernel
private theorem p3_6p_check : Sparse.mulEval (rootRows 11 1) (p3_6r) = p3_6p := by decide +kernel
private theorem p3_6_alignment : matrixHom (classProduct 3 6) = p3_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 4 * WeylData.matrix 6) = p3_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p3_6q_check]
  rw [show p3_6q * WeylData.matrix 6 = p3_6r from Sparse.mul_eq_of_check p3_6qRows _ _ p3_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_6p_check
private def p3_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p3_6pow2 : Mat := Sparse.eval p3_6pow2Rows
private theorem p3_6pow2_check : p3_6p * p3_6p = p3_6pow2 := by
  apply Sparse.mul_eq_of_check p3_6pRows
  decide +kernel
private theorem p3_6pow2_eq : p3_6p ^ 2 = p3_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_6pow2_check
theorem product_power_3_6 : classProduct 3 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_6_alignment, map_one]
  rw [p3_6pow2_eq]
  decide +kernel

private def p4_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e5), (14, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e5), (16, e1)],
    [(6, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(12, e1)],
    [(0, e5), (13, e1)],
    [(3, e1)],
    [(0, e3), (19, e1)],
    [(9, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)],
    [(3, e5), (18, e1)],
    [(15, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e5), (20, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(17, e1)]]
private def p4_6q : Mat := Sparse.eval p4_6qRows
private def p4_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e5), (3, e1)],
    [(1, e3), (2, e5), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e5), (9, e1)],
    [(10, e1)],
    [(5, e3), (7, e5), (11, e1)],
    [(12, e1)],
    [(8, e5), (13, e1)],
    [(14, e1)],
    [(8, e3), (15, e1)],
    [(16, e1)],
    [(8, e7), (10, e3), (12, e5), (17, e1)],
    [(14, e5), (18, e1)],
    [(19, e1)],
    [(14, e3), (16, e5), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e5), (23, e1)],
    [(21, e3), (22, e5), (24, e1)],
    [(25, e1)]]
private def p4_6r : Mat := Sparse.eval p4_6rRows
private def p4_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e5), (3, e1)],
    [(1, e3), (2, e5), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e5), (9, e1)],
    [(10, e1)],
    [(5, e3), (7, e5), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e5), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e3), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e7), (10, e3), (12, e5), (17, e1)],
    [(1, e5), (3, e1), (14, e5), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e3), (2, e5), (4, e1), (14, e3), (16, e5), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e5), (3, e1), (5, e5), (9, e1), (21, e5), (23, e1)],
    [(1, e3), (2, e5), (4, e1), (5, e3), (7, e5), (11, e1), (21, e3), (22, e5), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p4_6p : Mat := Sparse.eval p4_6pRows
private theorem p4_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 5) = p4_6q := by decide +kernel
private theorem p4_6r_check : Sparse.mulEval (p4_6qRows) (WeylData.matrix 6) = p4_6r := by decide +kernel
private theorem p4_6p_check : Sparse.mulEval (rootRows 11 1) (p4_6r) = p4_6p := by decide +kernel
private theorem p4_6_alignment : matrixHom (classProduct 4 6) = p4_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 5 * WeylData.matrix 6) = p4_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p4_6q_check]
  rw [show p4_6q * WeylData.matrix 6 = p4_6r from Sparse.mul_eq_of_check p4_6qRows _ _ p4_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_6p_check
private def p4_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p4_6pow2 : Mat := Sparse.eval p4_6pow2Rows
private theorem p4_6pow2_check : p4_6p * p4_6p = p4_6pow2 := by
  apply Sparse.mul_eq_of_check p4_6pRows
  decide +kernel
private theorem p4_6pow2_eq : p4_6p ^ 2 = p4_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_6pow2_check
theorem product_power_4_6 : classProduct 4 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_6_alignment, map_one]
  rw [p4_6pow2_eq]
  decide +kernel

private def p5_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e6), (14, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e6), (16, e1)],
    [(6, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(12, e1)],
    [(0, e6), (13, e1)],
    [(3, e1)],
    [(0, e4), (19, e1)],
    [(9, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)],
    [(3, e6), (18, e1)],
    [(15, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e6), (20, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(17, e1)]]
private def p5_6q : Mat := Sparse.eval p5_6qRows
private def p5_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e6), (3, e1)],
    [(1, e4), (2, e6), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e6), (9, e1)],
    [(10, e1)],
    [(5, e4), (7, e6), (11, e1)],
    [(12, e1)],
    [(8, e6), (13, e1)],
    [(14, e1)],
    [(8, e4), (15, e1)],
    [(16, e1)],
    [(8, e2), (10, e4), (12, e6), (17, e1)],
    [(14, e6), (18, e1)],
    [(19, e1)],
    [(14, e4), (16, e6), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e6), (23, e1)],
    [(21, e4), (22, e6), (24, e1)],
    [(25, e1)]]
private def p5_6r : Mat := Sparse.eval p5_6rRows
private def p5_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e6), (3, e1)],
    [(1, e4), (2, e6), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e6), (9, e1)],
    [(10, e1)],
    [(5, e4), (7, e6), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e6), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e4), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e2), (10, e4), (12, e6), (17, e1)],
    [(1, e6), (3, e1), (14, e6), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e4), (2, e6), (4, e1), (14, e4), (16, e6), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e6), (3, e1), (5, e6), (9, e1), (21, e6), (23, e1)],
    [(1, e4), (2, e6), (4, e1), (5, e4), (7, e6), (11, e1), (21, e4), (22, e6), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p5_6p : Mat := Sparse.eval p5_6pRows
private theorem p5_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 6) = p5_6q := by decide +kernel
private theorem p5_6r_check : Sparse.mulEval (p5_6qRows) (WeylData.matrix 6) = p5_6r := by decide +kernel
private theorem p5_6p_check : Sparse.mulEval (rootRows 11 1) (p5_6r) = p5_6p := by decide +kernel
private theorem p5_6_alignment : matrixHom (classProduct 5 6) = p5_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 6 * WeylData.matrix 6) = p5_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p5_6q_check]
  rw [show p5_6q * WeylData.matrix 6 = p5_6r from Sparse.mul_eq_of_check p5_6qRows _ _ p5_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_6p_check
private def p5_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p5_6pow2 : Mat := Sparse.eval p5_6pow2Rows
private theorem p5_6pow2_check : p5_6p * p5_6p = p5_6pow2 := by
  apply Sparse.mul_eq_of_check p5_6pRows
  decide +kernel
private theorem p5_6pow2_eq : p5_6p ^ 2 = p5_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_6pow2_check
theorem product_power_5_6 : classProduct 5 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_6_alignment, map_one]
  rw [p5_6pow2_eq]
  decide +kernel

private def p6_6qRows : Sparse.Table (Fin 26) := ![[(8, e1)],
    [(1, e1)],
    [(5, e1)],
    [(1, e7), (14, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(2, e1)],
    [(10, e1)],
    [(7, e1)],
    [(0, e1)],
    [(2, e7), (16, e1)],
    [(6, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(12, e1)],
    [(0, e7), (13, e1)],
    [(3, e1)],
    [(0, e5), (19, e1)],
    [(9, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)],
    [(3, e7), (18, e1)],
    [(15, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e1)],
    [(11, e1)],
    [(4, e7), (20, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(17, e1)]]
private def p6_6q : Mat := Sparse.eval p6_6qRows
private def p6_6rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e7), (3, e1)],
    [(1, e5), (2, e7), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e7), (9, e1)],
    [(10, e1)],
    [(5, e5), (7, e7), (11, e1)],
    [(12, e1)],
    [(8, e7), (13, e1)],
    [(14, e1)],
    [(8, e5), (15, e1)],
    [(16, e1)],
    [(8, e3), (10, e5), (12, e7), (17, e1)],
    [(14, e7), (18, e1)],
    [(19, e1)],
    [(14, e5), (16, e7), (20, e1)],
    [(21, e1)],
    [(22, e1)],
    [(21, e7), (23, e1)],
    [(21, e5), (22, e7), (24, e1)],
    [(25, e1)]]
private def p6_6r : Mat := Sparse.eval p6_6rRows
private def p6_6pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e7), (3, e1)],
    [(1, e5), (2, e7), (4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(5, e7), (9, e1)],
    [(10, e1)],
    [(5, e5), (7, e7), (11, e1)],
    [(12, e1)],
    [(0, e1), (8, e7), (13, e1)],
    [(1, e1), (14, e1)],
    [(8, e5), (15, e1)],
    [(2, e1), (16, e1)],
    [(8, e3), (10, e5), (12, e7), (17, e1)],
    [(1, e7), (3, e1), (14, e7), (18, e1)],
    [(0, e1), (19, e1)],
    [(1, e5), (2, e7), (4, e1), (14, e5), (16, e7), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(1, e7), (3, e1), (5, e7), (9, e1), (21, e7), (23, e1)],
    [(1, e5), (2, e7), (4, e1), (5, e5), (7, e7), (11, e1), (21, e5), (22, e7), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p6_6p : Mat := Sparse.eval p6_6pRows
private theorem p6_6q_check : Sparse.mulEval (WeylData.rows (inverseIndex 6)) (rootMatrix 11 7) = p6_6q := by decide +kernel
private theorem p6_6r_check : Sparse.mulEval (p6_6qRows) (WeylData.matrix 6) = p6_6r := by decide +kernel
private theorem p6_6p_check : Sparse.mulEval (rootRows 11 1) (p6_6r) = p6_6p := by decide +kernel
private theorem p6_6_alignment : matrixHom (classProduct 6 6) = p6_6p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 6)) * rootMatrix 11 7 * WeylData.matrix 6) = p6_6p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 6)) _ _ p6_6q_check]
  rw [show p6_6q * WeylData.matrix 6 = p6_6r from Sparse.mul_eq_of_check p6_6qRows _ _ p6_6r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_6p_check
private def p6_6pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p6_6pow2 : Mat := Sparse.eval p6_6pow2Rows
private theorem p6_6pow2_check : p6_6p * p6_6p = p6_6pow2 := by
  apply Sparse.mul_eq_of_check p6_6pRows
  decide +kernel
private theorem p6_6pow2_eq : p6_6p ^ 2 = p6_6pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_6pow2_check
theorem product_power_6_6 : classProduct 6 6 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_6_alignment, map_one]
  rw [p6_6pow2_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
