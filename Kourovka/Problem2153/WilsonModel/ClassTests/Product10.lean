import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_10qRows : Sparse.Table (Fin 26) := ![[(1, e1), (5, e1), (21, e1)],
    [(8, e1)],
    [(1, e1), (14, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(5, e1)],
    [(2, e1), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e1), (19, e1)],
    [(7, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(0, e1), (12, e1), (13, e1)],
    [(0, e1), (13, e1)],
    [(2, e1)],
    [(3, e1), (18, e1)],
    [(6, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e1), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p0_10q : Mat := Sparse.eval p0_10qRows
private def p0_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e1), (8, e1)],
    [(1, e1)],
    [(2, e1), (8, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(5, e1)],
    [(6, e1), (14, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e1)],
    [(10, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(12, e1), (21, e1)],
    [(13, e1), (21, e1)],
    [(14, e1)],
    [(15, e1), (22, e1)],
    [(16, e1)],
    [(17, e1), (23, e1), (25, e1)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e1)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p0_10r : Mat := Sparse.eval p0_10rRows
private def p0_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e1), (8, e1)],
    [(1, e1)],
    [(2, e1), (8, e1)],
    [(3, e1), (10, e1), (14, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (21, e1)],
    [(5, e1)],
    [(6, e1), (14, e1)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e1)],
    [(10, e1)],
    [(11, e1), (19, e1), (22, e1)],
    [(12, e1), (21, e1)],
    [(0, e1), (5, e1), (8, e1), (13, e1), (21, e1)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e1)],
    [(2, e1), (8, e1), (16, e1)],
    [(17, e1), (23, e1), (25, e1)],
    [(3, e1), (10, e1), (14, e1), (18, e1)],
    [(0, e1), (5, e1), (8, e1), (19, e1)],
    [(4, e1), (12, e1), (13, e1), (16, e1), (20, e1), (21, e1), (25, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e1), (22, e1)],
    [(3, e1), (9, e1), (10, e1), (14, e1), (21, e1), (23, e1)],
    [(4, e1), (11, e1), (12, e1), (13, e1), (16, e1), (19, e1), (21, e1), (22, e1), (24, e1)],
    [(0, e1), (5, e1), (6, e1), (8, e1), (12, e1), (14, e1), (21, e1), (25, e1)]]
private def p0_10p : Mat := Sparse.eval p0_10pRows
private theorem p0_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 1) = p0_10q := by decide +kernel
private theorem p0_10r_check : Sparse.mulEval (p0_10qRows) (WeylData.matrix 10) = p0_10r := by decide +kernel
private theorem p0_10p_check : Sparse.mulEval (rootRows 11 1) (p0_10r) = p0_10p := by decide +kernel
private theorem p0_10_alignment : matrixHom (classProduct 0 10) = p0_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 1 * WeylData.matrix 10) = p0_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p0_10q_check]
  rw [show p0_10q * WeylData.matrix 10 = p0_10r from Sparse.mul_eq_of_check p0_10qRows _ _ p0_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_10p_check
private def p0_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(0, e1), (1, e1), (2, e1), (4, e1)],
    [(5, e1)],
    [(1, e1), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e1), (5, e1), (9, e1)],
    [(10, e1)],
    [(0, e1), (2, e1), (5, e1), (7, e1), (11, e1)],
    [(1, e1), (5, e1), (12, e1)],
    [(1, e1), (8, e1), (13, e1)],
    [(14, e1)],
    [(2, e1), (7, e1), (8, e1), (15, e1)],
    [(8, e1), (16, e1)],
    [(0, e1), (3, e1), (5, e1), (6, e1), (8, e1), (9, e1), (10, e1), (12, e1), (17, e1)],
    [(1, e1), (10, e1), (14, e1), (18, e1)],
    [(5, e1), (8, e1), (19, e1)],
    [(1, e1), (2, e1), (5, e1), (6, e1), (8, e1), (13, e1), (14, e1), (16, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (22, e1)],
    [(5, e1), (10, e1), (14, e1), (21, e1), (23, e1)],
    [(1, e1), (5, e1), (7, e1), (12, e1), (13, e1), (16, e1), (19, e1), (21, e1), (22, e1), (24, e1)],
    [(8, e1), (14, e1), (21, e1), (25, e1)]]
private def p0_10pow2 : Mat := Sparse.eval p0_10pow2Rows
private theorem p0_10pow2_check : p0_10p * p0_10p = p0_10pow2 := by
  apply Sparse.mul_eq_of_check p0_10pRows
  decide +kernel
private theorem p0_10pow2_eq : p0_10p ^ 2 = p0_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p0_10pow2_check
private def p0_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p0_10pow4 : Mat := Sparse.eval p0_10pow4Rows
private theorem p0_10pow4_check : p0_10pow2 * p0_10pow2 = p0_10pow4 := by
  apply Sparse.mul_eq_of_check p0_10pow2Rows
  decide +kernel
private theorem p0_10pow4_eq : p0_10p ^ 4 = p0_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p0_10pow2_eq]
  exact p0_10pow4_check
theorem product_power_0_10 : classProduct 0 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_10_alignment, map_one]
  rw [p0_10pow4_eq]
  decide +kernel

private def p1_10qRows : Sparse.Table (Fin 26) := ![[(1, e6), (5, e2), (21, e1)],
    [(8, e1)],
    [(1, e2), (14, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)],
    [(5, e1)],
    [(2, e2), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e6), (19, e1)],
    [(7, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(0, e2), (12, e1), (13, e1)],
    [(0, e2), (13, e1)],
    [(2, e1)],
    [(3, e2), (18, e1)],
    [(6, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e2), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p1_10q : Mat := Sparse.eval p1_10qRows
private def p1_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e2), (8, e6)],
    [(1, e1)],
    [(2, e1), (8, e2)],
    [(3, e1), (10, e2), (14, e6)],
    [(4, e1), (12, e2), (13, e2), (16, e6), (21, e4)],
    [(5, e1)],
    [(6, e1), (14, e2)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e6)],
    [(10, e1)],
    [(11, e1), (19, e2), (22, e6)],
    [(12, e1), (21, e2)],
    [(13, e1), (21, e2)],
    [(14, e1)],
    [(15, e1), (22, e2)],
    [(16, e1)],
    [(17, e1), (23, e2), (25, e6)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e2)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p1_10r : Mat := Sparse.eval p1_10rRows
private def p1_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e2), (8, e6)],
    [(1, e1)],
    [(2, e1), (8, e2)],
    [(3, e1), (10, e2), (14, e6)],
    [(4, e1), (12, e2), (13, e2), (16, e6), (21, e4)],
    [(5, e1)],
    [(6, e1), (14, e2)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e6)],
    [(10, e1)],
    [(11, e1), (19, e2), (22, e6)],
    [(12, e1), (21, e2)],
    [(0, e1), (5, e2), (8, e6), (13, e1), (21, e2)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e2)],
    [(2, e1), (8, e2), (16, e1)],
    [(17, e1), (23, e2), (25, e6)],
    [(3, e1), (10, e2), (14, e6), (18, e1)],
    [(0, e1), (5, e2), (8, e6), (19, e1)],
    [(4, e1), (12, e2), (13, e2), (16, e6), (20, e1), (21, e4), (25, e2)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e2), (22, e1)],
    [(3, e1), (9, e1), (10, e2), (14, e6), (21, e6), (23, e1)],
    [(4, e1), (11, e1), (12, e2), (13, e2), (16, e6), (19, e2), (21, e4), (22, e6), (24, e1)],
    [(0, e1), (5, e2), (6, e1), (8, e6), (12, e1), (14, e2), (21, e2), (25, e1)]]
private def p1_10p : Mat := Sparse.eval p1_10pRows
private theorem p1_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 2) = p1_10q := by decide +kernel
private theorem p1_10r_check : Sparse.mulEval (p1_10qRows) (WeylData.matrix 10) = p1_10r := by decide +kernel
private theorem p1_10p_check : Sparse.mulEval (rootRows 11 1) (p1_10r) = p1_10p := by decide +kernel
private theorem p1_10_alignment : matrixHom (classProduct 1 10) = p1_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 2 * WeylData.matrix 10) = p1_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p1_10q_check]
  rw [show p1_10q * WeylData.matrix 10 = p1_10r from Sparse.mul_eq_of_check p1_10qRows _ _ p1_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_10p_check
private def p1_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e6), (3, e1)],
    [(0, e2), (1, e4), (2, e6), (4, e1)],
    [(5, e1)],
    [(1, e2), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e6), (5, e6), (9, e1)],
    [(10, e1)],
    [(0, e2), (2, e6), (5, e4), (7, e6), (11, e1)],
    [(1, e2), (5, e2), (12, e1)],
    [(1, e2), (8, e6), (13, e1)],
    [(14, e1)],
    [(2, e2), (7, e2), (8, e4), (15, e1)],
    [(8, e2), (16, e1)],
    [(0, e6), (3, e2), (5, e7), (6, e6), (8, e2), (9, e2), (10, e4), (12, e6), (17, e1)],
    [(1, e6), (10, e2), (14, e6), (18, e1)],
    [(5, e2), (8, e6), (19, e1)],
    [(1, e4), (2, e6), (5, e4), (6, e2), (8, e7), (13, e2), (14, e4), (16, e6), (20, e1)],
    [(21, e1)],
    [(8, e2), (22, e1)],
    [(5, e6), (10, e2), (14, e6), (21, e6), (23, e1)],
    [(1, e4), (5, e4), (7, e6), (12, e2), (13, e2), (16, e6), (19, e2), (21, e4), (22, e6), (24, e1)],
    [(8, e6), (14, e2), (21, e2), (25, e1)]]
private def p1_10pow2 : Mat := Sparse.eval p1_10pow2Rows
private theorem p1_10pow2_check : p1_10p * p1_10p = p1_10pow2 := by
  apply Sparse.mul_eq_of_check p1_10pRows
  decide +kernel
private theorem p1_10pow2_eq : p1_10p ^ 2 = p1_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_10pow2_check
private def p1_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p1_10pow4 : Mat := Sparse.eval p1_10pow4Rows
private theorem p1_10pow4_check : p1_10pow2 * p1_10pow2 = p1_10pow4 := by
  apply Sparse.mul_eq_of_check p1_10pow2Rows
  decide +kernel
private theorem p1_10pow4_eq : p1_10p ^ 4 = p1_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p1_10pow2_eq]
  exact p1_10pow4_check
theorem product_power_1_10 : classProduct 1 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_10_alignment, map_one]
  rw [p1_10pow4_eq]
  decide +kernel

private def p2_10qRows : Sparse.Table (Fin 26) := ![[(1, e7), (5, e3), (21, e1)],
    [(8, e1)],
    [(1, e3), (14, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)],
    [(5, e1)],
    [(2, e3), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e7), (19, e1)],
    [(7, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(0, e3), (12, e1), (13, e1)],
    [(0, e3), (13, e1)],
    [(2, e1)],
    [(3, e3), (18, e1)],
    [(6, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e3), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p2_10q : Mat := Sparse.eval p2_10qRows
private def p2_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e3), (8, e7)],
    [(1, e1)],
    [(2, e1), (8, e3)],
    [(3, e1), (10, e3), (14, e7)],
    [(4, e1), (12, e3), (13, e3), (16, e7), (21, e5)],
    [(5, e1)],
    [(6, e1), (14, e3)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e7)],
    [(10, e1)],
    [(11, e1), (19, e3), (22, e7)],
    [(12, e1), (21, e3)],
    [(13, e1), (21, e3)],
    [(14, e1)],
    [(15, e1), (22, e3)],
    [(16, e1)],
    [(17, e1), (23, e3), (25, e7)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e3)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p2_10r : Mat := Sparse.eval p2_10rRows
private def p2_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e3), (8, e7)],
    [(1, e1)],
    [(2, e1), (8, e3)],
    [(3, e1), (10, e3), (14, e7)],
    [(4, e1), (12, e3), (13, e3), (16, e7), (21, e5)],
    [(5, e1)],
    [(6, e1), (14, e3)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e7)],
    [(10, e1)],
    [(11, e1), (19, e3), (22, e7)],
    [(12, e1), (21, e3)],
    [(0, e1), (5, e3), (8, e7), (13, e1), (21, e3)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e3)],
    [(2, e1), (8, e3), (16, e1)],
    [(17, e1), (23, e3), (25, e7)],
    [(3, e1), (10, e3), (14, e7), (18, e1)],
    [(0, e1), (5, e3), (8, e7), (19, e1)],
    [(4, e1), (12, e3), (13, e3), (16, e7), (20, e1), (21, e5), (25, e3)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e3), (22, e1)],
    [(3, e1), (9, e1), (10, e3), (14, e7), (21, e7), (23, e1)],
    [(4, e1), (11, e1), (12, e3), (13, e3), (16, e7), (19, e3), (21, e5), (22, e7), (24, e1)],
    [(0, e1), (5, e3), (6, e1), (8, e7), (12, e1), (14, e3), (21, e3), (25, e1)]]
private def p2_10p : Mat := Sparse.eval p2_10pRows
private theorem p2_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 3) = p2_10q := by decide +kernel
private theorem p2_10r_check : Sparse.mulEval (p2_10qRows) (WeylData.matrix 10) = p2_10r := by decide +kernel
private theorem p2_10p_check : Sparse.mulEval (rootRows 11 1) (p2_10r) = p2_10p := by decide +kernel
private theorem p2_10_alignment : matrixHom (classProduct 2 10) = p2_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 3 * WeylData.matrix 10) = p2_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p2_10q_check]
  rw [show p2_10q * WeylData.matrix 10 = p2_10r from Sparse.mul_eq_of_check p2_10qRows _ _ p2_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_10p_check
private def p2_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e7), (3, e1)],
    [(0, e3), (1, e5), (2, e7), (4, e1)],
    [(5, e1)],
    [(1, e3), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e7), (5, e7), (9, e1)],
    [(10, e1)],
    [(0, e3), (2, e7), (5, e5), (7, e7), (11, e1)],
    [(1, e3), (5, e3), (12, e1)],
    [(1, e3), (8, e7), (13, e1)],
    [(14, e1)],
    [(2, e3), (7, e3), (8, e5), (15, e1)],
    [(8, e3), (16, e1)],
    [(0, e7), (3, e3), (5, e2), (6, e7), (8, e3), (9, e3), (10, e5), (12, e7), (17, e1)],
    [(1, e7), (10, e3), (14, e7), (18, e1)],
    [(5, e3), (8, e7), (19, e1)],
    [(1, e5), (2, e7), (5, e5), (6, e3), (8, e2), (13, e3), (14, e5), (16, e7), (20, e1)],
    [(21, e1)],
    [(8, e3), (22, e1)],
    [(5, e7), (10, e3), (14, e7), (21, e7), (23, e1)],
    [(1, e5), (5, e5), (7, e7), (12, e3), (13, e3), (16, e7), (19, e3), (21, e5), (22, e7), (24, e1)],
    [(8, e7), (14, e3), (21, e3), (25, e1)]]
private def p2_10pow2 : Mat := Sparse.eval p2_10pow2Rows
private theorem p2_10pow2_check : p2_10p * p2_10p = p2_10pow2 := by
  apply Sparse.mul_eq_of_check p2_10pRows
  decide +kernel
private theorem p2_10pow2_eq : p2_10p ^ 2 = p2_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_10pow2_check
private def p2_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p2_10pow4 : Mat := Sparse.eval p2_10pow4Rows
private theorem p2_10pow4_check : p2_10pow2 * p2_10pow2 = p2_10pow4 := by
  apply Sparse.mul_eq_of_check p2_10pow2Rows
  decide +kernel
private theorem p2_10pow4_eq : p2_10p ^ 4 = p2_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p2_10pow2_eq]
  exact p2_10pow4_check
theorem product_power_2_10 : classProduct 2 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_10_alignment, map_one]
  rw [p2_10pow4_eq]
  decide +kernel

private def p3_10qRows : Sparse.Table (Fin 26) := ![[(1, e2), (5, e4), (21, e1)],
    [(8, e1)],
    [(1, e4), (14, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)],
    [(5, e1)],
    [(2, e4), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e2), (19, e1)],
    [(7, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(0, e4), (12, e1), (13, e1)],
    [(0, e4), (13, e1)],
    [(2, e1)],
    [(3, e4), (18, e1)],
    [(6, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e4), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p3_10q : Mat := Sparse.eval p3_10qRows
private def p3_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e4), (8, e2)],
    [(1, e1)],
    [(2, e1), (8, e4)],
    [(3, e1), (10, e4), (14, e2)],
    [(4, e1), (12, e4), (13, e4), (16, e2), (21, e6)],
    [(5, e1)],
    [(6, e1), (14, e4)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e2)],
    [(10, e1)],
    [(11, e1), (19, e4), (22, e2)],
    [(12, e1), (21, e4)],
    [(13, e1), (21, e4)],
    [(14, e1)],
    [(15, e1), (22, e4)],
    [(16, e1)],
    [(17, e1), (23, e4), (25, e2)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e4)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p3_10r : Mat := Sparse.eval p3_10rRows
private def p3_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e4), (8, e2)],
    [(1, e1)],
    [(2, e1), (8, e4)],
    [(3, e1), (10, e4), (14, e2)],
    [(4, e1), (12, e4), (13, e4), (16, e2), (21, e6)],
    [(5, e1)],
    [(6, e1), (14, e4)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e2)],
    [(10, e1)],
    [(11, e1), (19, e4), (22, e2)],
    [(12, e1), (21, e4)],
    [(0, e1), (5, e4), (8, e2), (13, e1), (21, e4)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e4)],
    [(2, e1), (8, e4), (16, e1)],
    [(17, e1), (23, e4), (25, e2)],
    [(3, e1), (10, e4), (14, e2), (18, e1)],
    [(0, e1), (5, e4), (8, e2), (19, e1)],
    [(4, e1), (12, e4), (13, e4), (16, e2), (20, e1), (21, e6), (25, e4)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e4), (22, e1)],
    [(3, e1), (9, e1), (10, e4), (14, e2), (21, e2), (23, e1)],
    [(4, e1), (11, e1), (12, e4), (13, e4), (16, e2), (19, e4), (21, e6), (22, e2), (24, e1)],
    [(0, e1), (5, e4), (6, e1), (8, e2), (12, e1), (14, e4), (21, e4), (25, e1)]]
private def p3_10p : Mat := Sparse.eval p3_10pRows
private theorem p3_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 4) = p3_10q := by decide +kernel
private theorem p3_10r_check : Sparse.mulEval (p3_10qRows) (WeylData.matrix 10) = p3_10r := by decide +kernel
private theorem p3_10p_check : Sparse.mulEval (rootRows 11 1) (p3_10r) = p3_10p := by decide +kernel
private theorem p3_10_alignment : matrixHom (classProduct 3 10) = p3_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 4 * WeylData.matrix 10) = p3_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p3_10q_check]
  rw [show p3_10q * WeylData.matrix 10 = p3_10r from Sparse.mul_eq_of_check p3_10qRows _ _ p3_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_10p_check
private def p3_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e2), (3, e1)],
    [(0, e4), (1, e6), (2, e2), (4, e1)],
    [(5, e1)],
    [(1, e4), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e2), (5, e2), (9, e1)],
    [(10, e1)],
    [(0, e4), (2, e2), (5, e6), (7, e2), (11, e1)],
    [(1, e4), (5, e4), (12, e1)],
    [(1, e4), (8, e2), (13, e1)],
    [(14, e1)],
    [(2, e4), (7, e4), (8, e6), (15, e1)],
    [(8, e4), (16, e1)],
    [(0, e2), (3, e4), (5, e3), (6, e2), (8, e4), (9, e4), (10, e6), (12, e2), (17, e1)],
    [(1, e2), (10, e4), (14, e2), (18, e1)],
    [(5, e4), (8, e2), (19, e1)],
    [(1, e6), (2, e2), (5, e6), (6, e4), (8, e3), (13, e4), (14, e6), (16, e2), (20, e1)],
    [(21, e1)],
    [(8, e4), (22, e1)],
    [(5, e2), (10, e4), (14, e2), (21, e2), (23, e1)],
    [(1, e6), (5, e6), (7, e2), (12, e4), (13, e4), (16, e2), (19, e4), (21, e6), (22, e2), (24, e1)],
    [(8, e2), (14, e4), (21, e4), (25, e1)]]
private def p3_10pow2 : Mat := Sparse.eval p3_10pow2Rows
private theorem p3_10pow2_check : p3_10p * p3_10p = p3_10pow2 := by
  apply Sparse.mul_eq_of_check p3_10pRows
  decide +kernel
private theorem p3_10pow2_eq : p3_10p ^ 2 = p3_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_10pow2_check
private def p3_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p3_10pow4 : Mat := Sparse.eval p3_10pow4Rows
private theorem p3_10pow4_check : p3_10pow2 * p3_10pow2 = p3_10pow4 := by
  apply Sparse.mul_eq_of_check p3_10pow2Rows
  decide +kernel
private theorem p3_10pow4_eq : p3_10p ^ 4 = p3_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p3_10pow2_eq]
  exact p3_10pow4_check
theorem product_power_3_10 : classProduct 3 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_10_alignment, map_one]
  rw [p3_10pow4_eq]
  decide +kernel

private def p4_10qRows : Sparse.Table (Fin 26) := ![[(1, e3), (5, e5), (21, e1)],
    [(8, e1)],
    [(1, e5), (14, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)],
    [(5, e1)],
    [(2, e5), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e3), (19, e1)],
    [(7, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(0, e5), (12, e1), (13, e1)],
    [(0, e5), (13, e1)],
    [(2, e1)],
    [(3, e5), (18, e1)],
    [(6, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e5), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p4_10q : Mat := Sparse.eval p4_10qRows
private def p4_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e5), (8, e3)],
    [(1, e1)],
    [(2, e1), (8, e5)],
    [(3, e1), (10, e5), (14, e3)],
    [(4, e1), (12, e5), (13, e5), (16, e3), (21, e7)],
    [(5, e1)],
    [(6, e1), (14, e5)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e3)],
    [(10, e1)],
    [(11, e1), (19, e5), (22, e3)],
    [(12, e1), (21, e5)],
    [(13, e1), (21, e5)],
    [(14, e1)],
    [(15, e1), (22, e5)],
    [(16, e1)],
    [(17, e1), (23, e5), (25, e3)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e5)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p4_10r : Mat := Sparse.eval p4_10rRows
private def p4_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e5), (8, e3)],
    [(1, e1)],
    [(2, e1), (8, e5)],
    [(3, e1), (10, e5), (14, e3)],
    [(4, e1), (12, e5), (13, e5), (16, e3), (21, e7)],
    [(5, e1)],
    [(6, e1), (14, e5)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e3)],
    [(10, e1)],
    [(11, e1), (19, e5), (22, e3)],
    [(12, e1), (21, e5)],
    [(0, e1), (5, e5), (8, e3), (13, e1), (21, e5)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e5)],
    [(2, e1), (8, e5), (16, e1)],
    [(17, e1), (23, e5), (25, e3)],
    [(3, e1), (10, e5), (14, e3), (18, e1)],
    [(0, e1), (5, e5), (8, e3), (19, e1)],
    [(4, e1), (12, e5), (13, e5), (16, e3), (20, e1), (21, e7), (25, e5)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e5), (22, e1)],
    [(3, e1), (9, e1), (10, e5), (14, e3), (21, e3), (23, e1)],
    [(4, e1), (11, e1), (12, e5), (13, e5), (16, e3), (19, e5), (21, e7), (22, e3), (24, e1)],
    [(0, e1), (5, e5), (6, e1), (8, e3), (12, e1), (14, e5), (21, e5), (25, e1)]]
private def p4_10p : Mat := Sparse.eval p4_10pRows
private theorem p4_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 5) = p4_10q := by decide +kernel
private theorem p4_10r_check : Sparse.mulEval (p4_10qRows) (WeylData.matrix 10) = p4_10r := by decide +kernel
private theorem p4_10p_check : Sparse.mulEval (rootRows 11 1) (p4_10r) = p4_10p := by decide +kernel
private theorem p4_10_alignment : matrixHom (classProduct 4 10) = p4_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 5 * WeylData.matrix 10) = p4_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p4_10q_check]
  rw [show p4_10q * WeylData.matrix 10 = p4_10r from Sparse.mul_eq_of_check p4_10qRows _ _ p4_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_10p_check
private def p4_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e3), (3, e1)],
    [(0, e5), (1, e7), (2, e3), (4, e1)],
    [(5, e1)],
    [(1, e5), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e3), (5, e3), (9, e1)],
    [(10, e1)],
    [(0, e5), (2, e3), (5, e7), (7, e3), (11, e1)],
    [(1, e5), (5, e5), (12, e1)],
    [(1, e5), (8, e3), (13, e1)],
    [(14, e1)],
    [(2, e5), (7, e5), (8, e7), (15, e1)],
    [(8, e5), (16, e1)],
    [(0, e3), (3, e5), (5, e4), (6, e3), (8, e5), (9, e5), (10, e7), (12, e3), (17, e1)],
    [(1, e3), (10, e5), (14, e3), (18, e1)],
    [(5, e5), (8, e3), (19, e1)],
    [(1, e7), (2, e3), (5, e7), (6, e5), (8, e4), (13, e5), (14, e7), (16, e3), (20, e1)],
    [(21, e1)],
    [(8, e5), (22, e1)],
    [(5, e3), (10, e5), (14, e3), (21, e3), (23, e1)],
    [(1, e7), (5, e7), (7, e3), (12, e5), (13, e5), (16, e3), (19, e5), (21, e7), (22, e3), (24, e1)],
    [(8, e3), (14, e5), (21, e5), (25, e1)]]
private def p4_10pow2 : Mat := Sparse.eval p4_10pow2Rows
private theorem p4_10pow2_check : p4_10p * p4_10p = p4_10pow2 := by
  apply Sparse.mul_eq_of_check p4_10pRows
  decide +kernel
private theorem p4_10pow2_eq : p4_10p ^ 2 = p4_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_10pow2_check
private def p4_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p4_10pow4 : Mat := Sparse.eval p4_10pow4Rows
private theorem p4_10pow4_check : p4_10pow2 * p4_10pow2 = p4_10pow4 := by
  apply Sparse.mul_eq_of_check p4_10pow2Rows
  decide +kernel
private theorem p4_10pow4_eq : p4_10p ^ 4 = p4_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p4_10pow2_eq]
  exact p4_10pow4_check
theorem product_power_4_10 : classProduct 4 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_10_alignment, map_one]
  rw [p4_10pow4_eq]
  decide +kernel

private def p5_10qRows : Sparse.Table (Fin 26) := ![[(1, e4), (5, e6), (21, e1)],
    [(8, e1)],
    [(1, e6), (14, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)],
    [(5, e1)],
    [(2, e6), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e4), (19, e1)],
    [(7, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(0, e6), (12, e1), (13, e1)],
    [(0, e6), (13, e1)],
    [(2, e1)],
    [(3, e6), (18, e1)],
    [(6, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e6), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p5_10q : Mat := Sparse.eval p5_10qRows
private def p5_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e6), (8, e4)],
    [(1, e1)],
    [(2, e1), (8, e6)],
    [(3, e1), (10, e6), (14, e4)],
    [(4, e1), (12, e6), (13, e6), (16, e4), (21, e2)],
    [(5, e1)],
    [(6, e1), (14, e6)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e4)],
    [(10, e1)],
    [(11, e1), (19, e6), (22, e4)],
    [(12, e1), (21, e6)],
    [(13, e1), (21, e6)],
    [(14, e1)],
    [(15, e1), (22, e6)],
    [(16, e1)],
    [(17, e1), (23, e6), (25, e4)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e6)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p5_10r : Mat := Sparse.eval p5_10rRows
private def p5_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e6), (8, e4)],
    [(1, e1)],
    [(2, e1), (8, e6)],
    [(3, e1), (10, e6), (14, e4)],
    [(4, e1), (12, e6), (13, e6), (16, e4), (21, e2)],
    [(5, e1)],
    [(6, e1), (14, e6)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e4)],
    [(10, e1)],
    [(11, e1), (19, e6), (22, e4)],
    [(12, e1), (21, e6)],
    [(0, e1), (5, e6), (8, e4), (13, e1), (21, e6)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e6)],
    [(2, e1), (8, e6), (16, e1)],
    [(17, e1), (23, e6), (25, e4)],
    [(3, e1), (10, e6), (14, e4), (18, e1)],
    [(0, e1), (5, e6), (8, e4), (19, e1)],
    [(4, e1), (12, e6), (13, e6), (16, e4), (20, e1), (21, e2), (25, e6)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e6), (22, e1)],
    [(3, e1), (9, e1), (10, e6), (14, e4), (21, e4), (23, e1)],
    [(4, e1), (11, e1), (12, e6), (13, e6), (16, e4), (19, e6), (21, e2), (22, e4), (24, e1)],
    [(0, e1), (5, e6), (6, e1), (8, e4), (12, e1), (14, e6), (21, e6), (25, e1)]]
private def p5_10p : Mat := Sparse.eval p5_10pRows
private theorem p5_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 6) = p5_10q := by decide +kernel
private theorem p5_10r_check : Sparse.mulEval (p5_10qRows) (WeylData.matrix 10) = p5_10r := by decide +kernel
private theorem p5_10p_check : Sparse.mulEval (rootRows 11 1) (p5_10r) = p5_10p := by decide +kernel
private theorem p5_10_alignment : matrixHom (classProduct 5 10) = p5_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 6 * WeylData.matrix 10) = p5_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p5_10q_check]
  rw [show p5_10q * WeylData.matrix 10 = p5_10r from Sparse.mul_eq_of_check p5_10qRows _ _ p5_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_10p_check
private def p5_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e4), (3, e1)],
    [(0, e6), (1, e2), (2, e4), (4, e1)],
    [(5, e1)],
    [(1, e6), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e4), (5, e4), (9, e1)],
    [(10, e1)],
    [(0, e6), (2, e4), (5, e2), (7, e4), (11, e1)],
    [(1, e6), (5, e6), (12, e1)],
    [(1, e6), (8, e4), (13, e1)],
    [(14, e1)],
    [(2, e6), (7, e6), (8, e2), (15, e1)],
    [(8, e6), (16, e1)],
    [(0, e4), (3, e6), (5, e5), (6, e4), (8, e6), (9, e6), (10, e2), (12, e4), (17, e1)],
    [(1, e4), (10, e6), (14, e4), (18, e1)],
    [(5, e6), (8, e4), (19, e1)],
    [(1, e2), (2, e4), (5, e2), (6, e6), (8, e5), (13, e6), (14, e2), (16, e4), (20, e1)],
    [(21, e1)],
    [(8, e6), (22, e1)],
    [(5, e4), (10, e6), (14, e4), (21, e4), (23, e1)],
    [(1, e2), (5, e2), (7, e4), (12, e6), (13, e6), (16, e4), (19, e6), (21, e2), (22, e4), (24, e1)],
    [(8, e4), (14, e6), (21, e6), (25, e1)]]
private def p5_10pow2 : Mat := Sparse.eval p5_10pow2Rows
private theorem p5_10pow2_check : p5_10p * p5_10p = p5_10pow2 := by
  apply Sparse.mul_eq_of_check p5_10pRows
  decide +kernel
private theorem p5_10pow2_eq : p5_10p ^ 2 = p5_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_10pow2_check
private def p5_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p5_10pow4 : Mat := Sparse.eval p5_10pow4Rows
private theorem p5_10pow4_check : p5_10pow2 * p5_10pow2 = p5_10pow4 := by
  apply Sparse.mul_eq_of_check p5_10pow2Rows
  decide +kernel
private theorem p5_10pow4_eq : p5_10p ^ 4 = p5_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p5_10pow2_eq]
  exact p5_10pow4_check
theorem product_power_5_10 : classProduct 5 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_10_alignment, map_one]
  rw [p5_10pow4_eq]
  decide +kernel

private def p6_10qRows : Sparse.Table (Fin 26) := ![[(1, e5), (5, e7), (21, e1)],
    [(8, e1)],
    [(1, e7), (14, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)],
    [(5, e1)],
    [(2, e7), (16, e1)],
    [(10, e1)],
    [(1, e1)],
    [(0, e5), (19, e1)],
    [(7, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(0, e7), (12, e1), (13, e1)],
    [(0, e7), (13, e1)],
    [(2, e1)],
    [(3, e7), (18, e1)],
    [(6, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(15, e1)],
    [(9, e1)],
    [(4, e7), (20, e1)],
    [(0, e1)],
    [(3, e1)],
    [(11, e1)],
    [(17, e1)],
    [(4, e1)]]
private def p6_10q : Mat := Sparse.eval p6_10qRows
private def p6_10rRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e7), (8, e5)],
    [(1, e1)],
    [(2, e1), (8, e7)],
    [(3, e1), (10, e7), (14, e5)],
    [(4, e1), (12, e7), (13, e7), (16, e5), (21, e3)],
    [(5, e1)],
    [(6, e1), (14, e7)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e5)],
    [(10, e1)],
    [(11, e1), (19, e7), (22, e5)],
    [(12, e1), (21, e7)],
    [(13, e1), (21, e7)],
    [(14, e1)],
    [(15, e1), (22, e7)],
    [(16, e1)],
    [(17, e1), (23, e7), (25, e5)],
    [(18, e1)],
    [(19, e1)],
    [(20, e1), (25, e7)],
    [(21, e1)],
    [(22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(25, e1)]]
private def p6_10r : Mat := Sparse.eval p6_10rRows
private def p6_10pRows : Sparse.Table (Fin 26) := ![[(0, e1), (5, e7), (8, e5)],
    [(1, e1)],
    [(2, e1), (8, e7)],
    [(3, e1), (10, e7), (14, e5)],
    [(4, e1), (12, e7), (13, e7), (16, e5), (21, e3)],
    [(5, e1)],
    [(6, e1), (14, e7)],
    [(7, e1)],
    [(8, e1)],
    [(9, e1), (21, e5)],
    [(10, e1)],
    [(11, e1), (19, e7), (22, e5)],
    [(12, e1), (21, e7)],
    [(0, e1), (5, e7), (8, e5), (13, e1), (21, e7)],
    [(1, e1), (14, e1)],
    [(15, e1), (22, e7)],
    [(2, e1), (8, e7), (16, e1)],
    [(17, e1), (23, e7), (25, e5)],
    [(3, e1), (10, e7), (14, e5), (18, e1)],
    [(0, e1), (5, e7), (8, e5), (19, e1)],
    [(4, e1), (12, e7), (13, e7), (16, e5), (20, e1), (21, e3), (25, e7)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e7), (22, e1)],
    [(3, e1), (9, e1), (10, e7), (14, e5), (21, e5), (23, e1)],
    [(4, e1), (11, e1), (12, e7), (13, e7), (16, e5), (19, e7), (21, e3), (22, e5), (24, e1)],
    [(0, e1), (5, e7), (6, e1), (8, e5), (12, e1), (14, e7), (21, e7), (25, e1)]]
private def p6_10p : Mat := Sparse.eval p6_10pRows
private theorem p6_10q_check : Sparse.mulEval (WeylData.rows (inverseIndex 10)) (rootMatrix 11 7) = p6_10q := by decide +kernel
private theorem p6_10r_check : Sparse.mulEval (p6_10qRows) (WeylData.matrix 10) = p6_10r := by decide +kernel
private theorem p6_10p_check : Sparse.mulEval (rootRows 11 1) (p6_10r) = p6_10p := by decide +kernel
private theorem p6_10_alignment : matrixHom (classProduct 6 10) = p6_10p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 10)) * rootMatrix 11 7 * WeylData.matrix 10) = p6_10p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 10)) _ _ p6_10q_check]
  rw [show p6_10q * WeylData.matrix 10 = p6_10r from Sparse.mul_eq_of_check p6_10qRows _ _ p6_10r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_10p_check
private def p6_10pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(1, e5), (3, e1)],
    [(0, e7), (1, e3), (2, e5), (4, e1)],
    [(5, e1)],
    [(1, e7), (6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(1, e5), (5, e5), (9, e1)],
    [(10, e1)],
    [(0, e7), (2, e5), (5, e3), (7, e5), (11, e1)],
    [(1, e7), (5, e7), (12, e1)],
    [(1, e7), (8, e5), (13, e1)],
    [(14, e1)],
    [(2, e7), (7, e7), (8, e3), (15, e1)],
    [(8, e7), (16, e1)],
    [(0, e5), (3, e7), (5, e6), (6, e5), (8, e7), (9, e7), (10, e3), (12, e5), (17, e1)],
    [(1, e5), (10, e7), (14, e5), (18, e1)],
    [(5, e7), (8, e5), (19, e1)],
    [(1, e3), (2, e5), (5, e3), (6, e7), (8, e6), (13, e7), (14, e3), (16, e5), (20, e1)],
    [(21, e1)],
    [(8, e7), (22, e1)],
    [(5, e5), (10, e7), (14, e5), (21, e5), (23, e1)],
    [(1, e3), (5, e3), (7, e5), (12, e7), (13, e7), (16, e5), (19, e7), (21, e3), (22, e5), (24, e1)],
    [(8, e5), (14, e7), (21, e7), (25, e1)]]
private def p6_10pow2 : Mat := Sparse.eval p6_10pow2Rows
private theorem p6_10pow2_check : p6_10p * p6_10p = p6_10pow2 := by
  apply Sparse.mul_eq_of_check p6_10pRows
  decide +kernel
private theorem p6_10pow2_eq : p6_10p ^ 2 = p6_10pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_10pow2_check
private def p6_10pow4Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p6_10pow4 : Mat := Sparse.eval p6_10pow4Rows
private theorem p6_10pow4_check : p6_10pow2 * p6_10pow2 = p6_10pow4 := by
  apply Sparse.mul_eq_of_check p6_10pow2Rows
  decide +kernel
private theorem p6_10pow4_eq : p6_10p ^ 4 = p6_10pow4 := by
  rw [show 4 = 2 + 2 from rfl, pow_add]
  rw [p6_10pow2_eq]
  exact p6_10pow4_check
theorem product_power_6_10 : classProduct 6 10 ^ 4 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_10_alignment, map_one]
  rw [p6_10pow4_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
