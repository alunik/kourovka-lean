import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p0_0q : Mat := Sparse.eval p0_0qRows
private def p0_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (18, e1)],
    [(0, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(4, e1), (11, e1), (24, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)]]
private def p0_0r : Mat := Sparse.eval p0_0rRows
private def p0_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p0_0p : Mat := Sparse.eval p0_0pRows
private theorem p0_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 1) = p0_0q := by decide +kernel
private theorem p0_0r_check : Sparse.mulEval (p0_0qRows) (WeylData.matrix 0) = p0_0r := by decide +kernel
private theorem p0_0p_check : Sparse.mulEval (rootRows 11 1) (p0_0r) = p0_0p := by decide +kernel
private theorem p0_0_alignment : matrixHom (classProduct 0 0) = p0_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 1 * WeylData.matrix 0) = p0_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p0_0q_check]
  rw [show p0_0q * WeylData.matrix 0 = p0_0r from Sparse.mul_eq_of_check p0_0qRows _ _ p0_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_0p_check
theorem product_power_0_0 : classProduct 0 0 ^ 1 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_0_alignment, map_one]
  rw [pow_one]
  decide +kernel

private def p1_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e2), (13, e1)],
    [(1, e2), (14, e1)],
    [(15, e1)],
    [(2, e2), (16, e1)],
    [(17, e1)],
    [(3, e2), (18, e1)],
    [(0, e6), (19, e1)],
    [(4, e2), (20, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)]]
private def p1_0q : Mat := Sparse.eval p1_0qRows
private def p1_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e2), (13, e1)],
    [(1, e2), (14, e1)],
    [(15, e1)],
    [(2, e2), (16, e1)],
    [(17, e1)],
    [(3, e2), (18, e1)],
    [(0, e6), (19, e1)],
    [(4, e2), (20, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)]]
private def p1_0r : Mat := Sparse.eval p1_0rRows
private def p1_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e3), (13, e1)],
    [(1, e3), (14, e1)],
    [(15, e1)],
    [(2, e3), (16, e1)],
    [(17, e1)],
    [(3, e3), (18, e1)],
    [(0, e7), (19, e1)],
    [(4, e3), (20, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)]]
private def p1_0p : Mat := Sparse.eval p1_0pRows
private theorem p1_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 2) = p1_0q := by decide +kernel
private theorem p1_0r_check : Sparse.mulEval (p1_0qRows) (WeylData.matrix 0) = p1_0r := by decide +kernel
private theorem p1_0p_check : Sparse.mulEval (rootRows 11 1) (p1_0r) = p1_0p := by decide +kernel
private theorem p1_0_alignment : matrixHom (classProduct 1 0) = p1_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 2 * WeylData.matrix 0) = p1_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p1_0q_check]
  rw [show p1_0q * WeylData.matrix 0 = p1_0r from Sparse.mul_eq_of_check p1_0qRows _ _ p1_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_0p_check
private def p1_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p1_0pow2 : Mat := Sparse.eval p1_0pow2Rows
private theorem p1_0pow2_check : p1_0p * p1_0p = p1_0pow2 := by
  apply Sparse.mul_eq_of_check p1_0pRows
  decide +kernel
private theorem p1_0pow2_eq : p1_0p ^ 2 = p1_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_0pow2_check
theorem product_power_1_0 : classProduct 1 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_0_alignment, map_one]
  rw [p1_0pow2_eq]
  decide +kernel

private def p2_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e3), (13, e1)],
    [(1, e3), (14, e1)],
    [(15, e1)],
    [(2, e3), (16, e1)],
    [(17, e1)],
    [(3, e3), (18, e1)],
    [(0, e7), (19, e1)],
    [(4, e3), (20, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)]]
private def p2_0q : Mat := Sparse.eval p2_0qRows
private def p2_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e3), (13, e1)],
    [(1, e3), (14, e1)],
    [(15, e1)],
    [(2, e3), (16, e1)],
    [(17, e1)],
    [(3, e3), (18, e1)],
    [(0, e7), (19, e1)],
    [(4, e3), (20, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(4, e7), (11, e3), (24, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)]]
private def p2_0r : Mat := Sparse.eval p2_0rRows
private def p2_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e2), (13, e1)],
    [(1, e2), (14, e1)],
    [(15, e1)],
    [(2, e2), (16, e1)],
    [(17, e1)],
    [(3, e2), (18, e1)],
    [(0, e6), (19, e1)],
    [(4, e2), (20, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(4, e6), (11, e2), (24, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)]]
private def p2_0p : Mat := Sparse.eval p2_0pRows
private theorem p2_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 3) = p2_0q := by decide +kernel
private theorem p2_0r_check : Sparse.mulEval (p2_0qRows) (WeylData.matrix 0) = p2_0r := by decide +kernel
private theorem p2_0p_check : Sparse.mulEval (rootRows 11 1) (p2_0r) = p2_0p := by decide +kernel
private theorem p2_0_alignment : matrixHom (classProduct 2 0) = p2_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 3 * WeylData.matrix 0) = p2_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p2_0q_check]
  rw [show p2_0q * WeylData.matrix 0 = p2_0r from Sparse.mul_eq_of_check p2_0qRows _ _ p2_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_0p_check
private def p2_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p2_0pow2 : Mat := Sparse.eval p2_0pow2Rows
private theorem p2_0pow2_check : p2_0p * p2_0p = p2_0pow2 := by
  apply Sparse.mul_eq_of_check p2_0pRows
  decide +kernel
private theorem p2_0pow2_eq : p2_0p ^ 2 = p2_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_0pow2_check
theorem product_power_2_0 : classProduct 2 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_0_alignment, map_one]
  rw [p2_0pow2_eq]
  decide +kernel

private def p3_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e4), (13, e1)],
    [(1, e4), (14, e1)],
    [(15, e1)],
    [(2, e4), (16, e1)],
    [(17, e1)],
    [(3, e4), (18, e1)],
    [(0, e2), (19, e1)],
    [(4, e4), (20, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)]]
private def p3_0q : Mat := Sparse.eval p3_0qRows
private def p3_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e4), (13, e1)],
    [(1, e4), (14, e1)],
    [(15, e1)],
    [(2, e4), (16, e1)],
    [(17, e1)],
    [(3, e4), (18, e1)],
    [(0, e2), (19, e1)],
    [(4, e4), (20, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)]]
private def p3_0r : Mat := Sparse.eval p3_0rRows
private def p3_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e5), (13, e1)],
    [(1, e5), (14, e1)],
    [(15, e1)],
    [(2, e5), (16, e1)],
    [(17, e1)],
    [(3, e5), (18, e1)],
    [(0, e3), (19, e1)],
    [(4, e5), (20, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)]]
private def p3_0p : Mat := Sparse.eval p3_0pRows
private theorem p3_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 4) = p3_0q := by decide +kernel
private theorem p3_0r_check : Sparse.mulEval (p3_0qRows) (WeylData.matrix 0) = p3_0r := by decide +kernel
private theorem p3_0p_check : Sparse.mulEval (rootRows 11 1) (p3_0r) = p3_0p := by decide +kernel
private theorem p3_0_alignment : matrixHom (classProduct 3 0) = p3_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 4 * WeylData.matrix 0) = p3_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p3_0q_check]
  rw [show p3_0q * WeylData.matrix 0 = p3_0r from Sparse.mul_eq_of_check p3_0qRows _ _ p3_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_0p_check
private def p3_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p3_0pow2 : Mat := Sparse.eval p3_0pow2Rows
private theorem p3_0pow2_check : p3_0p * p3_0p = p3_0pow2 := by
  apply Sparse.mul_eq_of_check p3_0pRows
  decide +kernel
private theorem p3_0pow2_eq : p3_0p ^ 2 = p3_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_0pow2_check
theorem product_power_3_0 : classProduct 3 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_0_alignment, map_one]
  rw [p3_0pow2_eq]
  decide +kernel

private def p4_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e5), (13, e1)],
    [(1, e5), (14, e1)],
    [(15, e1)],
    [(2, e5), (16, e1)],
    [(17, e1)],
    [(3, e5), (18, e1)],
    [(0, e3), (19, e1)],
    [(4, e5), (20, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)]]
private def p4_0q : Mat := Sparse.eval p4_0qRows
private def p4_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e5), (13, e1)],
    [(1, e5), (14, e1)],
    [(15, e1)],
    [(2, e5), (16, e1)],
    [(17, e1)],
    [(3, e5), (18, e1)],
    [(0, e3), (19, e1)],
    [(4, e5), (20, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(4, e3), (11, e5), (24, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)]]
private def p4_0r : Mat := Sparse.eval p4_0rRows
private def p4_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e4), (13, e1)],
    [(1, e4), (14, e1)],
    [(15, e1)],
    [(2, e4), (16, e1)],
    [(17, e1)],
    [(3, e4), (18, e1)],
    [(0, e2), (19, e1)],
    [(4, e4), (20, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(4, e2), (11, e4), (24, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)]]
private def p4_0p : Mat := Sparse.eval p4_0pRows
private theorem p4_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 5) = p4_0q := by decide +kernel
private theorem p4_0r_check : Sparse.mulEval (p4_0qRows) (WeylData.matrix 0) = p4_0r := by decide +kernel
private theorem p4_0p_check : Sparse.mulEval (rootRows 11 1) (p4_0r) = p4_0p := by decide +kernel
private theorem p4_0_alignment : matrixHom (classProduct 4 0) = p4_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 5 * WeylData.matrix 0) = p4_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p4_0q_check]
  rw [show p4_0q * WeylData.matrix 0 = p4_0r from Sparse.mul_eq_of_check p4_0qRows _ _ p4_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_0p_check
private def p4_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p4_0pow2 : Mat := Sparse.eval p4_0pow2Rows
private theorem p4_0pow2_check : p4_0p * p4_0p = p4_0pow2 := by
  apply Sparse.mul_eq_of_check p4_0pRows
  decide +kernel
private theorem p4_0pow2_eq : p4_0p ^ 2 = p4_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_0pow2_check
theorem product_power_4_0 : classProduct 4 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_0_alignment, map_one]
  rw [p4_0pow2_eq]
  decide +kernel

private def p5_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e6), (13, e1)],
    [(1, e6), (14, e1)],
    [(15, e1)],
    [(2, e6), (16, e1)],
    [(17, e1)],
    [(3, e6), (18, e1)],
    [(0, e4), (19, e1)],
    [(4, e6), (20, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)]]
private def p5_0q : Mat := Sparse.eval p5_0qRows
private def p5_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e6), (13, e1)],
    [(1, e6), (14, e1)],
    [(15, e1)],
    [(2, e6), (16, e1)],
    [(17, e1)],
    [(3, e6), (18, e1)],
    [(0, e4), (19, e1)],
    [(4, e6), (20, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)]]
private def p5_0r : Mat := Sparse.eval p5_0rRows
private def p5_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e7), (13, e1)],
    [(1, e7), (14, e1)],
    [(15, e1)],
    [(2, e7), (16, e1)],
    [(17, e1)],
    [(3, e7), (18, e1)],
    [(0, e5), (19, e1)],
    [(4, e7), (20, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)]]
private def p5_0p : Mat := Sparse.eval p5_0pRows
private theorem p5_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 6) = p5_0q := by decide +kernel
private theorem p5_0r_check : Sparse.mulEval (p5_0qRows) (WeylData.matrix 0) = p5_0r := by decide +kernel
private theorem p5_0p_check : Sparse.mulEval (rootRows 11 1) (p5_0r) = p5_0p := by decide +kernel
private theorem p5_0_alignment : matrixHom (classProduct 5 0) = p5_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 6 * WeylData.matrix 0) = p5_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p5_0q_check]
  rw [show p5_0q * WeylData.matrix 0 = p5_0r from Sparse.mul_eq_of_check p5_0qRows _ _ p5_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_0p_check
private def p5_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p5_0pow2 : Mat := Sparse.eval p5_0pow2Rows
private theorem p5_0pow2_check : p5_0p * p5_0p = p5_0pow2 := by
  apply Sparse.mul_eq_of_check p5_0pRows
  decide +kernel
private theorem p5_0pow2_eq : p5_0p ^ 2 = p5_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_0pow2_check
theorem product_power_5_0 : classProduct 5 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_0_alignment, map_one]
  rw [p5_0pow2_eq]
  decide +kernel

private def p6_0qRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e7), (13, e1)],
    [(1, e7), (14, e1)],
    [(15, e1)],
    [(2, e7), (16, e1)],
    [(17, e1)],
    [(3, e7), (18, e1)],
    [(0, e5), (19, e1)],
    [(4, e7), (20, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)]]
private def p6_0q : Mat := Sparse.eval p6_0qRows
private def p6_0rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e7), (13, e1)],
    [(1, e7), (14, e1)],
    [(15, e1)],
    [(2, e7), (16, e1)],
    [(17, e1)],
    [(3, e7), (18, e1)],
    [(0, e5), (19, e1)],
    [(4, e7), (20, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(4, e5), (11, e7), (24, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)]]
private def p6_0r : Mat := Sparse.eval p6_0rRows
private def p6_0pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e6), (13, e1)],
    [(1, e6), (14, e1)],
    [(15, e1)],
    [(2, e6), (16, e1)],
    [(17, e1)],
    [(3, e6), (18, e1)],
    [(0, e4), (19, e1)],
    [(4, e6), (20, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(4, e4), (11, e6), (24, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)]]
private def p6_0p : Mat := Sparse.eval p6_0pRows
private theorem p6_0q_check : Sparse.mulEval (WeylData.rows (inverseIndex 0)) (rootMatrix 11 7) = p6_0q := by decide +kernel
private theorem p6_0r_check : Sparse.mulEval (p6_0qRows) (WeylData.matrix 0) = p6_0r := by decide +kernel
private theorem p6_0p_check : Sparse.mulEval (rootRows 11 1) (p6_0r) = p6_0p := by decide +kernel
private theorem p6_0_alignment : matrixHom (classProduct 6 0) = p6_0p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 0)) * rootMatrix 11 7 * WeylData.matrix 0) = p6_0p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 0)) _ _ p6_0q_check]
  rw [show p6_0q * WeylData.matrix 0 = p6_0r from Sparse.mul_eq_of_check p6_0qRows _ _ p6_0r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_0p_check
private def p6_0pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p6_0pow2 : Mat := Sparse.eval p6_0pow2Rows
private theorem p6_0pow2_check : p6_0p * p6_0p = p6_0pow2 := by
  apply Sparse.mul_eq_of_check p6_0pRows
  decide +kernel
private theorem p6_0pow2_eq : p6_0p ^ 2 = p6_0pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_0pow2_check
theorem product_power_6_0 : classProduct 6 0 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_0_alignment, map_one]
  rw [p6_0pow2_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
