import Kourovka.Problem2153.WilsonModel.ClassTests.ProductBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open Field8 F8 RootData RootSystem
private def p0_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e1), (14, e1)],
    [(0, e1), (12, e1), (13, e1)],
    [(0, e1), (13, e1)],
    [(11, e1)],
    [(2, e1), (16, e1)],
    [(15, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(0, e1), (19, e1)],
    [(3, e1), (18, e1)],
    [(2, e1), (7, e1), (22, e1)],
    [(17, e1)],
    [(4, e1), (20, e1)],
    [(3, e1), (9, e1), (23, e1)],
    [(0, e1), (6, e1), (12, e1), (25, e1)],
    [(4, e1), (11, e1), (24, e1)]]
private def p0_2q : Mat := Sparse.eval p0_2qRows
private def p0_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(1, e1), (13, e1)],
    [(14, e1)],
    [(2, e1), (15, e1)],
    [(16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (18, e1)],
    [(5, e1), (19, e1)],
    [(2, e1), (6, e1), (20, e1)],
    [(21, e1)],
    [(8, e1), (22, e1)],
    [(5, e1), (10, e1), (23, e1)],
    [(1, e1), (7, e1), (12, e1), (13, e1), (24, e1)],
    [(8, e1), (14, e1), (25, e1)]]
private def p0_2r : Mat := Sparse.eval p0_2rRows
private def p0_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e1), (11, e1)],
    [(1, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e1), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (18, e1)],
    [(0, e1), (5, e1), (19, e1)],
    [(2, e1), (4, e1), (6, e1), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e1), (22, e1)],
    [(3, e1), (5, e1), (9, e1), (10, e1), (23, e1)],
    [(0, e1), (1, e1), (4, e1), (7, e1), (11, e1), (12, e1), (13, e1), (24, e1)],
    [(0, e1), (1, e1), (6, e1), (8, e1), (12, e1), (14, e1), (25, e1)]]
private def p0_2p : Mat := Sparse.eval p0_2pRows
private theorem p0_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 1) = p0_2q := by decide +kernel
private theorem p0_2r_check : Sparse.mulEval (p0_2qRows) (WeylData.matrix 2) = p0_2r := by decide +kernel
private theorem p0_2p_check : Sparse.mulEval (rootRows 11 1) (p0_2r) = p0_2p := by decide +kernel
private theorem p0_2_alignment : matrixHom (classProduct 0 2) = p0_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 1 * WeylData.matrix 2) = p0_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p0_2q_check]
  rw [show p0_2q * WeylData.matrix 2 = p0_2r from Sparse.mul_eq_of_check p0_2qRows _ _ p0_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p0_2p_check
private def p0_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p0_2pow2 : Mat := Sparse.eval p0_2pow2Rows
private theorem p0_2pow2_check : p0_2p * p0_2p = p0_2pow2 := by
  apply Sparse.mul_eq_of_check p0_2pRows
  decide +kernel
private theorem p0_2pow2_eq : p0_2p ^ 2 = p0_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p0_2pow2_check
theorem product_power_0_2 : classProduct 0 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p0_2_alignment, map_one]
  rw [p0_2pow2_eq]
  decide +kernel

private def p1_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e2), (14, e1)],
    [(0, e2), (12, e1), (13, e1)],
    [(0, e2), (13, e1)],
    [(11, e1)],
    [(2, e2), (16, e1)],
    [(15, e1)],
    [(1, e6), (5, e2), (21, e1)],
    [(0, e6), (19, e1)],
    [(3, e2), (18, e1)],
    [(2, e6), (7, e2), (22, e1)],
    [(17, e1)],
    [(4, e2), (20, e1)],
    [(3, e6), (9, e2), (23, e1)],
    [(0, e4), (6, e6), (12, e2), (25, e1)],
    [(4, e6), (11, e2), (24, e1)]]
private def p1_2q : Mat := Sparse.eval p1_2qRows
private def p1_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e2), (11, e1)],
    [(1, e2), (12, e1)],
    [(1, e2), (13, e1)],
    [(14, e1)],
    [(2, e2), (15, e1)],
    [(16, e1)],
    [(0, e6), (3, e2), (17, e1)],
    [(1, e6), (18, e1)],
    [(5, e2), (19, e1)],
    [(2, e6), (6, e2), (20, e1)],
    [(21, e1)],
    [(8, e2), (22, e1)],
    [(5, e6), (10, e2), (23, e1)],
    [(1, e4), (7, e6), (12, e2), (13, e2), (24, e1)],
    [(8, e6), (14, e2), (25, e1)]]
private def p1_2r : Mat := Sparse.eval p1_2rRows
private def p1_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e2), (11, e1)],
    [(1, e2), (12, e1)],
    [(0, e1), (1, e2), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e2), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e6), (3, e2), (17, e1)],
    [(1, e6), (3, e1), (18, e1)],
    [(0, e1), (5, e2), (19, e1)],
    [(2, e6), (4, e1), (6, e2), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e2), (22, e1)],
    [(3, e1), (5, e6), (9, e1), (10, e2), (23, e1)],
    [(0, e2), (1, e4), (4, e1), (7, e6), (11, e1), (12, e2), (13, e2), (24, e1)],
    [(0, e1), (1, e2), (6, e1), (8, e6), (12, e1), (14, e2), (25, e1)]]
private def p1_2p : Mat := Sparse.eval p1_2pRows
private theorem p1_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 2) = p1_2q := by decide +kernel
private theorem p1_2r_check : Sparse.mulEval (p1_2qRows) (WeylData.matrix 2) = p1_2r := by decide +kernel
private theorem p1_2p_check : Sparse.mulEval (rootRows 11 1) (p1_2r) = p1_2p := by decide +kernel
private theorem p1_2_alignment : matrixHom (classProduct 1 2) = p1_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 2 * WeylData.matrix 2) = p1_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p1_2q_check]
  rw [show p1_2q * WeylData.matrix 2 = p1_2r from Sparse.mul_eq_of_check p1_2qRows _ _ p1_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p1_2p_check
private def p1_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p1_2pow2 : Mat := Sparse.eval p1_2pow2Rows
private theorem p1_2pow2_check : p1_2p * p1_2p = p1_2pow2 := by
  apply Sparse.mul_eq_of_check p1_2pRows
  decide +kernel
private theorem p1_2pow2_eq : p1_2p ^ 2 = p1_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p1_2pow2_check
theorem product_power_1_2 : classProduct 1 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p1_2_alignment, map_one]
  rw [p1_2pow2_eq]
  decide +kernel

private def p2_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e3), (14, e1)],
    [(0, e3), (12, e1), (13, e1)],
    [(0, e3), (13, e1)],
    [(11, e1)],
    [(2, e3), (16, e1)],
    [(15, e1)],
    [(1, e7), (5, e3), (21, e1)],
    [(0, e7), (19, e1)],
    [(3, e3), (18, e1)],
    [(2, e7), (7, e3), (22, e1)],
    [(17, e1)],
    [(4, e3), (20, e1)],
    [(3, e7), (9, e3), (23, e1)],
    [(0, e5), (6, e7), (12, e3), (25, e1)],
    [(4, e7), (11, e3), (24, e1)]]
private def p2_2q : Mat := Sparse.eval p2_2qRows
private def p2_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e3), (11, e1)],
    [(1, e3), (12, e1)],
    [(1, e3), (13, e1)],
    [(14, e1)],
    [(2, e3), (15, e1)],
    [(16, e1)],
    [(0, e7), (3, e3), (17, e1)],
    [(1, e7), (18, e1)],
    [(5, e3), (19, e1)],
    [(2, e7), (6, e3), (20, e1)],
    [(21, e1)],
    [(8, e3), (22, e1)],
    [(5, e7), (10, e3), (23, e1)],
    [(1, e5), (7, e7), (12, e3), (13, e3), (24, e1)],
    [(8, e7), (14, e3), (25, e1)]]
private def p2_2r : Mat := Sparse.eval p2_2rRows
private def p2_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e3), (11, e1)],
    [(1, e3), (12, e1)],
    [(0, e1), (1, e3), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e3), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e7), (3, e3), (17, e1)],
    [(1, e7), (3, e1), (18, e1)],
    [(0, e1), (5, e3), (19, e1)],
    [(2, e7), (4, e1), (6, e3), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e3), (22, e1)],
    [(3, e1), (5, e7), (9, e1), (10, e3), (23, e1)],
    [(0, e3), (1, e5), (4, e1), (7, e7), (11, e1), (12, e3), (13, e3), (24, e1)],
    [(0, e1), (1, e3), (6, e1), (8, e7), (12, e1), (14, e3), (25, e1)]]
private def p2_2p : Mat := Sparse.eval p2_2pRows
private theorem p2_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 3) = p2_2q := by decide +kernel
private theorem p2_2r_check : Sparse.mulEval (p2_2qRows) (WeylData.matrix 2) = p2_2r := by decide +kernel
private theorem p2_2p_check : Sparse.mulEval (rootRows 11 1) (p2_2r) = p2_2p := by decide +kernel
private theorem p2_2_alignment : matrixHom (classProduct 2 2) = p2_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 3 * WeylData.matrix 2) = p2_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p2_2q_check]
  rw [show p2_2q * WeylData.matrix 2 = p2_2r from Sparse.mul_eq_of_check p2_2qRows _ _ p2_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p2_2p_check
private def p2_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p2_2pow2 : Mat := Sparse.eval p2_2pow2Rows
private theorem p2_2pow2_check : p2_2p * p2_2p = p2_2pow2 := by
  apply Sparse.mul_eq_of_check p2_2pRows
  decide +kernel
private theorem p2_2pow2_eq : p2_2p ^ 2 = p2_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p2_2pow2_check
theorem product_power_2_2 : classProduct 2 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p2_2_alignment, map_one]
  rw [p2_2pow2_eq]
  decide +kernel

private def p3_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e4), (14, e1)],
    [(0, e4), (12, e1), (13, e1)],
    [(0, e4), (13, e1)],
    [(11, e1)],
    [(2, e4), (16, e1)],
    [(15, e1)],
    [(1, e2), (5, e4), (21, e1)],
    [(0, e2), (19, e1)],
    [(3, e4), (18, e1)],
    [(2, e2), (7, e4), (22, e1)],
    [(17, e1)],
    [(4, e4), (20, e1)],
    [(3, e2), (9, e4), (23, e1)],
    [(0, e6), (6, e2), (12, e4), (25, e1)],
    [(4, e2), (11, e4), (24, e1)]]
private def p3_2q : Mat := Sparse.eval p3_2qRows
private def p3_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e4), (11, e1)],
    [(1, e4), (12, e1)],
    [(1, e4), (13, e1)],
    [(14, e1)],
    [(2, e4), (15, e1)],
    [(16, e1)],
    [(0, e2), (3, e4), (17, e1)],
    [(1, e2), (18, e1)],
    [(5, e4), (19, e1)],
    [(2, e2), (6, e4), (20, e1)],
    [(21, e1)],
    [(8, e4), (22, e1)],
    [(5, e2), (10, e4), (23, e1)],
    [(1, e6), (7, e2), (12, e4), (13, e4), (24, e1)],
    [(8, e2), (14, e4), (25, e1)]]
private def p3_2r : Mat := Sparse.eval p3_2rRows
private def p3_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e4), (11, e1)],
    [(1, e4), (12, e1)],
    [(0, e1), (1, e4), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e4), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e2), (3, e4), (17, e1)],
    [(1, e2), (3, e1), (18, e1)],
    [(0, e1), (5, e4), (19, e1)],
    [(2, e2), (4, e1), (6, e4), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e4), (22, e1)],
    [(3, e1), (5, e2), (9, e1), (10, e4), (23, e1)],
    [(0, e4), (1, e6), (4, e1), (7, e2), (11, e1), (12, e4), (13, e4), (24, e1)],
    [(0, e1), (1, e4), (6, e1), (8, e2), (12, e1), (14, e4), (25, e1)]]
private def p3_2p : Mat := Sparse.eval p3_2pRows
private theorem p3_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 4) = p3_2q := by decide +kernel
private theorem p3_2r_check : Sparse.mulEval (p3_2qRows) (WeylData.matrix 2) = p3_2r := by decide +kernel
private theorem p3_2p_check : Sparse.mulEval (rootRows 11 1) (p3_2r) = p3_2p := by decide +kernel
private theorem p3_2_alignment : matrixHom (classProduct 3 2) = p3_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 4 * WeylData.matrix 2) = p3_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p3_2q_check]
  rw [show p3_2q * WeylData.matrix 2 = p3_2r from Sparse.mul_eq_of_check p3_2qRows _ _ p3_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p3_2p_check
private def p3_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p3_2pow2 : Mat := Sparse.eval p3_2pow2Rows
private theorem p3_2pow2_check : p3_2p * p3_2p = p3_2pow2 := by
  apply Sparse.mul_eq_of_check p3_2pRows
  decide +kernel
private theorem p3_2pow2_eq : p3_2p ^ 2 = p3_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p3_2pow2_check
theorem product_power_3_2 : classProduct 3 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p3_2_alignment, map_one]
  rw [p3_2pow2_eq]
  decide +kernel

private def p4_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e5), (14, e1)],
    [(0, e5), (12, e1), (13, e1)],
    [(0, e5), (13, e1)],
    [(11, e1)],
    [(2, e5), (16, e1)],
    [(15, e1)],
    [(1, e3), (5, e5), (21, e1)],
    [(0, e3), (19, e1)],
    [(3, e5), (18, e1)],
    [(2, e3), (7, e5), (22, e1)],
    [(17, e1)],
    [(4, e5), (20, e1)],
    [(3, e3), (9, e5), (23, e1)],
    [(0, e7), (6, e3), (12, e5), (25, e1)],
    [(4, e3), (11, e5), (24, e1)]]
private def p4_2q : Mat := Sparse.eval p4_2qRows
private def p4_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e5), (11, e1)],
    [(1, e5), (12, e1)],
    [(1, e5), (13, e1)],
    [(14, e1)],
    [(2, e5), (15, e1)],
    [(16, e1)],
    [(0, e3), (3, e5), (17, e1)],
    [(1, e3), (18, e1)],
    [(5, e5), (19, e1)],
    [(2, e3), (6, e5), (20, e1)],
    [(21, e1)],
    [(8, e5), (22, e1)],
    [(5, e3), (10, e5), (23, e1)],
    [(1, e7), (7, e3), (12, e5), (13, e5), (24, e1)],
    [(8, e3), (14, e5), (25, e1)]]
private def p4_2r : Mat := Sparse.eval p4_2rRows
private def p4_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e5), (11, e1)],
    [(1, e5), (12, e1)],
    [(0, e1), (1, e5), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e5), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e3), (3, e5), (17, e1)],
    [(1, e3), (3, e1), (18, e1)],
    [(0, e1), (5, e5), (19, e1)],
    [(2, e3), (4, e1), (6, e5), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e5), (22, e1)],
    [(3, e1), (5, e3), (9, e1), (10, e5), (23, e1)],
    [(0, e5), (1, e7), (4, e1), (7, e3), (11, e1), (12, e5), (13, e5), (24, e1)],
    [(0, e1), (1, e5), (6, e1), (8, e3), (12, e1), (14, e5), (25, e1)]]
private def p4_2p : Mat := Sparse.eval p4_2pRows
private theorem p4_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 5) = p4_2q := by decide +kernel
private theorem p4_2r_check : Sparse.mulEval (p4_2qRows) (WeylData.matrix 2) = p4_2r := by decide +kernel
private theorem p4_2p_check : Sparse.mulEval (rootRows 11 1) (p4_2r) = p4_2p := by decide +kernel
private theorem p4_2_alignment : matrixHom (classProduct 4 2) = p4_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 5 * WeylData.matrix 2) = p4_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p4_2q_check]
  rw [show p4_2q * WeylData.matrix 2 = p4_2r from Sparse.mul_eq_of_check p4_2qRows _ _ p4_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p4_2p_check
private def p4_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p4_2pow2 : Mat := Sparse.eval p4_2pow2Rows
private theorem p4_2pow2_check : p4_2p * p4_2p = p4_2pow2 := by
  apply Sparse.mul_eq_of_check p4_2pRows
  decide +kernel
private theorem p4_2pow2_eq : p4_2p ^ 2 = p4_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p4_2pow2_check
theorem product_power_4_2 : classProduct 4 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p4_2_alignment, map_one]
  rw [p4_2pow2_eq]
  decide +kernel

private def p5_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e6), (14, e1)],
    [(0, e6), (12, e1), (13, e1)],
    [(0, e6), (13, e1)],
    [(11, e1)],
    [(2, e6), (16, e1)],
    [(15, e1)],
    [(1, e4), (5, e6), (21, e1)],
    [(0, e4), (19, e1)],
    [(3, e6), (18, e1)],
    [(2, e4), (7, e6), (22, e1)],
    [(17, e1)],
    [(4, e6), (20, e1)],
    [(3, e4), (9, e6), (23, e1)],
    [(0, e2), (6, e4), (12, e6), (25, e1)],
    [(4, e4), (11, e6), (24, e1)]]
private def p5_2q : Mat := Sparse.eval p5_2qRows
private def p5_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e6), (11, e1)],
    [(1, e6), (12, e1)],
    [(1, e6), (13, e1)],
    [(14, e1)],
    [(2, e6), (15, e1)],
    [(16, e1)],
    [(0, e4), (3, e6), (17, e1)],
    [(1, e4), (18, e1)],
    [(5, e6), (19, e1)],
    [(2, e4), (6, e6), (20, e1)],
    [(21, e1)],
    [(8, e6), (22, e1)],
    [(5, e4), (10, e6), (23, e1)],
    [(1, e2), (7, e4), (12, e6), (13, e6), (24, e1)],
    [(8, e4), (14, e6), (25, e1)]]
private def p5_2r : Mat := Sparse.eval p5_2rRows
private def p5_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e6), (11, e1)],
    [(1, e6), (12, e1)],
    [(0, e1), (1, e6), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e6), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e4), (3, e6), (17, e1)],
    [(1, e4), (3, e1), (18, e1)],
    [(0, e1), (5, e6), (19, e1)],
    [(2, e4), (4, e1), (6, e6), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e6), (22, e1)],
    [(3, e1), (5, e4), (9, e1), (10, e6), (23, e1)],
    [(0, e6), (1, e2), (4, e1), (7, e4), (11, e1), (12, e6), (13, e6), (24, e1)],
    [(0, e1), (1, e6), (6, e1), (8, e4), (12, e1), (14, e6), (25, e1)]]
private def p5_2p : Mat := Sparse.eval p5_2pRows
private theorem p5_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 6) = p5_2q := by decide +kernel
private theorem p5_2r_check : Sparse.mulEval (p5_2qRows) (WeylData.matrix 2) = p5_2r := by decide +kernel
private theorem p5_2p_check : Sparse.mulEval (rootRows 11 1) (p5_2r) = p5_2p := by decide +kernel
private theorem p5_2_alignment : matrixHom (classProduct 5 2) = p5_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 6 * WeylData.matrix 2) = p5_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p5_2q_check]
  rw [show p5_2q * WeylData.matrix 2 = p5_2r from Sparse.mul_eq_of_check p5_2qRows _ _ p5_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p5_2p_check
private def p5_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p5_2pow2 : Mat := Sparse.eval p5_2pow2Rows
private theorem p5_2pow2_check : p5_2p * p5_2p = p5_2pow2 := by
  apply Sparse.mul_eq_of_check p5_2pRows
  decide +kernel
private theorem p5_2pow2_eq : p5_2p ^ 2 = p5_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p5_2pow2_check
theorem product_power_5_2 : classProduct 5 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p5_2_alignment, map_one]
  rw [p5_2pow2_eq]
  decide +kernel

private def p6_2qRows : Sparse.Table (Fin 26) := ![[(1, e1)],
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
    [(1, e7), (14, e1)],
    [(0, e7), (12, e1), (13, e1)],
    [(0, e7), (13, e1)],
    [(11, e1)],
    [(2, e7), (16, e1)],
    [(15, e1)],
    [(1, e5), (5, e7), (21, e1)],
    [(0, e5), (19, e1)],
    [(3, e7), (18, e1)],
    [(2, e5), (7, e7), (22, e1)],
    [(17, e1)],
    [(4, e7), (20, e1)],
    [(3, e5), (9, e7), (23, e1)],
    [(0, e3), (6, e5), (12, e7), (25, e1)],
    [(4, e5), (11, e7), (24, e1)]]
private def p6_2q : Mat := Sparse.eval p6_2qRows
private def p6_2rRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e7), (11, e1)],
    [(1, e7), (12, e1)],
    [(1, e7), (13, e1)],
    [(14, e1)],
    [(2, e7), (15, e1)],
    [(16, e1)],
    [(0, e5), (3, e7), (17, e1)],
    [(1, e5), (18, e1)],
    [(5, e7), (19, e1)],
    [(2, e5), (6, e7), (20, e1)],
    [(21, e1)],
    [(8, e7), (22, e1)],
    [(5, e5), (10, e7), (23, e1)],
    [(1, e3), (7, e5), (12, e7), (13, e7), (24, e1)],
    [(8, e5), (14, e7), (25, e1)]]
private def p6_2r : Mat := Sparse.eval p6_2rRows
private def p6_2pRows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
    [(0, e7), (11, e1)],
    [(1, e7), (12, e1)],
    [(0, e1), (1, e7), (13, e1)],
    [(1, e1), (14, e1)],
    [(2, e7), (15, e1)],
    [(2, e1), (16, e1)],
    [(0, e5), (3, e7), (17, e1)],
    [(1, e5), (3, e1), (18, e1)],
    [(0, e1), (5, e7), (19, e1)],
    [(2, e5), (4, e1), (6, e7), (20, e1)],
    [(1, e1), (5, e1), (21, e1)],
    [(2, e1), (7, e1), (8, e7), (22, e1)],
    [(3, e1), (5, e5), (9, e1), (10, e7), (23, e1)],
    [(0, e7), (1, e3), (4, e1), (7, e5), (11, e1), (12, e7), (13, e7), (24, e1)],
    [(0, e1), (1, e7), (6, e1), (8, e5), (12, e1), (14, e7), (25, e1)]]
private def p6_2p : Mat := Sparse.eval p6_2pRows
private theorem p6_2q_check : Sparse.mulEval (WeylData.rows (inverseIndex 2)) (rootMatrix 11 7) = p6_2q := by decide +kernel
private theorem p6_2r_check : Sparse.mulEval (p6_2qRows) (WeylData.matrix 2) = p6_2r := by decide +kernel
private theorem p6_2p_check : Sparse.mulEval (rootRows 11 1) (p6_2r) = p6_2p := by decide +kernel
private theorem p6_2_alignment : matrixHom (classProduct 6 2) = p6_2p := by
  rw [classProduct_matrix]
  change rootMatrix 11 1 * (Sparse.eval (WeylData.rows (inverseIndex 2)) * rootMatrix 11 7 * WeylData.matrix 2) = p6_2p
  rw [Sparse.mul_eq_of_check (WeylData.rows (inverseIndex 2)) _ _ p6_2q_check]
  rw [show p6_2q * WeylData.matrix 2 = p6_2r from Sparse.mul_eq_of_check p6_2qRows _ _ p6_2r_check]
  exact Sparse.mul_eq_of_check (rootRows 11 1) _ _ p6_2p_check
private def p6_2pow2Rows : Sparse.Table (Fin 26) := ![[(0, e1)],
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
private def p6_2pow2 : Mat := Sparse.eval p6_2pow2Rows
private theorem p6_2pow2_check : p6_2p * p6_2p = p6_2pow2 := by
  apply Sparse.mul_eq_of_check p6_2pRows
  decide +kernel
private theorem p6_2pow2_eq : p6_2p ^ 2 = p6_2pow2 := by
  rw [show 2 = 1 + 1 from rfl, pow_add]
  simp only [pow_one]
  exact p6_2pow2_check
theorem product_power_6_2 : classProduct 6 2 ^ 2 = 1 := by
  apply matrixHom_injective
  rw [map_pow, p6_2_alignment, map_one]
  rw [p6_2pow2_eq]
  decide +kernel

end Kourovka.Problem2153.WilsonModel.ClassTests
