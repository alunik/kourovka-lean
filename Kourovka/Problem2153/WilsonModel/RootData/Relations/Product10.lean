import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_60_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e4), (7, e1)],
    [(1, e4), (8, e1)],
    [(9, e1)],
    [(0, e2), (10, e1)],
    [(11, e1)],
    [(3, e4), (12, e1)],
    [(13, e1)],
    [(2, e2), (14, e1)],
    [(4, e4), (15, e1)],
    [(6, e4), (16, e1)],
    [(17, e1)],
    [(4, e2), (18, e1)],
    [(9, e4), (19, e1)],
    [(20, e1)],
    [(0, e3), (7, e2), (10, e4), (21, e1)],
    [(3, e6), (13, e4), (22, e1)],
    [(11, e2), (23, e1)],
    [(17, e4), (24, e1)],
    [(4, e3), (15, e2), (18, e4), (25, e1)]])
private theorem product_60_left_s1 : wordMatrix [Atom.root 8 5] = atomMatrix (Atom.root 8 5) := by simp
private theorem product_60_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 5] = product_60_target := by
  rw [wordMatrix_cons, product_60_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_60_left : wordMatrix [Atom.root 8 1, Atom.root 8 5] = product_60_target := product_60_left_s0
private theorem product_60_right_s0 : wordMatrix [Atom.root 8 4] = atomMatrix (Atom.root 8 4) := by simp
private theorem product_60_right : wordMatrix [Atom.root 8 4] = product_60_target := by
  rw [product_60_right_s0]
  decide +kernel
theorem product_60 : wordGroup (product_lhs 60) = wordGroup (product_rhs 60) := by
  apply word_eq_of_matrix_eq
  exact product_60_left.trans product_60_right.symm

private def product_61_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e7), (7, e1)],
    [(1, e7), (8, e1)],
    [(9, e1)],
    [(0, e5), (10, e1)],
    [(11, e1)],
    [(3, e7), (12, e1)],
    [(13, e1)],
    [(2, e5), (14, e1)],
    [(4, e7), (15, e1)],
    [(6, e7), (16, e1)],
    [(17, e1)],
    [(4, e5), (18, e1)],
    [(9, e7), (19, e1)],
    [(20, e1)],
    [(0, e6), (7, e5), (10, e7), (21, e1)],
    [(3, e3), (13, e7), (22, e1)],
    [(11, e5), (23, e1)],
    [(17, e7), (24, e1)],
    [(4, e6), (15, e5), (18, e7), (25, e1)]])
private theorem product_61_left_s1 : wordMatrix [Atom.root 8 6] = atomMatrix (Atom.root 8 6) := by simp
private theorem product_61_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 6] = product_61_target := by
  rw [wordMatrix_cons, product_61_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_61_left : wordMatrix [Atom.root 8 1, Atom.root 8 6] = product_61_target := product_61_left_s0
private theorem product_61_right_s0 : wordMatrix [Atom.root 8 7] = atomMatrix (Atom.root 8 7) := by simp
private theorem product_61_right : wordMatrix [Atom.root 8 7] = product_61_target := by
  rw [product_61_right_s0]
  decide +kernel
theorem product_61 : wordGroup (product_lhs 61) = wordGroup (product_rhs 61) := by
  apply word_eq_of_matrix_eq
  exact product_61_left.trans product_61_right.symm

private def product_62_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e6), (7, e1)],
    [(1, e6), (8, e1)],
    [(9, e1)],
    [(0, e4), (10, e1)],
    [(11, e1)],
    [(3, e6), (12, e1)],
    [(13, e1)],
    [(2, e4), (14, e1)],
    [(4, e6), (15, e1)],
    [(6, e6), (16, e1)],
    [(17, e1)],
    [(4, e4), (18, e1)],
    [(9, e6), (19, e1)],
    [(20, e1)],
    [(0, e5), (7, e4), (10, e6), (21, e1)],
    [(3, e2), (13, e6), (22, e1)],
    [(11, e4), (23, e1)],
    [(17, e6), (24, e1)],
    [(4, e5), (15, e4), (18, e6), (25, e1)]])
private theorem product_62_left_s1 : wordMatrix [Atom.root 8 7] = atomMatrix (Atom.root 8 7) := by simp
private theorem product_62_left_s0 : wordMatrix [Atom.root 8 1, Atom.root 8 7] = product_62_target := by
  rw [wordMatrix_cons, product_62_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private theorem product_62_left : wordMatrix [Atom.root 8 1, Atom.root 8 7] = product_62_target := product_62_left_s0
private theorem product_62_right_s0 : wordMatrix [Atom.root 8 6] = atomMatrix (Atom.root 8 6) := by simp
private theorem product_62_right : wordMatrix [Atom.root 8 6] = product_62_target := by
  rw [product_62_right_s0]
  decide +kernel
theorem product_62 : wordGroup (product_lhs 62) = wordGroup (product_rhs 62) := by
  apply word_eq_of_matrix_eq
  exact product_62_left.trans product_62_right.symm

private def product_63_target : Mat := 1
private theorem product_63_left_s1 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private theorem product_63_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 1] = product_63_target := by
  rw [wordMatrix_cons, product_63_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_63_left : wordMatrix [Atom.root 9 1, Atom.root 9 1] = product_63_target := product_63_left_s0
private theorem product_63_right : wordMatrix [] = product_63_target := by decide +kernel
theorem product_63 : wordGroup (product_lhs 63) = wordGroup (product_rhs 63) := by
  apply word_eq_of_matrix_eq
  exact product_63_left.trans product_63_right.symm

private def product_64_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e3), (9, e1)],
    [(1, e3), (10, e1)],
    [(11, e1)],
    [(2, e3), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e7), (15, e1)],
    [(1, e7), (16, e1)],
    [(4, e3), (17, e1)],
    [(6, e3), (18, e1)],
    [(7, e3), (19, e1)],
    [(3, e7), (20, e1)],
    [(8, e3), (21, e1)],
    [(5, e7), (22, e1)],
    [(2, e5), (13, e3), (23, e1)],
    [(0, e2), (9, e7), (15, e3), (24, e1)],
    [(1, e2), (10, e7), (16, e3), (25, e1)]])
private theorem product_64_left_s1 : wordMatrix [Atom.root 9 2] = atomMatrix (Atom.root 9 2) := by simp
private theorem product_64_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 2] = product_64_target := by
  rw [wordMatrix_cons, product_64_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_64_left : wordMatrix [Atom.root 9 1, Atom.root 9 2] = product_64_target := product_64_left_s0
private theorem product_64_right_s0 : wordMatrix [Atom.root 9 3] = atomMatrix (Atom.root 9 3) := by simp
private theorem product_64_right : wordMatrix [Atom.root 9 3] = product_64_target := by
  rw [product_64_right_s0]
  decide +kernel
theorem product_64 : wordGroup (product_lhs 64) = wordGroup (product_rhs 64) := by
  apply word_eq_of_matrix_eq
  exact product_64_left.trans product_64_right.symm

private def product_65_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e2), (9, e1)],
    [(1, e2), (10, e1)],
    [(11, e1)],
    [(2, e2), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e6), (15, e1)],
    [(1, e6), (16, e1)],
    [(4, e2), (17, e1)],
    [(6, e2), (18, e1)],
    [(7, e2), (19, e1)],
    [(3, e6), (20, e1)],
    [(8, e2), (21, e1)],
    [(5, e6), (22, e1)],
    [(2, e4), (13, e2), (23, e1)],
    [(0, e7), (9, e6), (15, e2), (24, e1)],
    [(1, e7), (10, e6), (16, e2), (25, e1)]])
private theorem product_65_left_s1 : wordMatrix [Atom.root 9 3] = atomMatrix (Atom.root 9 3) := by simp
private theorem product_65_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 3] = product_65_target := by
  rw [wordMatrix_cons, product_65_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_65_left : wordMatrix [Atom.root 9 1, Atom.root 9 3] = product_65_target := product_65_left_s0
private theorem product_65_right_s0 : wordMatrix [Atom.root 9 2] = atomMatrix (Atom.root 9 2) := by simp
private theorem product_65_right : wordMatrix [Atom.root 9 2] = product_65_target := by
  rw [product_65_right_s0]
  decide +kernel
theorem product_65 : wordGroup (product_lhs 65) = wordGroup (product_rhs 65) := by
  apply word_eq_of_matrix_eq
  exact product_65_left.trans product_65_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
