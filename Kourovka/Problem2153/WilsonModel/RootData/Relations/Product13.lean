import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_78_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e5), (6, e7), (12, e3), (25, e1)]])
private theorem product_78_left_s1 : wordMatrix [Atom.root 11 2] = atomMatrix (Atom.root 11 2) := by simp
private theorem product_78_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 2] = product_78_target := by
  rw [wordMatrix_cons, product_78_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_78_left : wordMatrix [Atom.root 11 1, Atom.root 11 2] = product_78_target := product_78_left_s0
private theorem product_78_right_s0 : wordMatrix [Atom.root 11 3] = atomMatrix (Atom.root 11 3) := by simp
private theorem product_78_right : wordMatrix [Atom.root 11 3] = product_78_target := by
  rw [product_78_right_s0]
  decide +kernel
theorem product_78 : wordGroup (product_lhs 78) = wordGroup (product_rhs 78) := by
  apply word_eq_of_matrix_eq
  exact product_78_left.trans product_78_right.symm

private def product_79_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e4), (6, e6), (12, e2), (25, e1)]])
private theorem product_79_left_s1 : wordMatrix [Atom.root 11 3] = atomMatrix (Atom.root 11 3) := by simp
private theorem product_79_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 3] = product_79_target := by
  rw [wordMatrix_cons, product_79_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_79_left : wordMatrix [Atom.root 11 1, Atom.root 11 3] = product_79_target := product_79_left_s0
private theorem product_79_right_s0 : wordMatrix [Atom.root 11 2] = atomMatrix (Atom.root 11 2) := by simp
private theorem product_79_right : wordMatrix [Atom.root 11 2] = product_79_target := by
  rw [product_79_right_s0]
  decide +kernel
theorem product_79 : wordGroup (product_lhs 79) = wordGroup (product_rhs 79) := by
  apply word_eq_of_matrix_eq
  exact product_79_left.trans product_79_right.symm

private def product_80_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e7), (6, e3), (12, e5), (25, e1)]])
private theorem product_80_left_s1 : wordMatrix [Atom.root 11 4] = atomMatrix (Atom.root 11 4) := by simp
private theorem product_80_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 4] = product_80_target := by
  rw [wordMatrix_cons, product_80_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_80_left : wordMatrix [Atom.root 11 1, Atom.root 11 4] = product_80_target := product_80_left_s0
private theorem product_80_right_s0 : wordMatrix [Atom.root 11 5] = atomMatrix (Atom.root 11 5) := by simp
private theorem product_80_right : wordMatrix [Atom.root 11 5] = product_80_target := by
  rw [product_80_right_s0]
  decide +kernel
theorem product_80 : wordGroup (product_lhs 80) = wordGroup (product_rhs 80) := by
  apply word_eq_of_matrix_eq
  exact product_80_left.trans product_80_right.symm

private def product_81_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e6), (6, e2), (12, e4), (25, e1)]])
private theorem product_81_left_s1 : wordMatrix [Atom.root 11 5] = atomMatrix (Atom.root 11 5) := by simp
private theorem product_81_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 5] = product_81_target := by
  rw [wordMatrix_cons, product_81_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_81_left : wordMatrix [Atom.root 11 1, Atom.root 11 5] = product_81_target := product_81_left_s0
private theorem product_81_right_s0 : wordMatrix [Atom.root 11 4] = atomMatrix (Atom.root 11 4) := by simp
private theorem product_81_right : wordMatrix [Atom.root 11 4] = product_81_target := by
  rw [product_81_right_s0]
  decide +kernel
theorem product_81 : wordGroup (product_lhs 81) = wordGroup (product_rhs 81) := by
  apply word_eq_of_matrix_eq
  exact product_81_left.trans product_81_right.symm

private def product_82_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e3), (6, e5), (12, e7), (25, e1)]])
private theorem product_82_left_s1 : wordMatrix [Atom.root 11 6] = atomMatrix (Atom.root 11 6) := by simp
private theorem product_82_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 6] = product_82_target := by
  rw [wordMatrix_cons, product_82_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_82_left : wordMatrix [Atom.root 11 1, Atom.root 11 6] = product_82_target := product_82_left_s0
private theorem product_82_right_s0 : wordMatrix [Atom.root 11 7] = atomMatrix (Atom.root 11 7) := by simp
private theorem product_82_right : wordMatrix [Atom.root 11 7] = product_82_target := by
  rw [product_82_right_s0]
  decide +kernel
theorem product_82 : wordGroup (product_lhs 82) = wordGroup (product_rhs 82) := by
  apply word_eq_of_matrix_eq
  exact product_82_left.trans product_82_right.symm

private def product_83_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e2), (6, e4), (12, e6), (25, e1)]])
private theorem product_83_left_s1 : wordMatrix [Atom.root 11 7] = atomMatrix (Atom.root 11 7) := by simp
private theorem product_83_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 7] = product_83_target := by
  rw [wordMatrix_cons, product_83_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_83_left : wordMatrix [Atom.root 11 1, Atom.root 11 7] = product_83_target := product_83_left_s0
private theorem product_83_right_s0 : wordMatrix [Atom.root 11 6] = atomMatrix (Atom.root 11 6) := by simp
private theorem product_83_right : wordMatrix [Atom.root 11 6] = product_83_target := by
  rw [product_83_right_s0]
  decide +kernel
theorem product_83 : wordGroup (product_lhs 83) = wordGroup (product_rhs 83) := by
  apply word_eq_of_matrix_eq
  exact product_83_left.trans product_83_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
