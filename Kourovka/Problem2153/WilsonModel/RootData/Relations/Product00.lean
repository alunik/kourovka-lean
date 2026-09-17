import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_0_target : Mat := 1
private theorem product_0_left_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem product_0_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 1] = product_0_target := by
  rw [wordMatrix_cons, product_0_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_0_left : wordMatrix [Atom.root 0 1, Atom.root 0 1] = product_0_target := product_0_left_s0
private theorem product_0_right : wordMatrix [] = product_0_target := by decide +kernel
theorem product_0 : wordGroup (product_lhs 0) = wordGroup (product_rhs 0) := by
  apply word_eq_of_matrix_eq
  exact product_0_left.trans product_0_right.symm

private def product_1_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e3), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e7), (5, e1)],
    [(4, e3), (6, e1)],
    [(4, e7), (7, e1)],
    [(4, e2), (6, e7), (7, e3), (8, e1)],
    [(9, e1)],
    [(9, e3), (10, e1)],
    [(11, e1)],
    [(11, e3), (12, e1)],
    [(13, e1)],
    [(11, e5), (13, e3), (14, e1)],
    [(15, e1)],
    [(15, e3), (16, e1)],
    [(17, e1)],
    [(17, e3), (18, e1)],
    [(17, e7), (19, e1)],
    [(20, e1)],
    [(17, e2), (18, e7), (19, e3), (21, e1)],
    [(20, e7), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e3), (25, e1)]])
private theorem product_1_left_s1 : wordMatrix [Atom.root 0 2] = atomMatrix (Atom.root 0 2) := by simp
private theorem product_1_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 2] = product_1_target := by
  rw [wordMatrix_cons, product_1_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_1_left : wordMatrix [Atom.root 0 1, Atom.root 0 2] = product_1_target := product_1_left_s0
private theorem product_1_right_s0 : wordMatrix [Atom.root 0 3] = atomMatrix (Atom.root 0 3) := by simp
private theorem product_1_right : wordMatrix [Atom.root 0 3] = product_1_target := by
  rw [product_1_right_s0]
  decide +kernel
theorem product_1 : wordGroup (product_lhs 1) = wordGroup (product_rhs 1) := by
  apply word_eq_of_matrix_eq
  exact product_1_left.trans product_1_right.symm

private def product_2_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e2), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e6), (5, e1)],
    [(4, e2), (6, e1)],
    [(4, e6), (7, e1)],
    [(4, e7), (6, e6), (7, e2), (8, e1)],
    [(9, e1)],
    [(9, e2), (10, e1)],
    [(11, e1)],
    [(11, e2), (12, e1)],
    [(13, e1)],
    [(11, e4), (13, e2), (14, e1)],
    [(15, e1)],
    [(15, e2), (16, e1)],
    [(17, e1)],
    [(17, e2), (18, e1)],
    [(17, e6), (19, e1)],
    [(20, e1)],
    [(17, e7), (18, e6), (19, e2), (21, e1)],
    [(20, e6), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e2), (25, e1)]])
private theorem product_2_left_s1 : wordMatrix [Atom.root 0 3] = atomMatrix (Atom.root 0 3) := by simp
private theorem product_2_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 3] = product_2_target := by
  rw [wordMatrix_cons, product_2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_2_left : wordMatrix [Atom.root 0 1, Atom.root 0 3] = product_2_target := product_2_left_s0
private theorem product_2_right_s0 : wordMatrix [Atom.root 0 2] = atomMatrix (Atom.root 0 2) := by simp
private theorem product_2_right : wordMatrix [Atom.root 0 2] = product_2_target := by
  rw [product_2_right_s0]
  decide +kernel
theorem product_2 : wordGroup (product_lhs 2) = wordGroup (product_rhs 2) := by
  apply word_eq_of_matrix_eq
  exact product_2_left.trans product_2_right.symm

private def product_3_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e5), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e3), (5, e1)],
    [(4, e5), (6, e1)],
    [(4, e3), (7, e1)],
    [(4, e4), (6, e3), (7, e5), (8, e1)],
    [(9, e1)],
    [(9, e5), (10, e1)],
    [(11, e1)],
    [(11, e5), (12, e1)],
    [(13, e1)],
    [(11, e7), (13, e5), (14, e1)],
    [(15, e1)],
    [(15, e5), (16, e1)],
    [(17, e1)],
    [(17, e5), (18, e1)],
    [(17, e3), (19, e1)],
    [(20, e1)],
    [(17, e4), (18, e3), (19, e5), (21, e1)],
    [(20, e3), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e5), (25, e1)]])
private theorem product_3_left_s1 : wordMatrix [Atom.root 0 4] = atomMatrix (Atom.root 0 4) := by simp
private theorem product_3_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 4] = product_3_target := by
  rw [wordMatrix_cons, product_3_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_3_left : wordMatrix [Atom.root 0 1, Atom.root 0 4] = product_3_target := product_3_left_s0
private theorem product_3_right_s0 : wordMatrix [Atom.root 0 5] = atomMatrix (Atom.root 0 5) := by simp
private theorem product_3_right : wordMatrix [Atom.root 0 5] = product_3_target := by
  rw [product_3_right_s0]
  decide +kernel
theorem product_3 : wordGroup (product_lhs 3) = wordGroup (product_rhs 3) := by
  apply word_eq_of_matrix_eq
  exact product_3_left.trans product_3_right.symm

private def product_4_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e4), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e2), (5, e1)],
    [(4, e4), (6, e1)],
    [(4, e2), (7, e1)],
    [(4, e3), (6, e2), (7, e4), (8, e1)],
    [(9, e1)],
    [(9, e4), (10, e1)],
    [(11, e1)],
    [(11, e4), (12, e1)],
    [(13, e1)],
    [(11, e6), (13, e4), (14, e1)],
    [(15, e1)],
    [(15, e4), (16, e1)],
    [(17, e1)],
    [(17, e4), (18, e1)],
    [(17, e2), (19, e1)],
    [(20, e1)],
    [(17, e3), (18, e2), (19, e4), (21, e1)],
    [(20, e2), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e4), (25, e1)]])
private theorem product_4_left_s1 : wordMatrix [Atom.root 0 5] = atomMatrix (Atom.root 0 5) := by simp
private theorem product_4_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 5] = product_4_target := by
  rw [wordMatrix_cons, product_4_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_4_left : wordMatrix [Atom.root 0 1, Atom.root 0 5] = product_4_target := product_4_left_s0
private theorem product_4_right_s0 : wordMatrix [Atom.root 0 4] = atomMatrix (Atom.root 0 4) := by simp
private theorem product_4_right : wordMatrix [Atom.root 0 4] = product_4_target := by
  rw [product_4_right_s0]
  decide +kernel
theorem product_4 : wordGroup (product_lhs 4) = wordGroup (product_rhs 4) := by
  apply word_eq_of_matrix_eq
  exact product_4_left.trans product_4_right.symm

private def product_5_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e7), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e5), (5, e1)],
    [(4, e7), (6, e1)],
    [(4, e5), (7, e1)],
    [(4, e6), (6, e5), (7, e7), (8, e1)],
    [(9, e1)],
    [(9, e7), (10, e1)],
    [(11, e1)],
    [(11, e7), (12, e1)],
    [(13, e1)],
    [(11, e3), (13, e7), (14, e1)],
    [(15, e1)],
    [(15, e7), (16, e1)],
    [(17, e1)],
    [(17, e7), (18, e1)],
    [(17, e5), (19, e1)],
    [(20, e1)],
    [(17, e6), (18, e5), (19, e7), (21, e1)],
    [(20, e5), (22, e1)],
    [(23, e1)],
    [(24, e1)],
    [(24, e7), (25, e1)]])
private theorem product_5_left_s1 : wordMatrix [Atom.root 0 6] = atomMatrix (Atom.root 0 6) := by simp
private theorem product_5_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 0 6] = product_5_target := by
  rw [wordMatrix_cons, product_5_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem product_5_left : wordMatrix [Atom.root 0 1, Atom.root 0 6] = product_5_target := product_5_left_s0
private theorem product_5_right_s0 : wordMatrix [Atom.root 0 7] = atomMatrix (Atom.root 0 7) := by simp
private theorem product_5_right : wordMatrix [Atom.root 0 7] = product_5_target := by
  rw [product_5_right_s0]
  decide +kernel
theorem product_5 : wordGroup (product_lhs 5) = wordGroup (product_rhs 5) := by
  apply word_eq_of_matrix_eq
  exact product_5_left.trans product_5_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
