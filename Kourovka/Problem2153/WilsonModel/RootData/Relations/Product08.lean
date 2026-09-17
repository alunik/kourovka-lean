import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_48_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e6), (5, e1)],
    [(0, e4), (6, e1)],
    [(2, e6), (7, e1)],
    [(8, e1)],
    [(3, e6), (9, e1)],
    [(10, e1)],
    [(4, e6), (11, e1)],
    [(12, e1)],
    [(0, e5), (6, e6), (13, e1)],
    [(5, e4), (14, e1)],
    [(15, e1)],
    [(7, e4), (16, e1)],
    [(17, e1)],
    [(9, e4), (18, e1)],
    [(6, e2), (12, e6), (19, e1)],
    [(11, e4), (20, e1)],
    [(1, e3), (5, e5), (14, e6), (21, e1)],
    [(2, e3), (7, e5), (16, e6), (22, e1)],
    [(3, e3), (9, e5), (18, e6), (23, e1)],
    [(4, e3), (11, e5), (20, e6), (24, e1)],
    [(0, e7), (6, e3), (19, e4), (25, e1)]])
private theorem product_48_left_s1 : wordMatrix [Atom.root 6 7] = atomMatrix (Atom.root 6 7) := by simp
private theorem product_48_left_s0 : wordMatrix [Atom.root 6 1, Atom.root 6 7] = product_48_target := by
  rw [wordMatrix_cons, product_48_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem product_48_left : wordMatrix [Atom.root 6 1, Atom.root 6 7] = product_48_target := product_48_left_s0
private theorem product_48_right_s1 : wordMatrix [Atom.root 11 5] = atomMatrix (Atom.root 11 5) := by simp
private theorem product_48_right_s0 : wordMatrix [Atom.root 6 6, Atom.root 11 5] = product_48_target := by
  rw [wordMatrix_cons, product_48_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 6))
  decide +kernel
private theorem product_48_right : wordMatrix [Atom.root 6 6, Atom.root 11 5] = product_48_target := product_48_right_s0
theorem product_48 : wordGroup (product_lhs 48) = wordGroup (product_rhs 48) := by
  apply word_eq_of_matrix_eq
  exact product_48_left.trans product_48_right.symm

private def product_49_target : Mat := 1
private theorem product_49_left_s1 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private theorem product_49_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 1] = product_49_target := by
  rw [wordMatrix_cons, product_49_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_49_left : wordMatrix [Atom.root 7 1, Atom.root 7 1] = product_49_target := product_49_left_s0
private theorem product_49_right : wordMatrix [] = product_49_target := by decide +kernel
theorem product_49 : wordGroup (product_lhs 49) = wordGroup (product_rhs 49) := by
  apply word_eq_of_matrix_eq
  exact product_49_left.trans product_49_right.symm

private def product_50_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(17, e7), (20, e3), (25, e1)]])
private theorem product_50_left_s1 : wordMatrix [Atom.root 7 2] = atomMatrix (Atom.root 7 2) := by simp
private theorem product_50_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 2] = product_50_target := by
  rw [wordMatrix_cons, product_50_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_50_left : wordMatrix [Atom.root 7 1, Atom.root 7 2] = product_50_target := product_50_left_s0
private theorem product_50_right_s0 : wordMatrix [Atom.root 7 3] = atomMatrix (Atom.root 7 3) := by simp
private theorem product_50_right : wordMatrix [Atom.root 7 3] = product_50_target := by
  rw [product_50_right_s0]
  decide +kernel
theorem product_50 : wordGroup (product_lhs 50) = wordGroup (product_rhs 50) := by
  apply word_eq_of_matrix_eq
  exact product_50_left.trans product_50_right.symm

private def product_51_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(17, e6), (20, e2), (25, e1)]])
private theorem product_51_left_s1 : wordMatrix [Atom.root 7 3] = atomMatrix (Atom.root 7 3) := by simp
private theorem product_51_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 3] = product_51_target := by
  rw [wordMatrix_cons, product_51_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_51_left : wordMatrix [Atom.root 7 1, Atom.root 7 3] = product_51_target := product_51_left_s0
private theorem product_51_right_s0 : wordMatrix [Atom.root 7 2] = atomMatrix (Atom.root 7 2) := by simp
private theorem product_51_right : wordMatrix [Atom.root 7 2] = product_51_target := by
  rw [product_51_right_s0]
  decide +kernel
theorem product_51 : wordGroup (product_lhs 51) = wordGroup (product_rhs 51) := by
  apply word_eq_of_matrix_eq
  exact product_51_left.trans product_51_right.symm

private def product_52_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(17, e3), (20, e5), (25, e1)]])
private theorem product_52_left_s1 : wordMatrix [Atom.root 7 4] = atomMatrix (Atom.root 7 4) := by simp
private theorem product_52_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 4] = product_52_target := by
  rw [wordMatrix_cons, product_52_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_52_left : wordMatrix [Atom.root 7 1, Atom.root 7 4] = product_52_target := product_52_left_s0
private theorem product_52_right_s0 : wordMatrix [Atom.root 7 5] = atomMatrix (Atom.root 7 5) := by simp
private theorem product_52_right : wordMatrix [Atom.root 7 5] = product_52_target := by
  rw [product_52_right_s0]
  decide +kernel
theorem product_52 : wordGroup (product_lhs 52) = wordGroup (product_rhs 52) := by
  apply word_eq_of_matrix_eq
  exact product_52_left.trans product_52_right.symm

private def product_53_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(17, e2), (20, e4), (25, e1)]])
private theorem product_53_left_s1 : wordMatrix [Atom.root 7 5] = atomMatrix (Atom.root 7 5) := by simp
private theorem product_53_left_s0 : wordMatrix [Atom.root 7 1, Atom.root 7 5] = product_53_target := by
  rw [wordMatrix_cons, product_53_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private theorem product_53_left : wordMatrix [Atom.root 7 1, Atom.root 7 5] = product_53_target := product_53_left_s0
private theorem product_53_right_s0 : wordMatrix [Atom.root 7 4] = atomMatrix (Atom.root 7 4) := by simp
private theorem product_53_right : wordMatrix [Atom.root 7 4] = product_53_target := by
  rw [product_53_right_s0]
  decide +kernel
theorem product_53 : wordGroup (product_lhs 53) = wordGroup (product_rhs 53) := by
  apply word_eq_of_matrix_eq
  exact product_53_left.trans product_53_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
