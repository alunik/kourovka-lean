import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_66_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e5), (9, e1)],
    [(1, e5), (10, e1)],
    [(11, e1)],
    [(2, e5), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e3), (15, e1)],
    [(1, e3), (16, e1)],
    [(4, e5), (17, e1)],
    [(6, e5), (18, e1)],
    [(7, e5), (19, e1)],
    [(3, e3), (20, e1)],
    [(8, e5), (21, e1)],
    [(5, e3), (22, e1)],
    [(2, e7), (13, e5), (23, e1)],
    [(0, e4), (9, e3), (15, e5), (24, e1)],
    [(1, e4), (10, e3), (16, e5), (25, e1)]])
private theorem product_66_left_s1 : wordMatrix [Atom.root 9 4] = atomMatrix (Atom.root 9 4) := by simp
private theorem product_66_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 4] = product_66_target := by
  rw [wordMatrix_cons, product_66_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_66_left : wordMatrix [Atom.root 9 1, Atom.root 9 4] = product_66_target := product_66_left_s0
private theorem product_66_right_s0 : wordMatrix [Atom.root 9 5] = atomMatrix (Atom.root 9 5) := by simp
private theorem product_66_right : wordMatrix [Atom.root 9 5] = product_66_target := by
  rw [product_66_right_s0]
  decide +kernel
theorem product_66 : wordGroup (product_lhs 66) = wordGroup (product_rhs 66) := by
  apply word_eq_of_matrix_eq
  exact product_66_left.trans product_66_right.symm

private def product_67_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e4), (9, e1)],
    [(1, e4), (10, e1)],
    [(11, e1)],
    [(2, e4), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e2), (15, e1)],
    [(1, e2), (16, e1)],
    [(4, e4), (17, e1)],
    [(6, e4), (18, e1)],
    [(7, e4), (19, e1)],
    [(3, e2), (20, e1)],
    [(8, e4), (21, e1)],
    [(5, e2), (22, e1)],
    [(2, e6), (13, e4), (23, e1)],
    [(0, e3), (9, e2), (15, e4), (24, e1)],
    [(1, e3), (10, e2), (16, e4), (25, e1)]])
private theorem product_67_left_s1 : wordMatrix [Atom.root 9 5] = atomMatrix (Atom.root 9 5) := by simp
private theorem product_67_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 5] = product_67_target := by
  rw [wordMatrix_cons, product_67_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_67_left : wordMatrix [Atom.root 9 1, Atom.root 9 5] = product_67_target := product_67_left_s0
private theorem product_67_right_s0 : wordMatrix [Atom.root 9 4] = atomMatrix (Atom.root 9 4) := by simp
private theorem product_67_right : wordMatrix [Atom.root 9 4] = product_67_target := by
  rw [product_67_right_s0]
  decide +kernel
theorem product_67 : wordGroup (product_lhs 67) = wordGroup (product_rhs 67) := by
  apply word_eq_of_matrix_eq
  exact product_67_left.trans product_67_right.symm

private def product_68_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e7), (9, e1)],
    [(1, e7), (10, e1)],
    [(11, e1)],
    [(2, e7), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e5), (15, e1)],
    [(1, e5), (16, e1)],
    [(4, e7), (17, e1)],
    [(6, e7), (18, e1)],
    [(7, e7), (19, e1)],
    [(3, e5), (20, e1)],
    [(8, e7), (21, e1)],
    [(5, e5), (22, e1)],
    [(2, e3), (13, e7), (23, e1)],
    [(0, e6), (9, e5), (15, e7), (24, e1)],
    [(1, e6), (10, e5), (16, e7), (25, e1)]])
private theorem product_68_left_s1 : wordMatrix [Atom.root 9 6] = atomMatrix (Atom.root 9 6) := by simp
private theorem product_68_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 6] = product_68_target := by
  rw [wordMatrix_cons, product_68_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_68_left : wordMatrix [Atom.root 9 1, Atom.root 9 6] = product_68_target := product_68_left_s0
private theorem product_68_right_s0 : wordMatrix [Atom.root 9 7] = atomMatrix (Atom.root 9 7) := by simp
private theorem product_68_right : wordMatrix [Atom.root 9 7] = product_68_target := by
  rw [product_68_right_s0]
  decide +kernel
theorem product_68 : wordGroup (product_lhs 68) = wordGroup (product_rhs 68) := by
  apply word_eq_of_matrix_eq
  exact product_68_left.trans product_68_right.symm

private def product_69_target : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e6), (9, e1)],
    [(1, e6), (10, e1)],
    [(11, e1)],
    [(2, e6), (12, e1)],
    [(13, e1)],
    [(14, e1)],
    [(0, e4), (15, e1)],
    [(1, e4), (16, e1)],
    [(4, e6), (17, e1)],
    [(6, e6), (18, e1)],
    [(7, e6), (19, e1)],
    [(3, e4), (20, e1)],
    [(8, e6), (21, e1)],
    [(5, e4), (22, e1)],
    [(2, e2), (13, e6), (23, e1)],
    [(0, e5), (9, e4), (15, e6), (24, e1)],
    [(1, e5), (10, e4), (16, e6), (25, e1)]])
private theorem product_69_left_s1 : wordMatrix [Atom.root 9 7] = atomMatrix (Atom.root 9 7) := by simp
private theorem product_69_left_s0 : wordMatrix [Atom.root 9 1, Atom.root 9 7] = product_69_target := by
  rw [wordMatrix_cons, product_69_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private theorem product_69_left : wordMatrix [Atom.root 9 1, Atom.root 9 7] = product_69_target := product_69_left_s0
private theorem product_69_right_s0 : wordMatrix [Atom.root 9 6] = atomMatrix (Atom.root 9 6) := by simp
private theorem product_69_right : wordMatrix [Atom.root 9 6] = product_69_target := by
  rw [product_69_right_s0]
  decide +kernel
theorem product_69 : wordGroup (product_lhs 69) = wordGroup (product_rhs 69) := by
  apply word_eq_of_matrix_eq
  exact product_69_left.trans product_69_right.symm

private def product_70_target : Mat := 1
private theorem product_70_left_s1 : wordMatrix [Atom.root 10 1] = atomMatrix (Atom.root 10 1) := by simp
private theorem product_70_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 1] = product_70_target := by
  rw [wordMatrix_cons, product_70_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_70_left : wordMatrix [Atom.root 10 1, Atom.root 10 1] = product_70_target := product_70_left_s0
private theorem product_70_right : wordMatrix [] = product_70_target := by decide +kernel
theorem product_70 : wordGroup (product_lhs 70) = wordGroup (product_rhs 70) := by
  apply word_eq_of_matrix_eq
  exact product_70_left.trans product_70_right.symm

private def product_71_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e7), (14, e3), (25, e1)]])
private theorem product_71_left_s1 : wordMatrix [Atom.root 10 2] = atomMatrix (Atom.root 10 2) := by simp
private theorem product_71_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 2] = product_71_target := by
  rw [wordMatrix_cons, product_71_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_71_left : wordMatrix [Atom.root 10 1, Atom.root 10 2] = product_71_target := product_71_left_s0
private theorem product_71_right_s0 : wordMatrix [Atom.root 10 3] = atomMatrix (Atom.root 10 3) := by simp
private theorem product_71_right : wordMatrix [Atom.root 10 3] = product_71_target := by
  rw [product_71_right_s0]
  decide +kernel
theorem product_71 : wordGroup (product_lhs 71) = wordGroup (product_rhs 71) := by
  apply word_eq_of_matrix_eq
  exact product_71_left.trans product_71_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
