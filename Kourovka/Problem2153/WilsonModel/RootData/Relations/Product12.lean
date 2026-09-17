import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def product_72_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e6), (14, e2), (25, e1)]])
private theorem product_72_left_s1 : wordMatrix [Atom.root 10 3] = atomMatrix (Atom.root 10 3) := by simp
private theorem product_72_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 3] = product_72_target := by
  rw [wordMatrix_cons, product_72_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_72_left : wordMatrix [Atom.root 10 1, Atom.root 10 3] = product_72_target := product_72_left_s0
private theorem product_72_right_s0 : wordMatrix [Atom.root 10 2] = atomMatrix (Atom.root 10 2) := by simp
private theorem product_72_right : wordMatrix [Atom.root 10 2] = product_72_target := by
  rw [product_72_right_s0]
  decide +kernel
theorem product_72 : wordGroup (product_lhs 72) = wordGroup (product_rhs 72) := by
  apply word_eq_of_matrix_eq
  exact product_72_left.trans product_72_right.symm

private def product_73_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e3), (14, e5), (25, e1)]])
private theorem product_73_left_s1 : wordMatrix [Atom.root 10 4] = atomMatrix (Atom.root 10 4) := by simp
private theorem product_73_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 4] = product_73_target := by
  rw [wordMatrix_cons, product_73_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_73_left : wordMatrix [Atom.root 10 1, Atom.root 10 4] = product_73_target := product_73_left_s0
private theorem product_73_right_s0 : wordMatrix [Atom.root 10 5] = atomMatrix (Atom.root 10 5) := by simp
private theorem product_73_right : wordMatrix [Atom.root 10 5] = product_73_target := by
  rw [product_73_right_s0]
  decide +kernel
theorem product_73 : wordGroup (product_lhs 73) = wordGroup (product_rhs 73) := by
  apply word_eq_of_matrix_eq
  exact product_73_left.trans product_73_right.symm

private def product_74_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e2), (14, e4), (25, e1)]])
private theorem product_74_left_s1 : wordMatrix [Atom.root 10 5] = atomMatrix (Atom.root 10 5) := by simp
private theorem product_74_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 5] = product_74_target := by
  rw [wordMatrix_cons, product_74_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_74_left : wordMatrix [Atom.root 10 1, Atom.root 10 5] = product_74_target := product_74_left_s0
private theorem product_74_right_s0 : wordMatrix [Atom.root 10 4] = atomMatrix (Atom.root 10 4) := by simp
private theorem product_74_right : wordMatrix [Atom.root 10 4] = product_74_target := by
  rw [product_74_right_s0]
  decide +kernel
theorem product_74 : wordGroup (product_lhs 74) = wordGroup (product_rhs 74) := by
  apply word_eq_of_matrix_eq
  exact product_74_left.trans product_74_right.symm

private def product_75_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e5), (14, e7), (25, e1)]])
private theorem product_75_left_s1 : wordMatrix [Atom.root 10 6] = atomMatrix (Atom.root 10 6) := by simp
private theorem product_75_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 6] = product_75_target := by
  rw [wordMatrix_cons, product_75_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_75_left : wordMatrix [Atom.root 10 1, Atom.root 10 6] = product_75_target := product_75_left_s0
private theorem product_75_right_s0 : wordMatrix [Atom.root 10 7] = atomMatrix (Atom.root 10 7) := by simp
private theorem product_75_right : wordMatrix [Atom.root 10 7] = product_75_target := by
  rw [product_75_right_s0]
  decide +kernel
theorem product_75 : wordGroup (product_lhs 75) = wordGroup (product_rhs 75) := by
  apply word_eq_of_matrix_eq
  exact product_75_left.trans product_75_right.symm

private def product_76_target : Mat := Sparse.eval (![[(0, e1)],
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
    [(8, e4), (14, e6), (25, e1)]])
private theorem product_76_left_s1 : wordMatrix [Atom.root 10 7] = atomMatrix (Atom.root 10 7) := by simp
private theorem product_76_left_s0 : wordMatrix [Atom.root 10 1, Atom.root 10 7] = product_76_target := by
  rw [wordMatrix_cons, product_76_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private theorem product_76_left : wordMatrix [Atom.root 10 1, Atom.root 10 7] = product_76_target := product_76_left_s0
private theorem product_76_right_s0 : wordMatrix [Atom.root 10 6] = atomMatrix (Atom.root 10 6) := by simp
private theorem product_76_right : wordMatrix [Atom.root 10 6] = product_76_target := by
  rw [product_76_right_s0]
  decide +kernel
theorem product_76 : wordGroup (product_lhs 76) = wordGroup (product_rhs 76) := by
  apply word_eq_of_matrix_eq
  exact product_76_left.trans product_76_right.symm

private def product_77_target : Mat := 1
private theorem product_77_left_s1 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private theorem product_77_left_s0 : wordMatrix [Atom.root 11 1, Atom.root 11 1] = product_77_target := by
  rw [wordMatrix_cons, product_77_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 1))
  decide +kernel
private theorem product_77_left : wordMatrix [Atom.root 11 1, Atom.root 11 1] = product_77_target := product_77_left_s0
private theorem product_77_right : wordMatrix [] = product_77_target := by decide +kernel
theorem product_77 : wordGroup (product_lhs 77) = wordGroup (product_rhs 77) := by
  apply word_eq_of_matrix_eq
  exact product_77_left.trans product_77_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
