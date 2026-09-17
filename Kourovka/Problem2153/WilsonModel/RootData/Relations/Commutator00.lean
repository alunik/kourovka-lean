import Kourovka.Problem2153.WilsonModel.RootData.Relations.Metadata
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
open Field8 F8
private def commutator_0_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(1, e1), (2, e1)],
    [(1, e1), (2, e1), (3, e1)],
    [(1, e1), (3, e1), (4, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (7, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (6, e1), (7, e1), (8, e1)],
    [(5, e1), (7, e1), (9, e1)],
    [(5, e1), (7, e1), (8, e1), (9, e1), (10, e1)],
    [(5, e1), (9, e1), (11, e1)],
    [(5, e1), (9, e1), (11, e1), (12, e1)],
    [(10, e1), (13, e1)],
    [(5, e1), (9, e1), (10, e1), (11, e1), (13, e1), (14, e1)],
    [(8, e1), (10, e1), (12, e1), (15, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (15, e1), (16, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1)],
    [(8, e1), (12, e1), (14, e1), (15, e1), (16, e1), (17, e1), (18, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1), (19, e1)],
    [(14, e1), (18, e1), (20, e1)],
    [(8, e1), (12, e1), (14, e1), (15, e1), (16, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(14, e1), (18, e1), (20, e1), (21, e1), (22, e1)],
    [(21, e1), (22, e1), (23, e1)],
    [(21, e1), (23, e1), (24, e1)],
    [(21, e1), (23, e1), (24, e1), (25, e1)]])
private theorem commutator_0_left_s1 : wordMatrix [Atom.root 1 1] = atomMatrix (Atom.root 1 1) := by simp
private theorem commutator_0_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 1 1] = commutator_0_target := by
  rw [wordMatrix_cons, commutator_0_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_0_left : wordMatrix [Atom.root 0 1, Atom.root 1 1] = commutator_0_target := commutator_0_left_s0
private theorem commutator_0_right_s8 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_0_right_m7 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(7, e1)],
    [(8, e1)],
    [(0, e1), (9, e1)],
    [(1, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (14, e1)],
    [(0, e1), (15, e1)],
    [(1, e1), (2, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(3, e1), (6, e1), (18, e1)],
    [(0, e1), (7, e1), (19, e1)],
    [(3, e1), (4, e1), (20, e1)],
    [(1, e1), (5, e1), (8, e1), (21, e1)],
    [(2, e1), (5, e1), (7, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (9, e1), (13, e1), (23, e1)],
    [(0, e1), (4, e1), (9, e1), (11, e1), (15, e1), (24, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1), (10, e1), (12, e1), (16, e1), (25, e1)]])
private theorem commutator_0_right_s7 : wordMatrix [Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m7 := by
  rw [wordMatrix_cons, commutator_0_right_s8]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 9 1))
  decide +kernel
private def commutator_0_right_m6 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(0, e1), (1, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (3, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(1, e1), (2, e1), (6, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(3, e1), (4, e1), (6, e1), (18, e1)],
    [(7, e1), (9, e1), (19, e1)],
    [(3, e1), (4, e1), (20, e1)],
    [(0, e1), (5, e1), (7, e1), (8, e1), (10, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (7, e1), (13, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (9, e1), (11, e1), (13, e1), (23, e1)],
    [(0, e1), (9, e1), (11, e1), (15, e1), (17, e1), (24, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1), (10, e1), (12, e1), (15, e1), (16, e1), (18, e1), (25, e1)]])
private theorem commutator_0_right_s6 : wordMatrix [Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m6 := by
  rw [wordMatrix_cons, commutator_0_right_s7]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_0_right_m5 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(0, e1), (1, e1), (3, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (3, e1), (4, e1), (12, e1)],
    [(0, e1), (4, e1), (13, e1)],
    [(1, e1), (2, e1), (3, e1), (6, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(3, e1), (4, e1), (6, e1), (18, e1)],
    [(7, e1), (9, e1), (11, e1), (19, e1)],
    [(3, e1), (4, e1), (20, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (5, e1), (7, e1), (8, e1), (9, e1), (10, e1), (12, e1), (13, e1), (21, e1)],
    [(2, e1), (3, e1), (4, e1), (5, e1), (7, e1), (11, e1), (13, e1), (15, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (9, e1), (11, e1), (13, e1), (17, e1), (23, e1)],
    [(0, e1), (9, e1), (11, e1), (15, e1), (17, e1), (24, e1)],
    [(1, e1), (2, e1), (4, e1), (10, e1), (12, e1), (15, e1), (16, e1), (17, e1), (18, e1), (20, e1), (25, e1)]])
private theorem commutator_0_right_s5 : wordMatrix [Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m5 := by
  rw [wordMatrix_cons, commutator_0_right_s6]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private def commutator_0_right_m4 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(0, e1), (3, e1), (9, e1)],
    [(0, e1), (1, e1), (3, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(2, e1), (3, e1), (4, e1), (12, e1)],
    [(0, e1), (4, e1), (6, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (7, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(0, e1), (4, e1), (6, e1), (9, e1), (18, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (6, e1), (7, e1), (9, e1), (11, e1), (12, e1), (19, e1)],
    [(3, e1), (11, e1), (20, e1)],
    [(0, e1), (4, e1), (5, e1), (6, e1), (7, e1), (8, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (6, e1), (7, e1), (11, e1), (13, e1), (15, e1), (16, e1), (22, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (9, e1), (11, e1), (13, e1), (17, e1), (18, e1), (23, e1)],
    [(0, e1), (3, e1), (9, e1), (11, e1), (15, e1), (17, e1), (20, e1), (24, e1)],
    [(0, e1), (1, e1), (3, e1), (7, e1), (9, e1), (10, e1), (11, e1), (15, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (25, e1)]])
private theorem commutator_0_right_s4 : wordMatrix [Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m4 := by
  rw [wordMatrix_cons, commutator_0_right_s5]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private def commutator_0_right_m3 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (1, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(0, e1), (1, e1), (3, e1), (9, e1)],
    [(0, e1), (1, e1), (3, e1), (10, e1)],
    [(2, e1), (4, e1), (11, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (4, e1), (5, e1), (12, e1)],
    [(0, e1), (4, e1), (6, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (14, e1)],
    [(2, e1), (4, e1), (7, e1), (15, e1)],
    [(2, e1), (4, e1), (6, e1), (7, e1), (8, e1), (16, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (10, e1), (18, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (7, e1), (8, e1), (9, e1), (11, e1), (12, e1), (19, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (6, e1), (11, e1), (13, e1), (20, e1)],
    [(0, e1), (4, e1), (5, e1), (6, e1), (7, e1), (8, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (6, e1), (7, e1), (11, e1), (13, e1), (15, e1), (16, e1), (22, e1)],
    [(5, e1), (9, e1), (11, e1), (13, e1), (14, e1), (17, e1), (18, e1), (23, e1)],
    [(8, e1), (12, e1), (15, e1), (16, e1), (17, e1), (19, e1), (20, e1), (24, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (6, e1), (8, e1), (11, e1), (12, e1), (13, e1), (14, e1), (15, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (21, e1), (25, e1)]])
private theorem commutator_0_right_s3 : wordMatrix [Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m3 := by
  rw [wordMatrix_cons, commutator_0_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private def commutator_0_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (2, e1), (5, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(0, e1), (2, e1), (5, e1), (8, e1)],
    [(1, e1), (3, e1), (4, e1), (9, e1)],
    [(6, e1), (10, e1)],
    [(2, e1), (4, e1), (11, e1)],
    [(2, e1), (4, e1), (5, e1), (9, e1), (12, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (13, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1), (6, e1), (10, e1), (14, e1)],
    [(7, e1), (11, e1), (15, e1)],
    [(5, e1), (7, e1), (8, e1), (9, e1), (12, e1), (13, e1), (16, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (10, e1), (18, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (8, e1), (9, e1), (12, e1), (15, e1), (19, e1)],
    [(5, e1), (9, e1), (11, e1), (13, e1), (17, e1), (20, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (10, e1), (14, e1), (16, e1), (21, e1)],
    [(5, e1), (8, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (16, e1), (19, e1), (22, e1)],
    [(14, e1), (18, e1), (20, e1), (23, e1)],
    [(8, e1), (12, e1), (15, e1), (16, e1), (17, e1), (19, e1), (20, e1), (24, e1)],
    [(8, e1), (12, e1), (15, e1), (16, e1), (17, e1), (19, e1), (20, e1), (21, e1), (23, e1), (25, e1)]])
private theorem commutator_0_right_s2 : wordMatrix [Atom.root 2 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m2 := by
  rw [wordMatrix_cons, commutator_0_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private def commutator_0_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (2, e1), (3, e1), (5, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1)],
    [(2, e1), (4, e1), (7, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (6, e1), (7, e1), (8, e1)],
    [(1, e1), (3, e1), (4, e1), (9, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (10, e1)],
    [(2, e1), (4, e1), (11, e1)],
    [(5, e1), (9, e1), (11, e1), (12, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (13, e1)],
    [(5, e1), (9, e1), (10, e1), (11, e1), (13, e1), (14, e1)],
    [(7, e1), (11, e1), (15, e1)],
    [(5, e1), (8, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (16, e1)],
    [(1, e1), (3, e1), (4, e1), (6, e1), (9, e1), (17, e1)],
    [(10, e1), (17, e1), (18, e1)],
    [(8, e1), (12, e1), (15, e1), (17, e1), (19, e1)],
    [(5, e1), (9, e1), (11, e1), (13, e1), (17, e1), (20, e1)],
    [(8, e1), (12, e1), (14, e1), (15, e1), (16, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(8, e1), (12, e1), (15, e1), (16, e1), (17, e1), (19, e1), (20, e1), (22, e1)],
    [(14, e1), (18, e1), (20, e1), (23, e1)],
    [(8, e1), (12, e1), (15, e1), (16, e1), (17, e1), (19, e1), (20, e1), (24, e1)],
    [(21, e1), (23, e1), (24, e1), (25, e1)]])
private theorem commutator_0_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 2 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_right_m1 := by
  rw [wordMatrix_cons, commutator_0_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_0_right_s0 : wordMatrix [Atom.root 1 1, Atom.root 0 1, Atom.root 2 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_target := by
  rw [wordMatrix_cons, commutator_0_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 1 1))
  decide +kernel
private theorem commutator_0_right : wordMatrix [Atom.root 1 1, Atom.root 0 1, Atom.root 2 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 9 1, Atom.root 11 1] = commutator_0_target := commutator_0_right_s0
theorem commutator_0 : wordGroup (commutator_lhs 0) = wordGroup (commutator_rhs 0) := by
  apply word_eq_of_matrix_eq
  exact commutator_0_left.trans commutator_0_right.symm

private def commutator_1_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(0, e1), (2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1)],
    [(3, e1), (4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(0, e1), (3, e1), (4, e1), (5, e1), (6, e1), (7, e1), (8, e1)],
    [(4, e1), (9, e1)],
    [(3, e1), (4, e1), (6, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(9, e1), (11, e1), (12, e1)],
    [(9, e1), (13, e1)],
    [(3, e1), (9, e1), (10, e1), (11, e1), (13, e1), (14, e1)],
    [(11, e1), (15, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(17, e1), (18, e1)],
    [(11, e1), (15, e1), (17, e1), (19, e1)],
    [(17, e1), (20, e1)],
    [(4, e1), (11, e1), (12, e1), (13, e1), (15, e1), (16, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(11, e1), (17, e1), (19, e1), (20, e1), (22, e1)],
    [(17, e1), (20, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (23, e1), (24, e1), (25, e1)]])
private theorem commutator_1_left_s1 : wordMatrix [Atom.root 2 1] = atomMatrix (Atom.root 2 1) := by simp
private theorem commutator_1_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 2 1] = commutator_1_target := by
  rw [wordMatrix_cons, commutator_1_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_1_left : wordMatrix [Atom.root 0 1, Atom.root 2 1] = commutator_1_target := commutator_1_left_s0
private theorem commutator_1_right_s1 : wordMatrix [Atom.root 0 1] = atomMatrix (Atom.root 0 1) := by simp
private theorem commutator_1_right_s0 : wordMatrix [Atom.root 2 1, Atom.root 0 1] = commutator_1_target := by
  rw [wordMatrix_cons, commutator_1_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 2 1))
  decide +kernel
private theorem commutator_1_right : wordMatrix [Atom.root 2 1, Atom.root 0 1] = commutator_1_target := commutator_1_right_s0
theorem commutator_1 : wordGroup (commutator_lhs 1) = wordGroup (commutator_rhs 1) := by
  apply word_eq_of_matrix_eq
  exact commutator_1_left.trans commutator_1_right.symm

private def commutator_2_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(1, e1), (3, e1)],
    [(1, e1), (2, e1), (4, e1)],
    [(1, e1), (3, e1), (5, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1)],
    [(1, e1), (2, e1), (4, e1), (7, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(5, e1), (9, e1)],
    [(5, e1), (9, e1), (10, e1)],
    [(5, e1), (7, e1), (11, e1)],
    [(5, e1), (7, e1), (11, e1), (12, e1)],
    [(8, e1), (13, e1)],
    [(5, e1), (7, e1), (8, e1), (11, e1), (13, e1), (14, e1)],
    [(8, e1), (15, e1)],
    [(8, e1), (15, e1), (16, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (17, e1), (18, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1), (19, e1)],
    [(14, e1), (16, e1), (20, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(14, e1), (16, e1), (20, e1), (22, e1)],
    [(21, e1), (23, e1)],
    [(21, e1), (22, e1), (24, e1)],
    [(21, e1), (22, e1), (24, e1), (25, e1)]])
private theorem commutator_2_left_s1 : wordMatrix [Atom.root 3 1] = atomMatrix (Atom.root 3 1) := by simp
private theorem commutator_2_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 3 1] = commutator_2_target := by
  rw [wordMatrix_cons, commutator_2_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_2_left : wordMatrix [Atom.root 0 1, Atom.root 3 1] = commutator_2_target := commutator_2_left_s0
private theorem commutator_2_right_s8 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_2_right_m7 : Mat := Sparse.eval (![[(0, e1)],
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
    [(0, e1), (1, e1), (6, e1), (8, e1), (12, e1), (14, e1), (25, e1)]])
private theorem commutator_2_right_s7 : wordMatrix [Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m7 := by
  rw [wordMatrix_cons, commutator_2_right_s8]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 10 1))
  decide +kernel
private def commutator_2_right_m6 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (3, e1), (12, e1)],
    [(0, e1), (1, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(2, e1), (4, e1), (15, e1)],
    [(2, e1), (6, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (18, e1)],
    [(0, e1), (5, e1), (9, e1), (19, e1)],
    [(2, e1), (4, e1), (6, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (7, e1), (8, e1), (13, e1), (22, e1)],
    [(0, e1), (3, e1), (5, e1), (9, e1), (10, e1), (11, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (7, e1), (11, e1), (12, e1), (13, e1), (17, e1), (24, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (6, e1), (8, e1), (12, e1), (14, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_2_right_s6 : wordMatrix [Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m6 := by
  rw [wordMatrix_cons, commutator_2_right_s7]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_2_right_m5 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (10, e1)],
    [(0, e1), (11, e1)],
    [(1, e1), (3, e1), (4, e1), (12, e1)],
    [(0, e1), (1, e1), (4, e1), (13, e1)],
    [(1, e1), (2, e1), (3, e1), (6, e1), (14, e1)],
    [(2, e1), (4, e1), (15, e1)],
    [(2, e1), (4, e1), (6, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (3, e1), (4, e1), (18, e1)],
    [(5, e1), (9, e1), (11, e1), (19, e1)],
    [(2, e1), (4, e1), (6, e1), (20, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (21, e1)],
    [(1, e1), (3, e1), (4, e1), (7, e1), (8, e1), (11, e1), (13, e1), (15, e1), (22, e1)],
    [(5, e1), (9, e1), (10, e1), (11, e1), (17, e1), (23, e1)],
    [(1, e1), (3, e1), (4, e1), (7, e1), (11, e1), (12, e1), (13, e1), (17, e1), (24, e1)],
    [(8, e1), (12, e1), (14, e1), (15, e1), (17, e1), (18, e1), (20, e1), (25, e1)]])
private theorem commutator_2_right_s5 : wordMatrix [Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m5 := by
  rw [wordMatrix_cons, commutator_2_right_s6]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private def commutator_2_right_m4 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(3, e1), (9, e1)],
    [(0, e1), (3, e1), (10, e1)],
    [(0, e1), (4, e1), (11, e1)],
    [(1, e1), (3, e1), (4, e1), (12, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (14, e1)],
    [(2, e1), (4, e1), (15, e1)],
    [(0, e1), (4, e1), (6, e1), (7, e1), (16, e1)],
    [(0, e1), (3, e1), (17, e1)],
    [(1, e1), (4, e1), (9, e1), (18, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (5, e1), (6, e1), (9, e1), (11, e1), (12, e1), (19, e1)],
    [(0, e1), (2, e1), (6, e1), (11, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(1, e1), (3, e1), (6, e1), (7, e1), (8, e1), (11, e1), (13, e1), (15, e1), (16, e1), (22, e1)],
    [(1, e1), (4, e1), (5, e1), (9, e1), (10, e1), (11, e1), (17, e1), (18, e1), (23, e1)],
    [(1, e1), (2, e1), (3, e1), (4, e1), (6, e1), (7, e1), (11, e1), (12, e1), (13, e1), (17, e1), (20, e1), (24, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (5, e1), (8, e1), (9, e1), (11, e1), (14, e1), (15, e1), (17, e1), (18, e1), (19, e1), (20, e1), (25, e1)]])
private theorem commutator_2_right_s4 : wordMatrix [Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m4 := by
  rw [wordMatrix_cons, commutator_2_right_s5]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private def commutator_2_right_m3 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (1, e1), (6, e1)],
    [(0, e1), (2, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(0, e1), (3, e1), (10, e1)],
    [(0, e1), (2, e1), (4, e1), (11, e1)],
    [(0, e1), (3, e1), (4, e1), (5, e1), (12, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (13, e1)],
    [(0, e1), (2, e1), (3, e1), (5, e1), (6, e1), (14, e1)],
    [(0, e1), (4, e1), (7, e1), (15, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(0, e1), (1, e1), (3, e1), (4, e1), (9, e1), (10, e1), (18, e1)],
    [(2, e1), (3, e1), (4, e1), (5, e1), (6, e1), (8, e1), (9, e1), (11, e1), (12, e1), (19, e1)],
    [(0, e1), (2, e1), (4, e1), (5, e1), (11, e1), (13, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(1, e1), (3, e1), (6, e1), (7, e1), (8, e1), (11, e1), (13, e1), (15, e1), (16, e1), (22, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (4, e1), (6, e1), (9, e1), (10, e1), (11, e1), (14, e1), (17, e1), (18, e1), (23, e1)],
    [(0, e1), (1, e1), (4, e1), (5, e1), (6, e1), (8, e1), (9, e1), (13, e1), (16, e1), (17, e1), (19, e1), (20, e1), (24, e1)],
    [(0, e1), (2, e1), (3, e1), (6, e1), (7, e1), (8, e1), (10, e1), (11, e1), (12, e1), (13, e1), (15, e1), (17, e1), (18, e1), (19, e1), (20, e1), (21, e1), (25, e1)]])
private theorem commutator_2_right_s3 : wordMatrix [Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m3 := by
  rw [wordMatrix_cons, commutator_2_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private def commutator_2_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(0, e1), (4, e1)],
    [(0, e1), (1, e1), (5, e1)],
    [(0, e1), (1, e1), (2, e1), (6, e1)],
    [(0, e1), (1, e1), (2, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(1, e1), (3, e1), (5, e1), (10, e1)],
    [(2, e1), (3, e1), (4, e1), (11, e1)],
    [(2, e1), (3, e1), (4, e1), (5, e1), (7, e1), (12, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (13, e1)],
    [(1, e1), (3, e1), (5, e1), (6, e1), (8, e1), (14, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (15, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1), (16, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (9, e1), (11, e1), (17, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (18, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (8, e1), (9, e1), (10, e1), (11, e1), (12, e1), (19, e1)],
    [(5, e1), (7, e1), (11, e1), (13, e1), (15, e1), (20, e1)],
    [(1, e1), (2, e1), (4, e1), (5, e1), (6, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (14, e1), (21, e1)],
    [(5, e1), (7, e1), (11, e1), (13, e1), (14, e1), (15, e1), (16, e1), (22, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (17, e1), (18, e1), (19, e1), (23, e1)],
    [(8, e1), (10, e1), (12, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (24, e1)],
    [(8, e1), (10, e1), (12, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (21, e1), (22, e1), (25, e1)]])
private theorem commutator_2_right_s2 : wordMatrix [Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m2 := by
  rw [wordMatrix_cons, commutator_2_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private def commutator_2_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(0, e1), (4, e1)],
    [(1, e1), (3, e1), (5, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1)],
    [(1, e1), (2, e1), (4, e1), (7, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(1, e1), (3, e1), (9, e1)],
    [(5, e1), (9, e1), (10, e1)],
    [(2, e1), (3, e1), (4, e1), (11, e1)],
    [(5, e1), (7, e1), (11, e1), (12, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (13, e1)],
    [(5, e1), (7, e1), (8, e1), (11, e1), (13, e1), (14, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (15, e1)],
    [(8, e1), (15, e1), (16, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (9, e1), (11, e1), (17, e1)],
    [(5, e1), (7, e1), (10, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1)],
    [(8, e1), (10, e1), (12, e1), (17, e1), (19, e1)],
    [(5, e1), (7, e1), (11, e1), (13, e1), (15, e1), (20, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(14, e1), (16, e1), (20, e1), (22, e1)],
    [(8, e1), (10, e1), (12, e1), (14, e1), (17, e1), (18, e1), (19, e1), (23, e1)],
    [(8, e1), (10, e1), (12, e1), (16, e1), (17, e1), (18, e1), (19, e1), (20, e1), (24, e1)],
    [(21, e1), (22, e1), (24, e1), (25, e1)]])
private theorem commutator_2_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_right_m1 := by
  rw [wordMatrix_cons, commutator_2_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_2_right_s0 : wordMatrix [Atom.root 3 1, Atom.root 0 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_target := by
  rw [wordMatrix_cons, commutator_2_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 3 1))
  decide +kernel
private theorem commutator_2_right : wordMatrix [Atom.root 3 1, Atom.root 0 1, Atom.root 4 1, Atom.root 5 1, Atom.root 6 1, Atom.root 7 1, Atom.root 8 1, Atom.root 10 1, Atom.root 11 1] = commutator_2_target := commutator_2_right_s0
theorem commutator_2 : wordGroup (commutator_lhs 2) = wordGroup (commutator_rhs 2) := by
  apply word_eq_of_matrix_eq
  exact commutator_2_left.trans commutator_2_right.symm

private def commutator_3_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(0, e1), (3, e1)],
    [(4, e1)],
    [(0, e1), (3, e1), (5, e1)],
    [(2, e1), (4, e1), (6, e1)],
    [(1, e1), (4, e1), (7, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(5, e1), (9, e1), (10, e1)],
    [(0, e1), (3, e1), (11, e1)],
    [(0, e1), (3, e1), (7, e1), (11, e1), (12, e1)],
    [(7, e1), (13, e1)],
    [(0, e1), (3, e1), (7, e1), (8, e1), (11, e1), (13, e1), (14, e1)],
    [(2, e1), (6, e1), (15, e1)],
    [(2, e1), (6, e1), (15, e1), (16, e1)],
    [(0, e1), (11, e1), (17, e1)],
    [(0, e1), (1, e1), (7, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1)],
    [(0, e1), (5, e1), (10, e1), (11, e1), (17, e1), (19, e1)],
    [(2, e1), (15, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(2, e1), (8, e1), (14, e1), (15, e1), (20, e1), (22, e1)],
    [(5, e1), (19, e1), (23, e1)],
    [(1, e1), (12, e1), (13, e1), (18, e1), (24, e1)],
    [(1, e1), (8, e1), (12, e1), (13, e1), (18, e1), (22, e1), (24, e1), (25, e1)]])
private theorem commutator_3_left_s1 : wordMatrix [Atom.root 4 1] = atomMatrix (Atom.root 4 1) := by simp
private theorem commutator_3_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 4 1] = commutator_3_target := by
  rw [wordMatrix_cons, commutator_3_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_3_left : wordMatrix [Atom.root 0 1, Atom.root 4 1] = commutator_3_target := commutator_3_left_s0
private theorem commutator_3_right_s4 : wordMatrix [Atom.root 11 1] = atomMatrix (Atom.root 11 1) := by simp
private def commutator_3_right_m3 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (12, e1)],
    [(0, e1), (13, e1)],
    [(1, e1), (2, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(2, e1), (6, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (18, e1)],
    [(0, e1), (9, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (7, e1), (13, e1), (22, e1)],
    [(3, e1), (9, e1), (11, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (6, e1), (12, e1), (15, e1), (18, e1), (25, e1)]])
private theorem commutator_3_right_s3 : wordMatrix [Atom.root 8 1, Atom.root 11 1] = commutator_3_right_m3 := by
  rw [wordMatrix_cons, commutator_3_right_s4]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_3_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(0, e1), (1, e1), (2, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (4, e1), (12, e1)],
    [(0, e1), (4, e1), (13, e1)],
    [(1, e1), (2, e1), (3, e1), (6, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(2, e1), (4, e1), (6, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (18, e1)],
    [(0, e1), (9, e1), (11, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(1, e1), (3, e1), (4, e1), (5, e1), (7, e1), (9, e1), (10, e1), (12, e1), (13, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (4, e1), (7, e1), (11, e1), (13, e1), (15, e1), (22, e1)],
    [(3, e1), (9, e1), (11, e1), (17, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (24, e1)],
    [(0, e1), (3, e1), (6, e1), (12, e1), (15, e1), (17, e1), (18, e1), (20, e1), (25, e1)]])
private theorem commutator_3_right_s2 : wordMatrix [Atom.root 7 1, Atom.root 8 1, Atom.root 11 1] = commutator_3_right_m2 := by
  rw [wordMatrix_cons, commutator_3_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 7 1))
  decide +kernel
private def commutator_3_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(0, e1), (4, e1), (7, e1)],
    [(1, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(0, e1), (3, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(3, e1), (4, e1), (11, e1), (12, e1)],
    [(0, e1), (4, e1), (13, e1)],
    [(0, e1), (1, e1), (2, e1), (3, e1), (4, e1), (6, e1), (11, e1), (13, e1), (14, e1)],
    [(4, e1), (15, e1)],
    [(2, e1), (6, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (4, e1), (17, e1), (18, e1)],
    [(0, e1), (9, e1), (11, e1), (17, e1), (19, e1)],
    [(4, e1), (20, e1)],
    [(0, e1), (1, e1), (5, e1), (7, e1), (10, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(0, e1), (2, e1), (3, e1), (7, e1), (11, e1), (13, e1), (15, e1), (20, e1), (22, e1)],
    [(3, e1), (9, e1), (11, e1), (17, e1), (23, e1)],
    [(4, e1), (11, e1), (17, e1), (24, e1)],
    [(0, e1), (3, e1), (4, e1), (6, e1), (11, e1), (12, e1), (15, e1), (18, e1), (20, e1), (24, e1), (25, e1)]])
private theorem commutator_3_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 7 1, Atom.root 8 1, Atom.root 11 1] = commutator_3_right_m1 := by
  rw [wordMatrix_cons, commutator_3_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_3_right_s0 : wordMatrix [Atom.root 4 1, Atom.root 0 1, Atom.root 7 1, Atom.root 8 1, Atom.root 11 1] = commutator_3_target := by
  rw [wordMatrix_cons, commutator_3_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 4 1))
  decide +kernel
private theorem commutator_3_right : wordMatrix [Atom.root 4 1, Atom.root 0 1, Atom.root 7 1, Atom.root 8 1, Atom.root 11 1] = commutator_3_target := commutator_3_right_s0
theorem commutator_3 : wordGroup (commutator_lhs 3) = wordGroup (commutator_rhs 3) := by
  apply word_eq_of_matrix_eq
  exact commutator_3_left.trans commutator_3_right.symm

private def commutator_4_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(0, e1), (4, e1)],
    [(3, e1), (5, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1)],
    [(0, e1), (4, e1), (7, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(1, e1), (9, e1)],
    [(1, e1), (9, e1), (10, e1)],
    [(2, e1), (11, e1)],
    [(2, e1), (5, e1), (11, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (11, e1), (13, e1), (14, e1)],
    [(7, e1), (15, e1)],
    [(7, e1), (8, e1), (15, e1), (16, e1)],
    [(1, e1), (6, e1), (9, e1), (17, e1)],
    [(1, e1), (6, e1), (9, e1), (10, e1), (17, e1), (18, e1)],
    [(1, e1), (6, e1), (8, e1), (9, e1), (17, e1), (19, e1)],
    [(5, e1), (13, e1), (20, e1)],
    [(1, e1), (6, e1), (8, e1), (9, e1), (10, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(5, e1), (13, e1), (20, e1), (22, e1)],
    [(14, e1), (23, e1)],
    [(8, e1), (16, e1), (19, e1), (24, e1)],
    [(8, e1), (16, e1), (19, e1), (21, e1), (24, e1), (25, e1)]])
private theorem commutator_4_left_s1 : wordMatrix [Atom.root 5 1] = atomMatrix (Atom.root 5 1) := by simp
private theorem commutator_4_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 5 1] = commutator_4_target := by
  rw [wordMatrix_cons, commutator_4_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_4_left : wordMatrix [Atom.root 0 1, Atom.root 5 1] = commutator_4_target := commutator_4_left_s0
private theorem commutator_4_right_s3 : wordMatrix [Atom.root 9 1] = atomMatrix (Atom.root 9 1) := by simp
private def commutator_4_right_m2 : Mat := Sparse.eval (![[(0, e1)],
    [(1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(5, e1)],
    [(6, e1)],
    [(0, e1), (7, e1)],
    [(1, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(0, e1), (1, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (3, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(1, e1), (6, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(4, e1), (6, e1), (18, e1)],
    [(0, e1), (7, e1), (9, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(0, e1), (1, e1), (7, e1), (8, e1), (10, e1), (21, e1)],
    [(3, e1), (5, e1), (13, e1), (22, e1)],
    [(2, e1), (11, e1), (13, e1), (23, e1)],
    [(0, e1), (4, e1), (9, e1), (15, e1), (17, e1), (24, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (10, e1), (15, e1), (16, e1), (18, e1), (25, e1)]])
private theorem commutator_4_right_s2 : wordMatrix [Atom.root 8 1, Atom.root 9 1] = commutator_4_right_m2 := by
  rw [wordMatrix_cons, commutator_4_right_s3]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 8 1))
  decide +kernel
private def commutator_4_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(0, e1), (4, e1), (7, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(0, e1), (9, e1)],
    [(1, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(2, e1), (3, e1), (11, e1), (12, e1)],
    [(13, e1)],
    [(2, e1), (11, e1), (13, e1), (14, e1)],
    [(0, e1), (4, e1), (15, e1)],
    [(0, e1), (1, e1), (4, e1), (6, e1), (15, e1), (16, e1)],
    [(4, e1), (17, e1)],
    [(6, e1), (17, e1), (18, e1)],
    [(0, e1), (4, e1), (7, e1), (9, e1), (17, e1), (19, e1)],
    [(3, e1), (20, e1)],
    [(1, e1), (6, e1), (8, e1), (9, e1), (10, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(5, e1), (13, e1), (20, e1), (22, e1)],
    [(2, e1), (11, e1), (13, e1), (23, e1)],
    [(0, e1), (4, e1), (9, e1), (15, e1), (17, e1), (24, e1)],
    [(1, e1), (6, e1), (9, e1), (10, e1), (16, e1), (17, e1), (18, e1), (24, e1), (25, e1)]])
private theorem commutator_4_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 8 1, Atom.root 9 1] = commutator_4_right_m1 := by
  rw [wordMatrix_cons, commutator_4_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_4_right_s0 : wordMatrix [Atom.root 5 1, Atom.root 0 1, Atom.root 8 1, Atom.root 9 1] = commutator_4_target := by
  rw [wordMatrix_cons, commutator_4_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 5 1))
  decide +kernel
private theorem commutator_4_right : wordMatrix [Atom.root 5 1, Atom.root 0 1, Atom.root 8 1, Atom.root 9 1] = commutator_4_target := commutator_4_right_s0
theorem commutator_4 : wordGroup (commutator_lhs 4) = wordGroup (commutator_rhs 4) := by
  apply word_eq_of_matrix_eq
  exact commutator_4_left.trans commutator_4_right.symm

private def commutator_5_target : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(1, e1), (3, e1), (5, e1)],
    [(0, e1), (4, e1), (6, e1)],
    [(2, e1), (4, e1), (7, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(3, e1), (9, e1)],
    [(3, e1), (9, e1), (10, e1)],
    [(4, e1), (11, e1)],
    [(4, e1), (11, e1), (12, e1)],
    [(6, e1), (13, e1)],
    [(1, e1), (4, e1), (5, e1), (6, e1), (11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(2, e1), (7, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(3, e1), (9, e1), (17, e1), (18, e1)],
    [(0, e1), (6, e1), (12, e1), (17, e1), (19, e1)],
    [(4, e1), (11, e1), (20, e1)],
    [(0, e1), (1, e1), (3, e1), (6, e1), (9, e1), (12, e1), (14, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(2, e1), (4, e1), (11, e1), (16, e1), (20, e1), (22, e1)],
    [(3, e1), (18, e1), (23, e1)],
    [(4, e1), (20, e1), (24, e1)],
    [(0, e1), (4, e1), (12, e1), (19, e1), (20, e1), (24, e1), (25, e1)]])
private theorem commutator_5_left_s1 : wordMatrix [Atom.root 6 1] = atomMatrix (Atom.root 6 1) := by simp
private theorem commutator_5_left_s0 : wordMatrix [Atom.root 0 1, Atom.root 6 1] = commutator_5_target := by
  rw [wordMatrix_cons, commutator_5_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_5_left : wordMatrix [Atom.root 0 1, Atom.root 6 1] = commutator_5_target := commutator_5_left_s0
private theorem commutator_5_right_s2 : wordMatrix [Atom.root 7 1] = atomMatrix (Atom.root 7 1) := by simp
private def commutator_5_right_m1 : Mat := Sparse.eval (![[(0, e1)],
    [(0, e1), (1, e1)],
    [(2, e1)],
    [(3, e1)],
    [(4, e1)],
    [(0, e1), (3, e1), (5, e1)],
    [(4, e1), (6, e1)],
    [(4, e1), (7, e1)],
    [(0, e1), (2, e1), (4, e1), (6, e1), (7, e1), (8, e1)],
    [(9, e1)],
    [(3, e1), (9, e1), (10, e1)],
    [(11, e1)],
    [(4, e1), (11, e1), (12, e1)],
    [(4, e1), (13, e1)],
    [(3, e1), (4, e1), (6, e1), (11, e1), (13, e1), (14, e1)],
    [(15, e1)],
    [(4, e1), (15, e1), (16, e1)],
    [(17, e1)],
    [(17, e1), (18, e1)],
    [(11, e1), (17, e1), (19, e1)],
    [(20, e1)],
    [(4, e1), (9, e1), (11, e1), (12, e1), (13, e1), (17, e1), (18, e1), (19, e1), (21, e1)],
    [(11, e1), (15, e1), (20, e1), (22, e1)],
    [(17, e1), (23, e1)],
    [(24, e1)],
    [(17, e1), (20, e1), (24, e1), (25, e1)]])
private theorem commutator_5_right_s1 : wordMatrix [Atom.root 0 1, Atom.root 7 1] = commutator_5_right_m1 := by
  rw [wordMatrix_cons, commutator_5_right_s2]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 0 1))
  decide +kernel
private theorem commutator_5_right_s0 : wordMatrix [Atom.root 6 1, Atom.root 0 1, Atom.root 7 1] = commutator_5_target := by
  rw [wordMatrix_cons, commutator_5_right_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 6 1))
  decide +kernel
private theorem commutator_5_right : wordMatrix [Atom.root 6 1, Atom.root 0 1, Atom.root 7 1] = commutator_5_target := commutator_5_right_s0
theorem commutator_5 : wordGroup (commutator_lhs 5) = wordGroup (commutator_rhs 5) := by
  apply word_eq_of_matrix_eq
  exact commutator_5_left.trans commutator_5_right.symm

end Kourovka.Problem2153.WilsonModel.RootData.Relations
