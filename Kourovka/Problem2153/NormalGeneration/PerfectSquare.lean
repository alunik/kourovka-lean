import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
open WilsonModel Field8 F8
private def PerfectSquare_target : WilsonModel.Mat := 1
private theorem PerfectSquare_left_s1 : wordMatrix [Atom.root 11 6] = atomMatrix (Atom.root 11 6) := by simp
private theorem PerfectSquare_left_s0 : wordMatrix [Atom.root 11 6, Atom.root 11 6] = PerfectSquare_target := by
  rw [wordMatrix_cons, PerfectSquare_left_s1]
  apply Sparse.mul_eq_of_check (atomRows (Atom.root 11 6))
  decide +kernel
private theorem PerfectSquare_left : wordMatrix [Atom.root 11 6, Atom.root 11 6] = PerfectSquare_target := PerfectSquare_left_s0
private theorem PerfectSquare_right : wordMatrix [] = PerfectSquare_target := by decide +kernel
theorem PerfectSquare_checked : wordGroup [Atom.root 11 6, Atom.root 11 6] = wordGroup [] := by
  apply word_eq_of_matrix_eq
  exact PerfectSquare_left.trans PerfectSquare_right.symm

end Kourovka.Problem2153.RootSystem.NormalGeneration
