import Kourovka.Problem2153.WilsonModel.RootData.Words

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem.RankOne

open WilsonModel

/-- A rank-one certificate additionally needs diagonal torus atoms. -/
inductive Atom where
  | root (i : Fin 12) (a : Fin 8)
  | rho
  | sigma
  | torus (a b : Fin 7)
  deriving DecidableEq

def torusRows (a b : Fin 7) : Sparse.Table (Fin 26) :=
  fun i => [(i, torusDiag a b i)]

theorem torusRows_alignment (a b : Fin 7) :
    Matrix.diagonal (torusDiag a b) = Sparse.eval (torusRows a b) := by
  ext i j
  simp [Sparse.eval, torusRows, Sparse.rowEval, Matrix.diagonal]

def atomRows : Atom → Sparse.Table (Fin 26)
  | .root i a => RootData.rootRows i a
  | .rho => rhoSparse
  | .sigma => sigmaSparse
  | .torus a b => torusRows a b

def atomMatrix (a : Atom) : WilsonModel.Mat := Sparse.eval (atomRows a)

def atomGroup : Atom → G
  | .root i a => root i a
  | .rho => r
  | .sigma => s
  | .torus a b => RootSystem.torus a b

theorem atom_alignment (a : Atom) : RootData.matrixHom (atomGroup a) = atomMatrix a := by
  cases a with
  | root i a => exact RootData.root_alignment i a
  | rho => exact rho_alignment
  | sigma => exact sigma_alignment
  | torus a b => exact torusRows_alignment a b

def wordMatrix (w : List Atom) : WilsonModel.Mat := (w.map atomMatrix).prod
def wordGroup (w : List Atom) : G := (w.map atomGroup).prod

@[simp] theorem wordMatrix_nil : wordMatrix [] = 1 := rfl
@[simp] theorem wordMatrix_cons (a : Atom) (w : List Atom) :
    wordMatrix (a :: w) = atomMatrix a * wordMatrix w := rfl
@[simp] theorem wordGroup_nil : wordGroup [] = 1 := rfl
@[simp] theorem wordGroup_cons (a : Atom) (w : List Atom) :
    wordGroup (a :: w) = atomGroup a * wordGroup w := rfl

theorem word_alignment (w : List Atom) : RootData.matrixHom (wordGroup w) = wordMatrix w := by
  induction w with
  | nil => exact map_one _
  | cons a w ih => rw [wordGroup_cons, map_mul, atom_alignment, ih, wordMatrix_cons]

theorem word_eq_of_matrix_eq (a b : List Atom) (h : wordMatrix a = wordMatrix b) :
    wordGroup a = wordGroup b := by
  apply RootData.matrixHom_injective
  simpa only [word_alignment] using h

end Kourovka.Problem2153.RootSystem.RankOne
