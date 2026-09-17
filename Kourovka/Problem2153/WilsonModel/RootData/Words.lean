import Kourovka.Problem2153.WilsonModel.RootData.Alignment

set_option autoImplicit false

namespace Kourovka.Problem2153.WilsonModel.RootData
open Field8

inductive Atom where
  | root (i : Fin 12) (a : Fin 8)
  | rho
  | sigma
  deriving DecidableEq

def atomRows : Atom → Sparse.Table (Fin 26)
  | .root i a => rootRows i a
  | .rho => rhoSparse
  | .sigma => sigmaSparse

def atomMatrix (a : Atom) : Mat := Sparse.eval (atomRows a)

def atomGroup : Atom → RootSystem.G
  | .root i a => RootSystem.root i a
  | .rho => RootSystem.r
  | .sigma => RootSystem.s

theorem atom_alignment (a : Atom) : matrixHom (atomGroup a) = atomMatrix a := by
  cases a with
  | root i a => exact root_alignment i a
  | rho => exact rho_alignment
  | sigma => exact sigma_alignment

def wordMatrix (w : List Atom) : Mat := (w.map atomMatrix).prod

def wordGroup (w : List Atom) : RootSystem.G := (w.map atomGroup).prod

@[simp] theorem wordMatrix_nil : wordMatrix [] = 1 := rfl
@[simp] theorem wordMatrix_cons (a : Atom) (w : List Atom) :
    wordMatrix (a :: w) = atomMatrix a * wordMatrix w := rfl

@[simp] theorem wordGroup_nil : wordGroup [] = 1 := rfl
@[simp] theorem wordGroup_cons (a : Atom) (w : List Atom) :
    wordGroup (a :: w) = atomGroup a * wordGroup w := rfl

theorem word_alignment (w : List Atom) : matrixHom (wordGroup w) = wordMatrix w := by
  induction w with
  | nil => exact map_one matrixHom
  | cons a w ih =>
    rw [wordGroup_cons, map_mul, atom_alignment, ih, wordMatrix_cons]

theorem matrixHom_injective : Function.Injective matrixHom := by
  intro a b h
  exact Subtype.ext (Units.ext h)

/-- A word equality checked in the certified matrices holds in the actual ambient group. -/
theorem word_eq_of_matrix_eq (a b : List Atom) (h : wordMatrix a = wordMatrix b) :
    wordGroup a = wordGroup b := by
  apply matrixHom_injective
  simpa only [word_alignment] using h

end Kourovka.Problem2153.WilsonModel.RootData
