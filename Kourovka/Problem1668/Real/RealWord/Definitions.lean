import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace RealWord

def comm {G : Type*} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

def base {G : Type*} [Group G] (a b : G) : G :=
  comm (a * comm a b * a⁻¹) (b * (comm a b)⁻¹ * b⁻¹)

def value {G : Type*} [Group G] (a b : G) : G := base a (b * a * b⁻¹)

def word : FreeGroup (Fin 2) := value (FreeGroup.of 0) (FreeGroup.of 1)

def hpoly {R : Type*} [CommRing R] (U p : R) : R :=
  U ^ 2 * (p - 1) ^ 2 - U * p * (p ^ 2 - 2) + p ^ 2

def tracePoly {R : Type*} [CommRing R] (U p : R) : R :=
  2 + U * (p - 2) ^ 2 * (p - 1) ^ 2 * (U - p - 2) ^ 3 * hpoly U p

theorem map_value {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    f (value a b) = value (f a) (f b) := by
  simp only [value, base, comm, map_mul, map_inv]

theorem eval_word {G : Type*} [Group G] (g : Fin 2 → G) :
    FreeGroup.lift g word = value (g 0) (g 1) := by
  rw [word, map_value]
  simp

end RealWord
