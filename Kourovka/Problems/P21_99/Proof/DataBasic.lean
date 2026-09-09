import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Sparse linear maps used by the finite certificates for Problem 21.99.

The lists are merely data.  All identities used later are proved in Lean's
kernel by checking the images of the coordinate basis vectors.
-/

namespace Kourovka.P21_99.Data

abbrev Scalar := ZMod 5
abbrev Vec (n : ℕ) := Fin n → Scalar
abbrev Row (n : ℕ) := List (Fin n × Scalar)
abbrev Rows (n m : ℕ) := Fin m → Row n

def rowLinear {n : ℕ} : Row n → Vec n →ₗ[Scalar] Scalar
  | [] => 0
  | (j, a) :: rest => a • LinearMap.proj j + rowLinear rest

def linear {n m : ℕ} (a : Rows n m) : Vec n →ₗ[Scalar] Vec m :=
  LinearMap.pi fun i => rowLinear (a i)

def basisVector {n : ℕ} (j : Fin n) : Vec n := Pi.single j 1

def entry {n m : ℕ} (a : Rows n m) (i : Fin m) (j : Fin n) : Scalar :=
  linear a (basisVector j) i

def compEntry {n m l : ℕ} (a : Rows m l) (b : Rows n m)
    (i : Fin l) (j : Fin n) : Scalar :=
  linear a (linear b (basisVector j)) i

def identityEntry {n : ℕ} (i j : Fin n) : Scalar := if i = j then 1 else 0

theorem ext_basis {n : ℕ} {M : Type*} [AddCommGroup M] [Module Scalar M]
    (f g : Vec n →ₗ[Scalar] M)
    (h : ∀ j, f (basisVector j) = g (basisVector j)) : f = g := by
  apply LinearMap.pi_ext
  intro j a
  have heq : Pi.single j a = a • basisVector j := by
    ext k
    by_cases hk : k = j
    · subst k; simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne hk]
  rw [heq, map_smul, map_smul, h]

theorem ext_entries {n m : ℕ} (f g : Vec n →ₗ[Scalar] Vec m)
    (h : ∀ i j, f (basisVector j) i = g (basisVector j) i) : f = g := by
  apply ext_basis
  intro j
  funext i
  exact h i j

theorem comp_eq_of_entries {n m l : ℕ} (a : Rows m l) (b : Rows n m)
    (c : Rows n l) (h : ∀ i j, compEntry a b i j = entry c i j) :
    (linear a).comp (linear b) = linear c :=
  ext_entries _ _ h

theorem comp_id_of_entries {n m : ℕ} (a : Rows m n) (b : Rows n m)
    (h : ∀ i j, compEntry a b i j = identityEntry i j) :
    (linear a).comp (linear b) = LinearMap.id := by
  apply ext_entries
  intro i j
  change compEntry a b i j = basisVector j i
  rw [h]
  by_cases hi : i = j
  · subst i; simp [identityEntry, basisVector]
  · simp [identityEntry, basisVector, hi]

end Kourovka.P21_99.Data
