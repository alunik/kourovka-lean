import Kourovka2135.BinaryExteriorAlgebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The characteristic-two unipotent character in squarefree coordinates.

The additive parameter maps to a product of commuting square-zero factors.
Its coordinates in the subset basis are the binary subset powers, supplying
the concrete coefficient matrix for the subsequent Vandermonde argument.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryExteriorCharacter

open Kourovka2135.BinaryExteriorAlgebra
open scoped CharTwo IsMulCommutative

variable (k : Type*) [CommRing k] [CharP k 2] (f : ℕ)

/-- The additive unipotent parameter in the concrete coordinate algebra. -/
def character (t : k) : Carrier k f :=
  ∏ i : Fin f, (1 + t ^ (2 ^ i.val) • generator k f i)

theorem one_add_smul_generator_mul (i : Fin f) (a b : k) :
    (1 + a • generator k f i) * (1 + b • generator k f i) =
      1 + (a + b) • generator k f i := by
  simp [add_mul, mul_add, generator_square,
    add_smul, add_assoc, add_left_comm, add_comm]

@[simp] theorem character_zero : character k f 0 = 1 := by
  simp [character]

/-- The product formula respects addition of the parameter. -/
theorem character_add (s t : k) :
    character k f (s + t) = character k f s * character k f t := by
  simp only [character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [add_pow_char_pow s t 2 i.val, one_add_smul_generator_mul]

/-- The character as a homomorphism from the multiplicative type tag of k. -/
def characterHom : Multiplicative k →* Carrier k f where
  toFun t := character k f t.toAdd
  map_one' := character_zero k f
  map_mul' s t := character_add k f s.toAdd t.toAdd

@[simp] theorem characterHom_apply (t : Multiplicative k) :
    characterHom k f t = character k f t.toAdd := rfl

@[simp] theorem character_mul_self (t : k) :
    character k f t * character k f t = 1 := by
  rw [← character_add, CharTwo.add_self_eq_zero, character_zero]

/-- The character value is a unit, with itself as inverse. -/
def characterUnit (t : k) : (Carrier k f)ˣ where
  val := character k f t
  inv := character k f t
  val_inv := character_mul_self k f t
  inv_val := character_mul_self k f t

@[simp] theorem characterUnit_val (t : k) :
    (characterUnit k f t : Carrier k f) = character k f t := rfl

/-- The same character with its invertibility recorded in the codomain. -/
def characterUnitsHom : Multiplicative k →* (Carrier k f)ˣ where
  toFun t := characterUnit k f t.toAdd
  map_one' := Units.ext (character_zero k f)
  map_mul' s t := Units.ext (character_add k f s.toAdd t.toAdd)

/-- Multiplying distinct generators gives the subset basis monomial. -/
theorem prod_smul_generator (s : Finset (Fin f)) (c : Fin f → k) :
    (∏ i ∈ s, c i • generator k f i) =
      (∏ i ∈ s, c i) • basis k f s := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih]
    simp [generator_mul_basis, hi, smul_smul, _root_.mul_comm]

/-- Expansion of the character in the squarefree basis. -/
theorem character_eq_sum_basis (t : k) :
    character k f t =
      ∑ I : Finset (Fin f), t ^ (∑ i ∈ I, 2 ^ i.val) • basis k f I := by
  unfold character
  rw [Finset.prod_one_add]
  have hpow : (Finset.univ : Finset (Fin f)).powerset = Finset.univ := by
    ext I
    simp
  rw [hpow]
  apply Finset.sum_congr rfl
  intro I _
  rw [prod_smul_generator, Finset.prod_pow_eq_pow_sum]

/-- The coefficient matrix consists of the binary subset powers of t. -/
@[simp] theorem character_coeff (t : k) (I : Finset (Fin f)) :
    (basis k f).repr (character k f t) I = t ^ (∑ i ∈ I, 2 ^ i.val) := by
  rw [character_eq_sum_basis]
  exact congrFun ((basis k f).repr_sum_self
    (fun J : Finset (Fin f) => t ^ (∑ i ∈ J, 2 ^ i.val))) I

end Kourovka2135.BinaryExteriorCharacter
