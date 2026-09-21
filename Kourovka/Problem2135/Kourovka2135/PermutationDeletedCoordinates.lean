import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Abel

/-! Actual coordinates on a permutation module modulo its constant line.
The distinguished coordinate is `none`. The construction is valid over any
commutative ring and requires neither finiteness nor a division by the number
of points. It is a genuine left representation, not a generator-only action. -/

set_option autoImplicit false
namespace Kourovka2135.PermutationDeletedCoordinates

variable (k : Type*) [CommRing k] (ι : Type*)

/-- Choose the unique representative whose distinguished coordinate is zero. -/
def extend : (ι → k) →ₗ[k] (Option ι → k) where
  toFun v x := x.elim 0 v
  map_add' v w := by funext x; cases x <;> simp
  map_smul' c v := by funext x; cases x <;> simp

/-- Coordinates of a function modulo the constant line. -/
def coordinates : (Option ι → k) →ₗ[k] (ι → k) where
  toFun f i := f (some i) - f none
  map_add' f g := by funext i; dsimp; abel
  map_smul' c f := by
    funext i
    change c * f (some i) - c * f none = c * (f (some i) - f none)
    exact (mul_sub c _ _).symm

@[simp] theorem coordinates_extend (v : ι → k) :
    coordinates k ι (extend k ι v) = v := by ext i; simp [coordinates, extend]

theorem extend_coordinates (f : Option ι → k) (x : Option ι) :
    extend k ι (coordinates k ι f) x = f x - f none := by
  cases x <;> simp [coordinates, extend]

theorem coordinates_surjective : Function.Surjective (coordinates k ι) :=
  fun v => ⟨extend k ι v, coordinates_extend k ι v⟩

theorem coordinates_eq_zero_iff (f : Option ι → k) :
    coordinates k ι f = 0 ↔ ∀ x, f x = f none := by
  constructor
  · intro h x
    cases x with
    | none => rfl
    | some i =>
      have hi := congrFun h i
      exact sub_eq_zero.mp hi
  · intro h
    ext i
    exact sub_eq_zero.mpr (h (some i))

/-- The coordinate operator induced by an actual permutation. -/
def action (p : Equiv.Perm (Option ι)) : (ι → k) →ₗ[k] (ι → k) where
  toFun v i := extend k ι v (p.symm (some i)) - extend k ι v (p.symm none)
  map_add' v w := by
    ext i
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' c v := by
    ext i
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem extend_action (p : Equiv.Perm (Option ι)) (v : ι → k) (x : Option ι) :
    extend k ι (action k ι p v) x =
      extend k ι v (p.symm x) - extend k ι v (p.symm none) := by
  cases x <;> simp [extend, action]

/-- A true representation of the full permutation group on the quotient coordinates. -/
def representation : Representation k (Equiv.Perm (Option ι)) (ι → k) where
  toFun := action k ι
  map_one' := by
    ext v i
    change extend k ι v (some i) - extend k ι v none = v i
    simp [extend]
  map_mul' p q := by
    ext v i
    change extend k ι v ((p * q).symm (some i)) - extend k ι v ((p * q).symm none) =
      extend k ι (action k ι q v) (p.symm (some i)) -
        extend k ι (action k ι q v) (p.symm none)
    rw [extend_action, extend_action]
    change extend k ι v (q.symm (p.symm (some i))) - extend k ι v (q.symm (p.symm none)) =
      (extend k ι v (q.symm (p.symm (some i))) - extend k ι v (q.symm none)) -
        (extend k ι v (q.symm (p.symm none)) - extend k ι v (q.symm none))
    abel

@[simp] theorem representation_apply (p : Equiv.Perm (Option ι)) (v : ι → k) (i : ι) :
    representation k ι p v i =
      extend k ι v (p.symm (some i)) - extend k ι v (p.symm none) := rfl

/-- The actual permutation action intertwines the coordinate quotient map. -/
theorem coordinates_permute (p : Equiv.Perm (Option ι)) (f : Option ι → k) :
    coordinates k ι (fun x => f (p.symm x)) = representation k ι p (coordinates k ι f) := by
  ext i
  change f (p.symm (some i)) - f (p.symm none) =
    extend k ι (coordinates k ι f) (p.symm (some i)) -
      extend k ι (coordinates k ι f) (p.symm none)
  rw [extend_coordinates, extend_coordinates]
  abel

end Kourovka2135.PermutationDeletedCoordinates
