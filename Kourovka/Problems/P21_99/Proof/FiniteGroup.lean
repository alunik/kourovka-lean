import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Equiv.Basic

/-! The ambient group of block permutations and additive automorphisms. -/

namespace Kourovka.P21_99

abbrev LinearBlockGroup (I V : Type*) [AddCommGroup V] :=
  Equiv.Perm I × Multiplicative (AddAut V)

instance linearBlockMulAction (I V : Type*) [AddCommGroup V] :
    MulAction (LinearBlockGroup I V) I where
  smul g i := g.1 i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance linearBlockDistribMulAction (I V : Type*) [AddCommGroup V] :
    DistribMulAction (LinearBlockGroup I V) V where
  smul g v := g.2.toAdd v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := g.2.toAdd.map_zero
  smul_add g v w := g.2.toAdd.map_add v w

@[simp] theorem linearBlock_smul_block {I V : Type*} [AddCommGroup V]
    (g : LinearBlockGroup I V) (i : I) : g • i = g.1 i := rfl

@[simp] theorem linearBlock_smul_vector {I V : Type*} [AddCommGroup V]
    (g : LinearBlockGroup I V) (v : V) : g • v = g.2 v := rfl

def addEquivOfInverse {V : Type*} [AddCommGroup V] (f g : V →+ V)
    (left : ∀ x, g (f x) = x) (right : ∀ x, f (g x) = x) :
    Multiplicative (AddAut V) where
  toFun := f
  invFun := g
  left_inv := left
  right_inv := right
  map_add' := f.map_add

@[simp] theorem addEquivOfInverse_apply {V : Type*} [AddCommGroup V]
    (f g : V →+ V) (left : ∀ x, g (f x) = x) (right : ∀ x, f (g x) = x)
    (x : V) : addEquivOfInverse f g left right x = f x := rfl

end Kourovka.P21_99
