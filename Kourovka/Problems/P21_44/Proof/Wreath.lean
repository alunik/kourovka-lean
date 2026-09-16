import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-! # The degree-five permutational wreath product

The root action is on the left; sections are reindexed by the inverse root
permutation. Consequently the directed generators use inverse three-cycles.
-/

namespace Kourovka.P21_44

abbrev Alphabet := Fin 5
abbrev A5 := alternatingGroup Alphabet

/-- Permuting the five factors by inverse reindexing. -/
def reindexAction (P : Type*) [Group P] : A5 →* MulAut (Alphabet → P) where
  toFun σ :=
    { toFun := fun f i => f (σ.val⁻¹ i)
      invFun := fun f i => f (σ.val i)
      left_inv := by intro f; funext i; simp
      right_inv := by intro f; funext i; simp
      map_mul' := by intros; rfl }
  map_one' := by ext f i; rfl
  map_mul' := by intros; ext f i; rfl

abbrev Wreath (P : Type*) [Group P] :=
  SemidirectProduct (Alphabet → P) A5 (reindexAction P)

/-- The inverse of the cycle `(0 1 2)`. -/
def rootA : A5 :=
  ⟨Equiv.swap 1 2 * Equiv.swap 0 1, by simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

/-- The inverse of the cycle `(2 3 4)`. -/
def rootB : A5 :=
  ⟨Equiv.swap 3 4 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

@[simp] theorem rootA_cube : rootA ^ 3 = 1 := by decide
@[simp] theorem rootB_cube : rootB ^ 3 = 1 := by decide
@[simp] theorem rootA_fix : rootA.val 3 = 3 := by decide
@[simp] theorem rootB_fix : rootB.val 0 = 0 := by decide
@[simp] theorem rootA_inv_fix : rootA.val⁻¹ 3 = 3 := by decide
@[simp] theorem rootB_inv_fix : rootB.val⁻¹ 0 = 0 := by decide

namespace Wreath
variable {P Q : Type*} [Group P] [Group Q]

@[simp] theorem mul_left_apply (x y : Wreath P) (i : Alphabet) :
    (x * y).left i = x.left i * y.left (x.right.val⁻¹ i) := rfl
@[simp] theorem inv_left_apply (x : Wreath P) (i : Alphabet) :
    (x⁻¹).left i = (x.left (x.right.val i))⁻¹ := rfl

/-- Applying a homomorphism in every section. -/
def map (f : P →* Q) : Wreath P →* Wreath Q where
  toFun x := ⟨fun i => f (x.left i), x.right⟩
  map_one' := by ext i <;> simp
  map_mul' := by intros; ext i <;> simp

@[simp] theorem map_left (f : P →* Q) (x : Wreath P) (i : Alphabet) :
    (map f x).left i = f (x.left i) := rfl
@[simp] theorem map_right (f : P →* Q) (x : Wreath P) :
    (map f x).right = x.right := rfl

/-- A directed element with its unique possibly nontrivial section at `3`. -/
def genA (u : P) : Wreath P := ⟨Pi.mulSingle 3 u, rootA⟩
/-- A directed element with its unique possibly nontrivial section at `0`. -/
def genB (v : P) : Wreath P := ⟨Pi.mulSingle 0 v, rootB⟩

@[simp] theorem genA_left (u : P) (i : Alphabet) :
    (genA u).left i = if i = 3 then u else 1 := by simp [genA, Pi.mulSingle_apply]
@[simp] theorem genB_left (u : P) (i : Alphabet) :
    (genB u).left i = if i = 0 then u else 1 := by simp [genB, Pi.mulSingle_apply]
@[simp] theorem genA_right (u : P) : (genA u).right = rootA := rfl
@[simp] theorem genB_right (u : P) : (genB u).right = rootB := rfl

@[simp] theorem map_genA (f : P →* Q) (u : P) : map f (genA u) = genA (f u) := by
  apply SemidirectProduct.ext
  · funext i; by_cases h : i = 3 <;> simp [h]
  · rfl
@[simp] theorem map_genB (f : P →* Q) (u : P) : map f (genB u) = genB (f u) := by
  apply SemidirectProduct.ext
  · funext i; by_cases h : i = 0 <;> simp [h]
  · rfl

theorem genA_cube (u : P) (h : u ^ 3 = 1) : genA u ^ 3 = 1 := by
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;> simp_all [pow_succ, pow_zero, rootA, Equiv.swap_apply_def]
  · simpa only [pow_succ, pow_zero, SemidirectProduct.mul_right, genA_right, SemidirectProduct.one_right] using rootA_cube

theorem genB_cube (u : P) (h : u ^ 3 = 1) : genB u ^ 3 = 1 := by
  apply SemidirectProduct.ext
  · funext i
    fin_cases i <;> simp_all [pow_succ, pow_zero, rootB, Equiv.swap_apply_def]
  · simpa only [pow_succ, pow_zero, SemidirectProduct.mul_right, genB_right, SemidirectProduct.one_right] using rootB_cube

end Wreath
end Kourovka.P21_44
