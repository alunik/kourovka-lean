import Kourovka2135.ClassTwoAddition
import Mathlib.Algebra.Module.ZMod

/-! A canonical additive group attached to class-two groups with odd commutator exponent. -/

set_option autoImplicit false
universe u
namespace Kourovka2135

/-- Data for division by two on a central derived subgroup. -/
structure ClassTwoData (G : Type u) [Group G] where
  halfExponent : ℕ
  central : commutator G ≤ Subgroup.center G
  half : ∀ c ∈ commutator G, c ^ (halfExponent + halfExponent) = c

/-- The original elements, equipped with corrected addition. -/
structure ClassTwoAdditive {G : Type u} [Group G] (_D : ClassTwoData G) : Type u where
  value : G

namespace ClassTwoAdditive
variable {G : Type u} [Group G] (D : ClassTwoData G)

def ofMul (x : G) : ClassTwoAdditive D := ⟨x⟩

def toMul (x : ClassTwoAdditive D) : G := x.value

@[simp] theorem toMul_ofMul (x : G) : toMul D (ofMul D x) = x := rfl
@[simp] theorem ofMul_toMul (x : ClassTwoAdditive D) : ofMul D (toMul D x) = x := rfl

theorem toMul_injective : Function.Injective (toMul D) := by
  intro x y h
  cases x
  cases y
  cases h
  rfl

instance : Zero (ClassTwoAdditive D) := ⟨ofMul D 1⟩
instance : Add (ClassTwoAdditive D) :=
  ⟨fun x y => ofMul D (classTwoSum D.halfExponent (toMul D x) (toMul D y))⟩
instance : Neg (ClassTwoAdditive D) := ⟨fun x => ofMul D (toMul D x)⁻¹⟩

instance : AddCommGroup (ClassTwoAdditive D) :=
  { AddGroup.ofLeftAxioms
      (fun x y z => toMul_injective D (classTwoSum_assoc D.central D.halfExponent
        (toMul D x) (toMul D y) (toMul D z)))
      (fun x => toMul_injective D (classTwoSum_one_left D.halfExponent (toMul D x)))
      (fun x => toMul_injective D (classTwoSum_inv_left D.halfExponent (toMul D x))) with
    add_comm := fun x y => toMul_injective D
      (classTwoSum_comm D.halfExponent D.half (toMul D x) (toMul D y)) }

@[simp] theorem toMul_zero : toMul D 0 = 1 := rfl
@[simp] theorem toMul_neg (x : ClassTwoAdditive D) : toMul D (-x) = (toMul D x)⁻¹ := rfl
@[simp] theorem toMul_add (x y : ClassTwoAdditive D) :
    toMul D (x + y) = classTwoSum D.halfExponent (toMul D x) (toMul D y) := rfl

@[simp] theorem toMul_nsmul (n : ℕ) (x : ClassTwoAdditive D) :
    toMul D (n • x) = toMul D x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, toMul_add, ih,
      classTwoSum_of_commute _ _ _ ((Commute.refl (toMul D x)).pow_left n), pow_succ]

/-- Every automorphism of the original group preserves corrected addition. -/
def map {H : Type u} [Group H] (E : ClassTwoData H)
    (f : G →* H) (hr : D.halfExponent = E.halfExponent) :
    ClassTwoAdditive D →+ ClassTwoAdditive E where
  toFun x := ofMul E (f (toMul D x))
  map_zero' := toMul_injective E f.map_one
  map_add' x y := by
    apply toMul_injective E
    change f (classTwoSum D.halfExponent (toMul D x) (toMul D y)) =
      classTwoSum E.halfExponent (f (toMul D x)) (f (toMul D y))
    simp only [classTwoSum, paperCommutator, map_mul, map_inv, map_pow, hr]

/-- The prime-field structure when every original element has exponent dividing `p`. -/
abbrev zmodModule (p : ℕ) (hpow : ∀ x : G, x ^ p = 1) :
    Module (ZMod p) (ClassTwoAdditive D) :=
  AddCommGroup.zmodModule (by
    intro x
    apply toMul_injective D
    rw [toMul_nsmul, hpow, toMul_zero])

end ClassTwoAdditive

namespace ClassTwoData
variable {G : Type u} [Group G]

def ofOddPrime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hD : commutator G ≤ Subgroup.center G)
    (hpow : ∀ c ∈ commutator G, c ^ p = 1) : ClassTwoData G where
  halfExponent := (p + 1) / 2
  central := hD
  half c hc := by
    have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hodd
    have hr : (p + 1) / 2 + (p + 1) / 2 = p + 1 := by omega
    rw [hr, pow_succ, hpow c hc, one_mul]

end ClassTwoData
end Kourovka2135
