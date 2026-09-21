import Kourovka2135.SuzukiBruhat
import Kourovka2135.RegularAugmentationCoordinates

/-! Actual Suzuki ovoid augmentation, over an arbitrary coefficient field.

The root-restriction equivalence is valid in every characteristic. In
characteristic two the actual augmentation is irreducible, by the explicit
root norm and ovoid transitivity. No Suzuki module classification or group
simplicity assumption is used. The construction includes m = 0.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiOvoidAugmentation

open SuzukiGeometry FinitePermutationAugmentation

instance ovoidFintype (m : ℕ) : Fintype (Ovoid m) := Fintype.ofFinite _
instance rootFintype (m : ℕ) : Fintype (root m) := Fintype.ofFinite _

abbrev Augmentation (L : Type) [Field L] (m : ℕ) := Space L (Ovoid m)

def representation (L : Type) [Field L] (m : ℕ) :
    Representation L (G m) (Augmentation L m) := action L (G m) (Ovoid m)

def baseFinitePoint (m : ℕ) : Ovoid m := finiteOvoid m (0, 0)

theorem baseFinitePoint_ne_infinity (m : ℕ) : baseFinitePoint m ≠ infinityOvoid m := by
  intro h
  apply infinity_not_mem_finitePoint_range m
  exact ⟨(0, 0), congrArg Subtype.val h⟩

theorem transitive (m : ℕ) (x : Ovoid m) : ∃ g : G m, g • infinityOvoid m = x := by
  let : MulAction.IsPretransitive (G m) (Ovoid m) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact MulAction.exists_smul_eq (G m) (infinityOvoid m) x

/-- Exact root-subgroup restriction to the genuine group-algebra regular module. -/
def rootRestrictionEquiv (L : Type) [Field L] (m : ℕ) :
    Representation.Equiv ((representation L m).comp (root m).subtype)
      (Representation.leftRegular L (root m)) :=
  RegularAugmentationCoordinates.regularEquiv L (G m) (Ovoid m)
    (root m) (infinityOvoid m) (root_fixes_infinity m) (root_regular m)
    (baseFinitePoint m) (baseFinitePoint_ne_infinity m)

theorem finrank_augmentation (L : Type) [Field L] (m : ℕ) :
    Module.finrank L (Augmentation L m) = (q m) ^ 2 := by
  calc
    Module.finrank L (Augmentation L m) = Fintype.card (root m) :=
      RegularAugmentationCoordinates.finrank_space L (G m) (Ovoid m)
        (root m) (infinityOvoid m) (root_fixes_infinity m) (root_regular m)
        (baseFinitePoint m) (baseFinitePoint_ne_infinity m)
    _ = (q m) ^ 2 := by simpa only [Nat.card_eq_fintype_card] using card_root m

variable (L : Type) [Field L] [CharP L 2]

theorem card_ovoid_cast (m : ℕ) : (Fintype.card (Ovoid m) : L) = 1 := by
  have hodd : Odd (Fintype.card (Ovoid m)) := by
    rw [← Nat.card_eq_fintype_card, card_ovoid]
    exact ((even_q m).pow_of_ne_zero (by decide : 2 ≠ 0)).add_one
  exact natCast_eq_one_of_odd_of_two_eq_zero hodd (CharTwo.two_eq_zero (R := L))

/-- Actual irreducibility over every binary coefficient field, including all extensions. -/
theorem isIrreducible (m : ℕ) : (representation L m).IsIrreducible :=
  RegularAugmentationIrreducible.isIrreducible L (G m) (Ovoid m)
    (card_ovoid_cast L m) (root m) (infinityOvoid m) (root_fixes_infinity m)
    (root_regular m) (baseFinitePoint m) (baseFinitePoint_ne_infinity m) (transitive m)

/-- The explicit rank-one root norm on the actual augmentation space. -/
theorem root_norm (m : ℕ) (f : Augmentation L m) :
    (∑ a : root m, representation L m (a : G m) f) =
      (f : Ovoid m → L) (infinityOvoid m) •
        RegularAugmentationIrreducible.complementVector L (Ovoid m)
          (card_ovoid_cast L m) (infinityOvoid m) :=
  RegularAugmentationIrreducible.norm_eq L (G m) (Ovoid m)
    (card_ovoid_cast L m) (root m) (infinityOvoid m) (root_fixes_infinity m)
    (root_regular m) (baseFinitePoint m) (baseFinitePoint_ne_infinity m) f

end Kourovka2135.SuzukiOvoidAugmentation
