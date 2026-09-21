import Kourovka2135.OddPSLTwoProjectiveChart
import Kourovka2135.FinitePermutationHeart
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Option

/-! The actual unipotent subgroup and binary permutation heart of odd PSL2.

The projective root homomorphism is injective, its subgroup has the parameter
field's cardinality, fixes infinity, and is transitive on the affine chart.
For an odd parameter-field cardinality and binary coefficients, averaging
therefore proves that the actual projective permutation heart has no root-
subgroup fixed vectors.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoPermutationHeart

open OddPSLTwoProjectiveChart

variable (F : Type u) [Field F]

def unipotentHom : Multiplicative F →* Q F :=
  (quotient F).comp (SLTwo.uniHom F)

@[simp] theorem unipotentHom_apply (t : F) :
    unipotentHom F (Multiplicative.ofAdd t) = quotient F (SLTwo.uni t) := rfl

/-- The affine action at zero detects the actual root parameter. -/
theorem unipotentHom_injective : Function.Injective (unipotentHom F) := by
  intro a b h
  have he := congrArg (fun g : Q F => g • (some (0 : F) : Option F)) h
  change quotient F (SLTwo.uni a.toAdd) • (some (0 : F) : Option F) =
    quotient F (SLTwo.uni b.toAdd) • (some (0 : F) : Option F) at he
  simp only [uni_smul_some, zero_add, Option.some.injEq] at he
  exact congrArg Multiplicative.ofAdd he

def unipotent : Subgroup (Q F) := (unipotentHom F).range

def member (t : F) : unipotent F :=
  ⟨unipotentHom F (Multiplicative.ofAdd t), ⟨Multiplicative.ofAdd t, rfl⟩⟩

@[simp] theorem member_coe (t : F) :
    (member F t : Q F) = quotient F (SLTwo.uni t) := rfl

theorem card_unipotent : Nat.card (unipotent F) = Nat.card F := by
  calc
    Nat.card (unipotent F) = Nat.card (Multiplicative F) :=
      (Nat.card_congr (MonoidHom.ofInjective (unipotentHom_injective F)).toEquiv).symm
    _ = Nat.card F := (Nat.card_congr (Multiplicative.ofAdd : F ≃ Multiplicative F)).symm

theorem unipotent_le_stabilizer :
    unipotent F ≤ MulAction.stabilizer (Q F) (none : Option F) := by
  rintro _ ⟨t, rfl⟩
  change quotient F (SLTwo.uni t.toAdd) • (none : Option F) = none
  exact uni_smul_none F t.toAdd

/-- A root element with parameter y-x moves affine x to affine y. -/
theorem affine_transitive (x y : Option F) (hx : x ≠ none) (hy : y ≠ none) :
    ∃ g : unipotent F, (g : Q F) • x = y := by
  cases x with
  | none => exact (hx rfl).elim
  | some x =>
      cases y with
      | none => exact (hy rfl).elim
      | some y =>
          refine ⟨member F (y - x), ?_⟩
          rw [member_coe, uni_smul_some]
          congr 1
          abel

variable [Fintype F]
variable (k : Type u) [Field k] [CharP k 2]
variable (hodd : Odd (Fintype.card F))

include hodd

omit [Field F] in
theorem card_field_cast : (Fintype.card F : k) = 1 :=
  natCast_eq_one_of_odd_of_two_eq_zero hodd (CharTwo.two_eq_zero (R := k))

omit [Field F] in
/-- The constant functions lie in the actual augmentation kernel. -/
theorem card_points_cast_zero : (Fintype.card (Option F) : k) = 0 := by
  rw [Fintype.card_option, Nat.cast_add, Nat.cast_one, card_field_cast F k hodd]
  exact CharTwo.add_self_eq_zero (1 : k)

theorem card_unipotent_cast_ne_zero [Fintype (unipotent F)] :
    (Fintype.card (unipotent F) : k) ≠ 0 := by
  have hcard : Fintype.card (unipotent F) = Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using card_unipotent F
  rw [hcard, card_field_cast F k hodd]
  exact one_ne_zero

abbrev Heart := FinitePermutationHeart.Heart k (Option F) (card_points_cast_zero F k hodd)

def heartRepresentation : Representation k (Q F) (Heart F k hodd) :=
  FinitePermutationHeart.representation k (Q F) (Option F) (card_points_cast_zero F k hodd)

/-- The honest root-subgroup fixed-space premise used by the cohomology bridge. -/
theorem heart_unipotent_invariants_eq_bot :
    Representation.invariants ((heartRepresentation F k hodd).comp (unipotent F).subtype) = ⊥ := by
  let : Fintype (unipotent F) := Fintype.ofFinite _
  exact FinitePermutationHeart.heart_invariants_eq_bot
    k (Q F) (Option F) (card_points_cast_zero F k hodd) (unipotent F) none
    (card_unipotent_cast_ne_zero F k hodd) (affine_transitive F)

end Kourovka2135.OddPSLTwoPermutationHeart
