import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Data.Finite.Perm

/-! Elementary bounds on automorphisms of groups of order two or four.

An automorphism permutes the nonidentity elements faithfully. Thus its
order divides `(card E - 1)!`. In particular a binary-order automorphism
of a group of order four squares to the identity. No classification of
groups or automorphism groups is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SmallNormalTwoAction

variable {E : Type*} [Group E]

def nonidentityPerm : MulAut E →* Equiv.Perm {x : E // x ≠ 1} where
  toFun a :=
    { toFun x := ⟨a x, fun h => x.property (a.injective (h.trans a.map_one.symm))⟩
      invFun x := ⟨a.symm x, fun h => x.property (a.symm.injective
        (h.trans a.symm.map_one.symm))⟩
      left_inv x := Subtype.ext (a.symm_apply_apply x)
      right_inv x := Subtype.ext (a.apply_symm_apply x) }
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem nonidentityPerm_injective : Function.Injective (nonidentityPerm (E := E)) := by
  intro a b h
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val (congrArg (fun p => p ⟨x, hx⟩) h)

theorem orderOf_dvd_factorial [Finite E] (a : MulAut E) :
    orderOf a ∣ (Nat.card E - 1).factorial := by
  classical
  let : Fintype E := Fintype.ofFinite E
  have hc : Nat.card {x : E // x ≠ 1} = Nat.card E - 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have hd := orderOf_dvd_natCard (nonidentityPerm a)
  rw [Nat.card_perm, hc,
    orderOf_injective nonidentityPerm nonidentityPerm_injective] at hd
  exact hd

theorem eq_one_of_card_two [Finite E] (hc : Nat.card E = 2) (a : MulAut E) :
    a = 1 := by
  have hd := orderOf_dvd_factorial a
  have hfac : (Nat.card E - 1).factorial = 1 := by rw [hc]; decide
  rw [hfac] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem sq_eq_one_of_card_four [Finite E] (hc : Nat.card E = 4)
    (a : MulAut E) (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1) : a ^ 2 = 1 := by
  obtain ⟨n, hn⟩ := ha
  have hd := orderOf_dvd_factorial a
  have hp := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (orderOf a) 3 :=
    Nat.Coprime.of_dvd_left hp ((by decide : Nat.Coprime 2 3).pow_left n)
  have hfac : (Nat.card E - 1).factorial = 2 * 3 := by rw [hc]; decide
  rw [hfac] at hd
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_mul_right.mp hd)

variable {G : Type*} [Group G]

theorem conjugation_eq_one_of_card_two (N : Subgroup G) [N.Normal] [Finite N]
    (hc : Nat.card N = 2) (g : G) : MulAut.conjNormal g = (1 : MulAut N) :=
  eq_one_of_card_two hc _

theorem conjugation_sq_eq_one_of_card_four (N : Subgroup G) [N.Normal] [Finite N]
    (hc : Nat.card N = 4) (g : G) (hg : ∃ n : ℕ, g ^ (2 ^ n) = 1) :
    MulAut.conjNormal (g ^ 2) = (1 : MulAut N) := by
  rw [map_pow]
  apply sq_eq_one_of_card_four hc
  obtain ⟨n, hn⟩ := hg
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

end Kourovka2135.SmallNormalTwoAction
