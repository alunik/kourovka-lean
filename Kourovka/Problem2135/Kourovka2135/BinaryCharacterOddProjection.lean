import Kourovka2135.ModularCharacterIndependence
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

/-! A fixed odd-part projection and actual modular simple-type upper bound.

For an element killed by 11232=32*351, the power g^352 has odd order.
The commuting operators rho(g) and rho(g)^352 have equal 32nd powers;
their difference is nilpotent in characteristic two and has trace zero.
Thus ordinary field-valued trace is unchanged. An actual finite conjugacy
cover of odd-order elements now bounds the number of distinct simple types.
No Brauer class-count theorem or group-algebra semisimplicity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCharacterOddProjection

section Trace

variable {k V : Type*} [Field k] [CharP k 2]
variable [AddCommGroup V] [Module k V]

/-- Commuting operators with equal 2-power powers have the same actual trace. -/
theorem trace_eq_of_pow_two_pow_eq (A B : Module.End k V) (n : ℕ)
    (hcomm : Commute A B) (hpow : A ^ (2 ^ n) = B ^ (2 ^ n)) :
    LinearMap.trace k V A = LinearMap.trace k V B := by
  classical
  by_cases hV : Subsingleton V
  · let : Subsingleton V := hV
    exact congrArg (LinearMap.trace k V) (Subsingleton.elim A B)
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : CharP (Module.End k V) 2 :=
      charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective 2
    have hn : IsNilpotent (A - B) := by
      refine ⟨2 ^ n, ?_⟩
      rw [sub_pow_char_pow_of_commute 2 n hcomm, hpow, sub_self]
    have hz : LinearMap.trace k V (A - B) = 0 :=
      isNilpotent_iff_eq_zero.mp (LinearMap.isNilpotent_trace_of_isNilpotent hn)
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz

variable {G : Type*} [Group G] (ρ : Representation k G V)

/-- The ordinary characteristic-two trace is unchanged by the fixed odd-part
power for every actual element killed by 11232. -/
theorem character_pow352 (g : G) (hg : g ^ 11232 = 1) :
    ρ.character g = ρ.character (g ^ 352) := by
  have hA : (ρ g) ^ 11232 = 1 := by rw [← map_pow, hg, map_one]
  have hpow : (ρ g) ^ (2 ^ 5) = ((ρ g) ^ 352) ^ (2 ^ 5) := by
    change (ρ g) ^ 32 = ((ρ g) ^ 352) ^ 32
    calc
      (ρ g) ^ 32 = (ρ g) ^ 11232 * (ρ g) ^ 32 := by rw [hA, one_mul]
      _ = (ρ g) ^ (11232 + 32) := (pow_add _ _ _).symm
      _ = ((ρ g) ^ 352) ^ 32 := by rw [← pow_mul]
  change LinearMap.trace k V (ρ g) = LinearMap.trace k V (ρ (g ^ 352))
  rw [map_pow]
  exact trace_eq_of_pow_two_pow_eq (ρ g) ((ρ g) ^ 352) 5
    ((Commute.refl (ρ g)).pow_right 352) hpow

end Trace

section Group

variable {G : Type*} [Group G]

/-- The projected element is killed by the actual odd number 351. -/
theorem pow352_pow351 (g : G) (hg : g ^ 11232 = 1) : (g ^ 352) ^ 351 = 1 := by
  calc
    (g ^ 352) ^ 351 = (g ^ 11232) ^ 11 := by norm_num [← pow_mul]
    _ = 1 := by rw [hg, one_pow]

theorem odd_orderOf_pow352 (g : G) (hg : g ^ 11232 = 1) : Odd (orderOf (g ^ 352)) :=
  Odd.of_dvd_nat (by decide : Odd 351) (orderOf_dvd_of_pow_eq_one (pow352_pow351 g hg))

end Group

section Count

variable {k G ι J : Type*} [Field k] [IsAlgClosed k] [CharP k 2] [Group G]
variable [Fintype ι] [Fintype J]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable [∀ i, Module.Finite k (V i)]
variable (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
variable (hneq : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))

include hneq

/-- An actual conjugacy cover of the odd-order elements bounds the number
of distinct simple representation types; no class-count assertion is assumed. -/
theorem card_le_of_odd_conjugacy_cover
    (hpow : ∀ g : G, g ^ 11232 = 1) (c : J → G)
    (hcover : ∀ g : G, Odd (orderOf g) → ∃ j : J, IsConj (c j) g) :
    Fintype.card ι ≤ Fintype.card J := by
  apply ModularCharacterIndependence.card_le_of_character_cover ρ hneq c
  intro g
  obtain ⟨j, hj⟩ := hcover (g ^ 352) (odd_orderOf_pow352 g (hpow g))
  obtain ⟨a, ha⟩ := isConj_iff.mp hj
  refine ⟨j, fun i => ?_⟩
  rw [character_pow352 (ρ i) g (hpow g), ← ha]
  exact (ρ i).char_conj (c j) a

/-- The actual cardinal divisibility certificate already available for PSL3(3)
supplies the exponent premise without an exact cardinality formula. -/
theorem card_le_of_odd_conjugacy_cover_of_card_dvd [Finite G]
    (hcard : Nat.card G ∣ 11232) (c : J → G)
    (hcover : ∀ g : G, Odd (orderOf g) → ∃ j : J, IsConj (c j) g) :
    Fintype.card ι ≤ Fintype.card J := by
  apply card_le_of_odd_conjugacy_cover ρ hneq (fun g => ?_) c hcover
  exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hcard)

end Count

end Kourovka2135.BinaryCharacterOddProjection
