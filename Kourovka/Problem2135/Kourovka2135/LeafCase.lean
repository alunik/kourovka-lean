import Kourovka2135.Statement
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The one-variable case, without classification

For the leaf word every group element is a value. The product-order condition
then makes the set of p′-elements a subgroup, which is the required complement.
This argument cannot be used for a general word: its single-value set need not
be closed under multiplication.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

namespace LeafCase

variable {p : ℕ} {G : Type u} [Group G]

/-- Under the leaf-word hypothesis, all elements of order prime to p form
a subgroup. -/
def primeToSubgroup (hp : p.Prime) (h : ProductOrderCondition .leaf p G) : Subgroup G where
  carrier := {x | ¬ p ∣ orderOf x}
  one_mem' := by simpa only [Set.mem_ofPred_eq, orderOf_one] using hp.not_dvd_one
  mul_mem' := by
    intro a b ha hb hab
    change ¬ p ∣ orderOf a at ha
    have hai : ¬ p ∣ orderOf a⁻¹ := by simpa only [orderOf_inv] using ha
    have ht := h a⁻¹ (by simp) (a * b) (by simp) hai hab
    exact hb (by simpa only [inv_mul_cancel_left] using ht)
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, orderOf_inv] using ha

@[simp]
theorem mem_primeToSubgroup (hp : p.Prime) (h : ProductOrderCondition .leaf p G) (x : G) :
    x ∈ primeToSubgroup hp h ↔ ¬ p ∣ orderOf x := Iff.rfl

instance primeToSubgroup_normal (hp : p.Prime) (h : ProductOrderCondition .leaf p G) :
    (primeToSubgroup hp h).Normal where
  conj_mem := by
    intro x hx g
    have heq : orderOf (g * x * g⁻¹) = orderOf x := by
      simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
    change ¬ p ∣ orderOf (g * x * g⁻¹)
    rw [heq]
    exact hx

theorem card_coprime [Finite G] (hp : p.Prime)
    (h : ProductOrderCondition .leaf p G) : (Nat.card (primeToSubgroup hp h)).Coprime p := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := primeToSubgroup hp h) p hd
  have hnot : ¬ p ∣ orderOf (x : G) := x.property
  apply hnot
  rw [Subgroup.orderOf_coe, hx]

theorem quotient_isPGroup [Finite G] (hp : p.Prime)
    (h : ProductOrderCondition .leaf p G) : IsPGroup p (G ⧸ primeToSubgroup hp h) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (primeToSubgroup hp h) q
  obtain ⟨k, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (x ^ p ^ k)).mpr
  change ¬ p ∣ orderOf (x ^ p ^ k)
  have hpow : (x ^ p ^ k) ^ m = 1 := by
    rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  have hd : orderOf (x ^ p ^ k) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hpow
  exact fun hc => hm (hc.trans hd)

end LeafCase

/-- The leaf-word hypothesis implies that G itself has a normal p-complement. -/
theorem hasNormalPComplement_of_leaf_condition
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (h : ProductOrderCondition .leaf p G) : HasNormalPComplement p G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (LeafCase.quotient_isPGroup hp h)
  refine ⟨LeafCase.primeToSubgroup hp h, inferInstance, LeafCase.card_coprime hp h, n, ?_⟩
  rw [Subgroup.index_eq_card]
  exact hn

/-- The exact forward conclusion of 21.35 for the one-variable word. -/
theorem problem2135_leaf
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (h : ProductOrderCondition .leaf p G) :
    HasNormalPComplement p (OuterWord.leaf.verbalSubgroup G) :=
  hasNormalPComplement_of_leaf_condition hp (h.subgroup _)

end Kourovka2135
