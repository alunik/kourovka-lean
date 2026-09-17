import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Conj
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Kourovka.Problem2153

universe u v

/-- The entire ambient conjugacy class. -/
def InvolutionClass {G : Type u} [Group G] (d : G) := {x : G // IsConj d x}

def PreservesColour {G : Type u} [Group G] {d : G}
    (t : ℕ) (τ : Equiv.Perm (InvolutionClass d)) : Prop :=
  ∀ a b, a ≠ b → orderOf (a.val * b.val) = t →
    orderOf ((τ a).val * (τ b).val) = t

def PreservesAllColours {G : Type u} [Group G] {d : G}
    (τ : Equiv.Perm (InvolutionClass d)) : Prop :=
  ∀ a b, a ≠ b → orderOf (a.val * b.val) =
    orderOf ((τ a).val * (τ b).val)

/-- `2,p` are the two smallest prime divisors of the ambient group order. -/
def TwoSmallestPrimeDivisors (n p : ℕ) : Prop :=
  2 ∣ n ∧ p.Prime ∧ 2 < p ∧ p ∣ n ∧
    ∀ q, q.Prime → q ∣ n → 2 < q → p ≤ q

def Nonabelian (G : Type u) [Group G] : Prop := ∃ a b : G, a * b ≠ b * a

/-- The universal assertion in Problem 21.53, on whole conjugacy classes. -/
def Statement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], Nonabelian G →
    ∀ (d : G), orderOf d = 2 → ∀ p, TwoSmallestPrimeDivisors (Nat.card G) p →
      {τ : Equiv.Perm (InvolutionClass d) | PreservesAllColours τ} =
      {τ | PreservesColour 2 τ ∧ PreservesColour p τ}

theorem twoSmallestPrimeDivisors_three {n : ℕ} (h2 : 2 ∣ n) (h3 : 3 ∣ n) :
    TwoSmallestPrimeDivisors n 3 := by
  exact ⟨h2, by decide, by decide, h3, fun q _ _ hq => hq⟩

/-- The order expression used in the proposed Ree construction, with field size 8. -/
def reeEightOrder : ℕ := 8 ^ 12 * (8 - 1) * (8 ^ 3 + 1) * (8 ^ 4 - 1) * (8 ^ 6 + 1)

theorem reeEightOrder_primes : TwoSmallestPrimeDivisors reeEightOrder 3 := by
  apply twoSmallestPrimeDivisors_three <;> norm_num [reeEightOrder]

theorem orderOf_mul_reverse {G : Type u} [Group G] (a b : G) :
    orderOf (a * b) = orderOf (b * a) := by
  apply SemiconjBy.orderOf_eq b
  exact (mul_assoc b a b).symm

theorem orderOf_conjugate {G : Type u} [Group G] {d x : G} (h : IsConj d x) :
    orderOf d = orderOf x := by
  rcases isConj_iff.mp h with ⟨g, rfl⟩
  apply SemiconjBy.orderOf_eq g
  simp [SemiconjBy, mul_assoc]

theorem class_orderOf {G : Type u} [Group G] {d : G} (hd : orderOf d = 2)
    (x : InvolutionClass d) : orderOf x.val = 2 :=
  (orderOf_conjugate x.property).symm.trans hd

theorem involution_mul_self {G : Type u} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  simpa [hx, pow_two] using pow_orderOf_eq_one x

theorem involution_inv {G : Type u} [Group G] {x : G} (hx : orderOf x = 2) :
    x⁻¹ = x := by
  exact inv_eq_of_mul_eq_one_right (involution_mul_self hx)

/-- Swapping twins preserves a symmetric relation; only external neighborhoods are needed. -/
theorem swap_preserves_relation {α : Type v} [DecidableEq α] (R : α → α → Prop)
    (hSymm : ∀ a b, R a b → R b a) (x y : α)
    (hTwin : ∀ z, z ≠ x → z ≠ y → (R x z ↔ R y z)) :
    ∀ a b, a ≠ b → R a b → R (Equiv.swap x y a) (Equiv.swap x y b) := by
  intro a b hab hR
  by_cases hax : a = x
  · subst a
    by_cases hby : b = y
    · subst b
      simpa using hSymm x y hR
    · have hbx : b ≠ x := Ne.symm hab
      simpa [Equiv.swap_apply_of_ne_of_ne hbx hby] using (hTwin b hbx hby).mp hR
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        simpa using hSymm y x hR
      · have hby : b ≠ y := Ne.symm hab
        simpa [Equiv.swap_apply_of_ne_of_ne hbx hby] using (hTwin b hbx hby).mpr hR
    · by_cases hbx : b = x
      · subst b
        simpa [Equiv.swap_apply_of_ne_of_ne hax hay] using
          hSymm y a ((hTwin a hax hay).mp (hSymm a x hR))
      · by_cases hby : b = y
        · subst b
          simpa [Equiv.swap_apply_of_ne_of_ne hax hay] using
            hSymm x a ((hTwin a hax hay).mpr (hSymm a y hR))
        · simpa [Equiv.swap_apply_of_ne_of_ne hax hay,
            Equiv.swap_apply_of_ne_of_ne hbx hby] using hR

/-- Twin neighborhoods for the product-order relation, on the whole conjugacy class. -/
def ColourTwins {G : Type u} [Group G] {d : G} (t : ℕ)
    (x y : InvolutionClass d) : Prop :=
  ∀ z, z ≠ x → z ≠ y → (orderOf (x.val * z.val) = t ↔ orderOf (y.val * z.val) = t)

theorem swap_preservesColour {G : Type u} [Group G] {d : G}
    [DecidableEq (InvolutionClass d)] (t : ℕ) (x y : InvolutionClass d)
    (hTwin : ColourTwins t x y) : PreservesColour t (Equiv.swap x y) := by
  apply swap_preserves_relation (fun a b : InvolutionClass d => orderOf (a.val * b.val) = t)
  · intro a b h
    rwa [orderOf_mul_reverse]
  · exact hTwin

theorem orderOf_mul_self_class {G : Type u} [Group G] {d : G} (hd : orderOf d = 2)
    (a : InvolutionClass d) : orderOf (a.val * a.val) = 1 := by
  simp [involution_mul_self (class_orderOf hd a)]

/-- Exact orders 5 and 7 force the third vertex outside the transposition. -/
theorem witness_ne {G : Type u} [Group G] {d : G} (hd : orderOf d = 2)
    (a x y : InvolutionClass d) (h5 : orderOf (a.val * x.val) = 5)
    (h7 : orderOf (a.val * y.val) = 7) : a ≠ x ∧ a ≠ y ∧ x ≠ y := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; subst x
    have := orderOf_mul_self_class hd a
    omega
  · intro h; subst y
    have := orderOf_mul_self_class hd a
    omega
  · intro h; subst y; omega

/-- Complete abstract transposition bridge. All ambient structural facts remain hypotheses. -/
theorem swap_counterexample {G : Type u} [Group G] {d : G} (hd : orderOf d = 2)
    [DecidableEq (InvolutionClass d)] (a x y : InvolutionClass d)
    (h2 : ColourTwins 2 x y) (h3 : ColourTwins 3 x y)
    (h5 : orderOf (a.val * x.val) = 5) (h7 : orderOf (a.val * y.val) = 7) :
    PreservesColour 2 (Equiv.swap x y) ∧ PreservesColour 3 (Equiv.swap x y) ∧
      ¬ PreservesAllColours (Equiv.swap x y) := by
  refine ⟨swap_preservesColour 2 x y h2, swap_preservesColour 3 x y h3, ?_⟩
  intro hAll
  obtain ⟨hax, hay, _⟩ := witness_ne hd a x y h5 h7
  have hh := hAll a x hax
  rw [Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_left, h5, h7] at hh
  norm_num at hh

/-- For distinct involutions, product order two is equivalent to commuting. -/
theorem orderOf_mul_eq_two_iff {G : Type u} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hne : x ≠ y) :
    orderOf (x * y) = 2 ↔ Commute x y := by
  constructor
  · intro hxy
    have hi := involution_inv hxy
    rw [mul_inv_rev, involution_inv hx, involution_inv hy] at hi
    exact hi.symm
  · intro hc
    apply orderOf_eq_prime
    · rw [hc.mul_pow, show x ^ 2 = 1 by simpa [hx] using pow_orderOf_eq_one x,
        show y ^ 2 = 1 by simpa [hy] using pow_orderOf_eq_one y, mul_one]
    · intro h
      apply hne
      have := mul_eq_one_iff_eq_inv.mp h
      simpa [involution_inv hy] using this

/-- An elementwise formulation of equal ambient centralizers is sufficient. -/
theorem colourTwins_two_of_same_centralizer {G : Type u} [Group G] {d : G}
    (hd : orderOf d = 2) (x y : InvolutionClass d)
    (hc : ∀ g : G, Commute x.val g ↔ Commute y.val g) : ColourTwins 2 x y := by
  intro z hzx hzy
  have hxz : x.val ≠ z.val := fun h => hzx (Subtype.ext h.symm)
  have hyz : y.val ≠ z.val := fun h => hzy (Subtype.ext h.symm)
  rw [orderOf_mul_eq_two_iff (class_orderOf hd x) (class_orderOf hd z) hxz,
    orderOf_mul_eq_two_iff (class_orderOf hd y) (class_orderOf hd z) hyz]
  exact hc z.val

/-- The same bridge stated using mathlib's actual ambient centralizer subgroups. -/
theorem colourTwins_two_of_centralizer_eq {G : Type u} [Group G] {d : G}
    (hd : orderOf d = 2) (x y : InvolutionClass d)
    (hc : Subgroup.centralizer ({x.val} : Set G) = Subgroup.centralizer ({y.val} : Set G)) :
    ColourTwins 2 x y := by
  apply colourTwins_two_of_same_centralizer hd x y
  intro g
  have hm : g ∈ Subgroup.centralizer ({x.val} : Set G) ↔
      g ∈ Subgroup.centralizer ({y.val} : Set G) := by rw [hc]
  simpa only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    Commute, SemiconjBy] using hm

theorem involution_inverts_product {G : Type u} [Group G] {b c : G}
    (hb : orderOf b = 2) (hc : orderOf c = 2) :
    b * (b * c) * b⁻¹ = (b * c)⁻¹ := by
  rw [← mul_assoc b b c, involution_mul_self hb, one_mul,
    mul_inv_rev, involution_inv hb, involution_inv hc]

/-- This is an explicit structural hypothesis, not a claimed theorem about a Ree group. -/
def NoThreeInversion {G : Type u} [Group G] (d : G) : Prop :=
  ∀ b : InvolutionClass d, ∀ g : G, orderOf g = 3 → b.val * g * b.val⁻¹ ≠ g⁻¹

theorem no_orderThree_products {G : Type u} [Group G] {d : G}
    (hd : orderOf d = 2) (hn : NoThreeInversion d) (b c : InvolutionClass d) :
    orderOf (b.val * c.val) ≠ 3 := by
  intro h3
  exact hn b (b.val * c.val) h3
    (involution_inverts_product (class_orderOf hd b) (class_orderOf hd c))

theorem colourTwins_three_of_noThreeInversion {G : Type u} [Group G] {d : G}
    (hd : orderOf d = 2) (hn : NoThreeInversion d) (x y : InvolutionClass d) :
    ColourTwins 3 x y := by
  intro z _ _
  exact iff_of_false (no_orderThree_products hd hn x z) (no_orderThree_products hd hn y z)

/-- The exact order-five product itself proves the ambient group is nonabelian. -/
theorem nonabelian_of_order_five {G : Type u} [Group G] {a x : G}
    (ha : orderOf a = 2) (hx : orderOf x = 2) (h5 : orderOf (a * x) = 5) :
    Nonabelian G := by
  refine ⟨a, x, ?_⟩
  intro heq
  have hc : Commute a x := heq
  have hp : (a * x) ^ 2 = 1 := by
    rw [hc.mul_pow, show a ^ 2 = 1 by simpa [ha] using pow_orderOf_eq_one a,
      show x ^ 2 = 1 by simpa [hx] using pow_orderOf_eq_one x, mul_one]
  have hd : orderOf (a * x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hp
  norm_num [h5] at hd

/-- A finite simple ambient realization of the explicit hypotheses refutes 21.53. -/
theorem not_statement_of_swap {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {d : G} (hd : orderOf d = 2) (hcard2 : 2 ∣ Nat.card G) (hcard3 : 3 ∣ Nat.card G)
    (a x y : InvolutionClass d) (h2 : ColourTwins 2 x y) (h3 : ColourTwins 3 x y)
    (h5 : orderOf (a.val * x.val) = 5) (h7 : orderOf (a.val * y.val) = 7) :
    ¬ Statement.{u} := by
  classical
  intro hStatement
  have heq := hStatement G
    (nonabelian_of_order_five (class_orderOf hd a) (class_orderOf hd x) h5)
    d hd 3 (twoSmallestPrimeDivisors_three hcard2 hcard3)
  obtain ⟨hs2, hs3, hsAll⟩ := swap_counterexample hd a x y h2 h3 h5 h7
  apply hsAll
  exact (Set.ext_iff.mp heq (Equiv.swap x y)).mpr ⟨hs2, hs3⟩

/-- The published structural inputs are isolated in transparent hypotheses. -/
theorem not_statement_of_structural_witness
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G] {d : G}
    (hd : orderOf d = 2) (hcard : Nat.card G = reeEightOrder)
    (a x y : InvolutionClass d)
    (hc : ∀ g : G, Commute x.val g ↔ Commute y.val g)
    (hn : NoThreeInversion d)
    (h5 : orderOf (a.val * x.val) = 5) (h7 : orderOf (a.val * y.val) = 7) :
    ¬ Statement.{u} := by
  have hp := reeEightOrder_primes
  rw [← hcard] at hp
  exact not_statement_of_swap hd hp.1 hp.2.2.2.1 a x y
    (colourTwins_two_of_same_centralizer hd x y hc)
    (colourTwins_three_of_noThreeInversion hd hn x y) h5 h7

#print axioms swap_preserves_relation
#print axioms swap_counterexample
#print axioms orderOf_mul_eq_two_iff
#print axioms no_orderThree_products
#print axioms nonabelian_of_order_five
#print axioms reeEightOrder_primes
#print axioms not_statement_of_swap
#print axioms not_statement_of_structural_witness

end Kourovka.Problem2153
