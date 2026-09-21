import Kourovka2135.BinarySplitGoodSetGeneration
import Kourovka2135.BinaryFrattiniGoodSetInduction
import Kourovka2135.MinimalBinaryTerminalGoodSet

/-! The actual split-torus generating-good set through every binary Frattini
kernel. The concrete quotient generation and terminal nonspecial kernel case
are both discharged; no terminal, generation, representation-extension or
character premise remains in the family theorem. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFrattiniSplitGoodSet

open BinarySplitTorusGoodPair

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable [IsSimpleGroup (SLTwo.SL2 F)]
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
variable (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)

include hcard hf hsolv in
/-- The full binary family invariant, with all terminal and quotient-good-set
inputs constructed from the stated actual group and field hypotheses. -/
theorem hasOddGeneratingGoodSetOver
    (r : ℕ) [Fact r.Prime] (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) :
    HasOddGeneratingGoodSetOver pi (splitOrderSet (F := F) r) := by
  have hB := BinarySplitGoodSetGeneration.isGeneratingGoodSet F hsolv hrOdd hrSplit
  have hne := BinarySplitGoodSetGeneration.splitOrderSet_nonempty F hrSplit
  refine binary_frattini_good_set_induction f hcard hf (splitOrderSet (F := F) r) hB
    (fun s hs => BinarySplitGoodSetGeneration.ne_one_of_mem F hs)
    (BinarySplitGoodSetGeneration.exists_odd_member F hrOdd hrSplit) ?_
    pi hpi hR hRΦ
  intro A _ _ _ q hq hker hΦ hnonabelian hnonspecial hmin
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  have ht := minimal_binary_terminal_good_set q.ker hker hmin hnonabelian hΦ
    hnonspecial e.symm f hcard hf r Fact.out hrOdd hB hne
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' q.ker) = q := by
    apply MonoidHom.ext
    intro x
    rfl
  change HasOddGeneratingGoodSetOver
    (e.toMonoidHom.comp (QuotientGroup.mk' q.ker)) (splitOrderSet (F := F) r) at ht
  rwa [hcomp] at ht

/-- A suitable odd split prime exists for every exponent in the actual family. -/
theorem exists_odd_prime_dvd_two_pow_sub_one (n : ℕ) (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ 2 ^ n - 1 := by
  have hpow : 8 ≤ 2 ^ n := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have htwo : 2 ∣ 2 ^ n :=
    even_iff_two_dvd.mp ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega))
  have hrne : r ≠ 2 := by
    intro heq
    subst r
    have hdiv : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub htwo hd
    have hone : 2 ^ n - (2 ^ n - 1) = 1 := by omega
    rw [hone] at hdiv
    exact Nat.prime_two.not_dvd_one hdiv
  exact ⟨r, hr, hr.odd_of_ne_two hrne, hd⟩

include hcard hf hsolv in
/-- One actual nonidentity odd-order element is a single value of every outer
commutator word. It is chosen inside the proved generating-good set. -/
theorem exists_nonidentity_odd_universal_value
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) :
    ∃ x : G, x ≠ 1 ∧ Odd (orderOf x) ∧ ∀ w : OuterWord, x ∈ w.values G := by
  obtain ⟨r, hr, hrOdd, hrSplit⟩ := exists_odd_prime_dvd_two_pow_sub_one f hf
  let : Fact r.Prime := ⟨hr⟩
  have hrSplit' : r ∣ Nat.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card, hcard] using hrSplit
  obtain ⟨Y, hY, hsub, x, hx, hodd⟩ :=
    hasOddGeneratingGoodSetOver f hcard hf hsolv r hrOdd hrSplit' pi hpi hR hRΦ
  refine ⟨x, ?_, hodd, fun w => hY.subset_values w hx⟩
  intro heq
  have hne := BinarySplitGoodSetGeneration.ne_one_of_mem F (hsub hx)
  exact hne (by rw [heq, map_one])

include hcard hf hsolv in
/-- A directly usable single-word consequence of the same actual family theorem. -/
theorem exists_nonidentity_odd_value
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) (w : OuterWord) :
    ∃ x ∈ w.values G, x ≠ 1 ∧ Odd (orderOf x) := by
  obtain ⟨x, hne, hodd, hx⟩ :=
    exists_nonidentity_odd_universal_value f hcard hf hsolv pi hpi hR hRΦ
  exact ⟨x, hx w, hne, hodd⟩

end Kourovka2135.BinaryFrattiniSplitGoodSet
