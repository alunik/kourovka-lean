import Kourovka2135.OddPSLTwoSplitNoncentralBranch
import Kourovka2135.OddPSLTwoCentralObstruction
import Kourovka2135.OddPSLTwoSplitPrimeArithmetic

/-! Complete binary least-exception exclusion for odd PSL2 parameters
with an odd split-torus prime. Central and noncentral radicals are both
included. The explicit Thompson premise is used only by the noncentral
branch's proper-subgroup-solubility reduction. Arithmetic corollaries cover
every field size at least seventeen whose size minus one is not a power of
two, and every odd power 3^f with f at least three.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open OddPSLTwoProjectiveChart

theorem OrderMinimalException.false_of_binary_odd_pslTwo_split_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (F : Type) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (r : ℕ) [Fact r.Prime] (hrOdd : Odd r) (hsplit : r ∣ Nat.card F - 1)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  by_cases hc : solubleRadical G ≤ Subgroup.center G
  · exact h.false_of_central_radical_odd_pslTwo_quotient hodd (by omega) hc e
  · exact h.false_of_binary_odd_pslTwo_split_noncentral classification hc
      F hodd hsize r hrOdd hsplit e

/-- Uniformly covers all non-power-of-two split torus orders, including
every corresponding prime field. -/
theorem OrderMinimalException.false_of_binary_odd_pslTwo_not_two_power_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (F : Type) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hsize : 17 ≤ Nat.card F)
    (hnot : ¬ ∃ k : ℕ, Nat.card F - 1 = 2 ^ k)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  obtain ⟨r, hr, ho, hd⟩ :=
    OddPSLTwoSplitPrimeArithmetic.exists_odd_prime_dvd_sub_one_of_not_two_pow hnot
  let : Fact r.Prime := ⟨hr⟩
  exact h.false_of_binary_odd_pslTwo_split_quotient classification F hodd hsize r ho hd e

/-- The full odd-exponent characteristic-three family, with no centrality
or noncentrality condition on the radical. -/
theorem OrderMinimalException.false_of_binary_pslTwo_three_odd_power_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (F : Type) [Field F] [Finite F]
    (f : ℕ) (hf : Odd f) (hsize : 3 ≤ f) (hcard : Nat.card F = 3 ^ f)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  obtain ⟨r, hr, ho, hd⟩ :=
    OddPSLTwoSplitPrimeArithmetic.exists_odd_prime_dvd_three_pow_sub_one hf hsize
  let : Fact r.Prime := ⟨hr⟩
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (by decide : Odd 3).pow
  have hbound : 17 ≤ Nat.card F := by
    rw [hcard]
    exact OddPSLTwoSplitPrimeArithmetic.seventeen_le_three_pow hsize
  exact h.false_of_binary_odd_pslTwo_split_quotient classification F hodd hbound
    r ho (by simpa only [hcard] using hd) e

end Kourovka2135
