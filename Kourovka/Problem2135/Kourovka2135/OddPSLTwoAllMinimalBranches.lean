import Kourovka2135.OddPSLTwoNonFermatMinimalException
import Kourovka2135.OddPSLTwoFermatBinaryBranch

/-! All odd PSL2 branches in the permitted minimal-simple classification.

The prime-field branch is split by whether the unit-group cardinality is
a power of two. Thompson's numerical condition excludes the small Fermat
parameters, so the broad-trace theorem applies to every remaining Fermat
case. The characteristic-three prime-exponent theorem is imported unchanged;
the final disjunction matches the two corresponding classification entries.
The only classification parameter is the explicit Thompson statement.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoAllMinimalBranches

/-- Thompson's prime-field condition places every Fermat parameter in the
range of the broad-trace argument, without enumerating Fermat primes. -/
theorem seventeen_le_of_fermat_parameter (ell : ℕ) (hp : ell.Prime)
    (hlarge : 3 < ell) (hfive : 5 ∣ ell ^ 2 + 1)
    (hfermat : ∃ n : ℕ, ell - 1 = 2 ^ n) : 17 ≤ ell := by
  obtain ⟨n, hn⟩ := hfermat
  have hnot : ¬ 3 ∣ 2 ^ n := by
    intro hd
    have hbad := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hbad
  rcases OddPSLTwoNonFermatMinimalException.small_parameter_or_seventeen_le
      ell hp hlarge hfive with h7 | h13 | hbound
  · exact (hnot (by rw [← hn, h7]; norm_num)).elim
  · exact (hnot (by rw [← hn, h13]; norm_num)).elim
  · exact hbound

end Kourovka2135.OddPSLTwoAllMinimalBranches

namespace Kourovka2135

open OddPSLTwoProjectiveChart OddPSLTwoAllMinimalBranches

/-- The complete prime-field entry in Thompson's list, with no residual
Fermat, generation, module, or central-cover condition. -/
theorem OrderMinimalException.false_of_binary_prime_field_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (ell : ℕ) [Fact ell.Prime]
    (hlarge : 3 < ell) (hfive : 5 ∣ ell ^ 2 + 1)
    (e : (G ⧸ solubleRadical G) ≃* Q (GaloisField ell 1)) : False := by
  by_cases hfermat : ∃ n : ℕ, ell - 1 = 2 ^ n
  · have hp : ell.Prime := Fact.out
    have hcard : Nat.card (GaloisField ell 1) = ell := by
      simpa only [pow_one] using GaloisField.card ell 1 (by decide)
    have hbound := seventeen_le_of_fermat_parameter ell hp hlarge hfive hfermat
    exact h.false_of_binary_fermat_pslTwo_quotient classification
      (GaloisField ell 1) (by simpa only [hcard] using hp)
      (by simpa only [hcard] using hbound)
      (by simpa only [hcard] using hfermat) e
  · exact h.false_of_binary_nonFermat_prime_quotient classification
      ell hlarge hfive hfermat e

/-- Both odd PSL2 entries of the concrete minimal-simple model list.
The isomorphisms and numerical conditions are precisely classification data. -/
theorem OrderMinimalException.false_of_binary_odd_pslTwo_model_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (hmodel :
      (∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧
        Nonempty ((G ⧸ solubleRadical G) ≃* Q (GaloisField 3 f))) ∨
      (∃ (ell : ℕ) (hp : ell.Prime), 3 < ell ∧ 5 ∣ ell ^ 2 + 1 ∧
        (letI : Fact ell.Prime := ⟨hp⟩
         Nonempty ((G ⧸ solubleRadical G) ≃* Q (GaloisField ell 1))))) : False := by
  rcases hmodel with ⟨f, hf, hf2, ⟨e⟩⟩ | ⟨ell, hp, hlarge, hfive, he⟩
  · exact h.false_of_binary_three_prime_exponent_quotient classification f hf hf2 e
  · let : Fact ell.Prime := ⟨hp⟩
    obtain ⟨e⟩ := he
    exact h.false_of_binary_prime_field_quotient classification ell hlarge hfive e

end Kourovka2135
