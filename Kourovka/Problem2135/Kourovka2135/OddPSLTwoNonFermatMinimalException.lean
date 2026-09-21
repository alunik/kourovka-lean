import Kourovka2135.OddPSLTwoSplitBinaryBranch
import Kourovka2135.SmallOddPSLTwoBinaryBranch
import Mathlib.FieldTheory.Finite.GaloisField

/-! Classification-native odd PSL2 exclusions for the binary least exception.

The characteristic-three family is handled for every prime exponent other
than two. The prime-field family uses exactly Thompson's numerical condition
`5 ∣ ell^2 + 1`, with the remaining Fermat parameters explicitly excluded.
The small parameters seven and thirteen are transported through genuine
finite-field and projective-group isomorphisms. No module, central-cover, or
good-set premise remains in these endpoints.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoNonFermatMinimalException

open OddPSLTwoProjectiveChart

/-- Entrywise transport along an actual field isomorphism. -/
def specialLinearEquiv {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    SLTwo.SL2 F ≃* SLTwo.SL2 K where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    ext i j
    change e.symm (e (g.val i j)) = g.val i j
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    ext i j
    change e (e.symm (g.val i j)) = g.val i j
    exact e.apply_symm_apply _
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

/-- The same field isomorphism transports the actual center quotients. -/
def projectiveEquiv {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    Q F ≃* Q K :=
  QuotientGroup.congr (Subgroup.center (SLTwo.SL2 F))
    (Subgroup.center (SLTwo.SL2 K)) (specialLinearEquiv e)
    (Subgroup.map_center_eq (specialLinearEquiv e))

/-- The degree-one Galois-field model is the corresponding prime field. -/
def primeFieldEquiv (ell : ℕ) [Fact ell.Prime] :
    Q (GaloisField ell 1) ≃* Q (ZMod ell) :=
  projectiveEquiv (GaloisField.equivZmodP ell).toRingEquiv

/-- Thompson's prime-field restriction eliminates five and eleven from
the primes strictly between three and seventeen. -/
theorem small_parameter_or_seventeen_le (ell : ℕ) (hp : ell.Prime)
    (hlarge : 3 < ell) (hfive : 5 ∣ ell ^ 2 + 1) :
    ell = 7 ∨ ell = 13 ∨ 17 ≤ ell := by
  by_cases h7 : ell = 7
  · exact Or.inl h7
  by_cases h13 : ell = 13
  · exact Or.inr (Or.inl h13)
  refine Or.inr (Or.inr ?_)
  by_contra hb
  have hlt : ell < 17 := by omega
  have hsmall : ∀ i : Fin 17, i.val.Prime → 3 < i.val → 5 ∣ i.val ^ 2 + 1 →
      i.val = 7 ∨ i.val = 13 := by decide
  rcases hsmall ⟨ell, hlt⟩ hp hlarge hfive with he | he
  · exact h7 he
  · exact h13 he

end Kourovka2135.OddPSLTwoNonFermatMinimalException

namespace Kourovka2135

open OddPSLTwoProjectiveChart OddPSLTwoNonFermatMinimalException

/-- The entire characteristic-three family in Thompson's list is excluded
for a binary least exception, including central radicals. -/
theorem OrderMinimalException.false_of_binary_three_prime_exponent_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (f : ℕ) (hf : f.Prime) (hf2 : f ≠ 2)
    (e : (G ⧸ solubleRadical G) ≃* Q (GaloisField 3 f)) : False := by
  have hfOdd : Odd f := hf.odd_of_ne_two hf2
  have hsize : 3 ≤ f := by have := hf.two_le; omega
  exact h.false_of_binary_pslTwo_three_odd_power_quotient classification
    (GaloisField 3 f) f hfOdd hsize (GaloisField.card 3 f hf.ne_zero) e

/-- The non-Fermat portion of the prime-field family in Thompson's list.
The explicit exclusion concerns only the numerical field parameter. -/
theorem OrderMinimalException.false_of_binary_nonFermat_prime_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (ell : ℕ) [Fact ell.Prime]
    (hlarge : 3 < ell) (hfive : 5 ∣ ell ^ 2 + 1)
    (hnot : ¬ ∃ n : ℕ, ell - 1 = 2 ^ n)
    (e : (G ⧸ solubleRadical G) ≃* Q (GaloisField ell 1)) : False := by
  have hp : ell.Prime := Fact.out
  rcases small_parameter_or_seventeen_le ell hp hlarge hfive with h7 | h13 | hbound
  · subst ell
    exact h.false_of_binary_pslTwo7_quotient_complete classification
      (e.trans (primeFieldEquiv 7))
  · subst ell
    exact h.false_of_binary_pslTwo13_quotient_complete classification
      (e.trans (primeFieldEquiv 13))
  · have hcard : Nat.card (GaloisField ell 1) = ell := by
      simpa only [pow_one] using GaloisField.card ell 1 (by decide)
    have hodd : Odd (Nat.card (GaloisField ell 1)) := by
      rw [hcard]
      exact hp.odd_of_ne_two (by omega)
    exact h.false_of_binary_odd_pslTwo_not_two_power_quotient classification
      (GaloisField ell 1) hodd (by simpa only [hcard] using hbound)
      (by simpa only [hcard] using hnot) e

end Kourovka2135
