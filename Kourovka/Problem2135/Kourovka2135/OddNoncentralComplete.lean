import Kourovka2135.EvenPSLTwoOddNormalizerBranch
import Kourovka2135.OddPSLTwoOddNormalizerBranch
import Kourovka2135.PSLThreeThreeOddNormalizerBranch
import Kourovka2135.SuzukiOddNormalizerBranch
import Kourovka2135.ClassifiedMinimalException

/-! Every odd-prime least exception has central soluble radical, using the
actual normalizer obstruction in each of Thompson's five families. The
odd-prime central-radical branch remains outside this theorem. -/

set_option autoImplicit false
universe u
noncomputable section
namespace Kourovka2135

/-- The complete odd-prime noncentral-radical exclusion. No family premise
is retained: the actual quotient model is supplied by Thompson. -/
theorem OrderMinimalException.false_of_odd_noncentral
    (classification : MinimalSimpleClassification.{u})
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G) : False := by
  have hmodel := h.radical_quotient_has_classified_model classification hp hnoncentral
  rcases hmodel with heven | hthree | hprime | hsuzuki | hthreeThree
  · obtain ⟨f, hf, ⟨e⟩⟩ := heven
    exact h.false_of_odd_noncentral_even_pslTwo_quotient hp hodd hnoncentral
      (GaloisField 2 f) f (GaloisField.card 2 f hf.ne_zero) hf.two_le e
  · obtain ⟨f, hf, hf2, ⟨e⟩⟩ := hthree
    have hcard : Nat.card (GaloisField 3 f) = 3 ^ f := GaloisField.card 3 f hf.ne_zero
    have hFodd : Odd (Nat.card (GaloisField 3 f)) := by
      rw [hcard]
      exact (by decide : Odd (3 : ℕ)).pow
    have hlarge : 27 ≤ Nat.card (GaloisField 3 f) := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ f by have := hf.two_le; omega)
    exact h.false_of_odd_noncentral_odd_pslTwo_card_ge hp hodd hnoncentral
      (GaloisField 3 f) hFodd hlarge e
  · obtain ⟨ell, hell, hlarge, hfive, he⟩ := hprime
    let : Fact ell.Prime := ⟨hell⟩
    obtain ⟨e⟩ := he
    have hcard : Nat.card (GaloisField ell 1) = ell := by
      simpa only [pow_one] using GaloisField.card ell 1 (by decide)
    have hseven : 7 ≤ ell := by
      by_contra! hlt
      interval_cases ell <;> norm_num at *
    exact h.false_of_odd_noncentral_prime_pslTwo_quotient hp hodd hnoncentral
      (GaloisField ell 1) (by simpa only [hcard] using hell)
      (by simpa only [hcard] using hseven) e
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hsuzuki
    exact h.false_of_odd_noncentral_suzuki_quotient hp hodd hnoncentral m hm e
  · obtain ⟨e⟩ := hthreeThree
    exact h.false_of_odd_noncentral_pslThreeThree_quotient hp hodd hnoncentral e

end Kourovka2135
