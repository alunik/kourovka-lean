import Kourovka.Problems.P21_44.Proof.WordEncoding
import Kourovka.Problems.P21_44.Proof.SectionCounting
import Kourovka.Problems.P21_44.Proof.GrowthRate
import Kourovka.Problems.P21_44.Proof.RecurrentSections.ExponentialGrowth

/-!
# From word shortening to subexponential growth

Partition a word ball according to whether an alternating representative has
few sign changes. Sparse words have a small explicit encoding. All remaining
elements have a shorter total section length and are counted by their actual
section balls. Every encoding is injective; no realizability of arbitrary
section tuples is assumed.
-/

namespace Kourovka.P21_44

open RecurrentSections
open scoped BigOperators

section
variable {G R : Type*} [Group G] [DecidableEq G] [Fintype R]

theorem wordGrowth_recurrence
    (V : WordGeometry G) (A B : G)
    (root : G → R) (sections : G → Fin 5 → G)
    (hinj : Function.Injective fun g => (root g, sections g))
    (hrootcard : Fintype.card R = 60)
    (hcover : ∀ n : ℕ, ∀ g ∈ V.ball n,
      ∃ w : Word, Alternating w ∧ w.length ≤ n ∧ evalWord A B w = g)
    (hshort : ∀ w : Word, Alternating w →
      (∑ i, (V.length (sections (evalWord A B w) i) : ℝ)) +
        (variation w : ℝ) / 10 ≤ (w.length : ℝ) + 1) :
    EnvelopeRecurrence (fun n => (V.volume n : ℝ)) Real.binEntropy := by
  classical
  intro δ hδ hδhalf s hs C hC henv n
  let low : Finset G := (V.ball n).filter fun g =>
    ∃ w : SmallWord n δ, evalWord A B w.val = g
  have hlow : (low.card : ℝ) ≤
      8 * ((n : ℝ) + 1) * Real.exp (Real.binEntropy δ * n) := by
    let chooseWord : {g : G // g ∈ low} → SmallWord n δ := fun g =>
      Classical.choose (Finset.mem_filter.1 g.property).2
    have hchoose (g : {g : G // g ∈ low}) :
        evalWord A B (chooseWord g).val = g.val :=
      Classical.choose_spec (Finset.mem_filter.1 g.property).2
    have hi : Function.Injective chooseWord := by
      intro g h heq
      apply Subtype.ext
      rw [← hchoose g, ← hchoose h, heq]
    have hc : low.card ≤ Fintype.card (SmallWord n δ) := by
      simpa using Fintype.card_le_of_injective chooseWord hi
    calc
      (low.card : ℝ) ≤ Fintype.card (SmallWord n δ) := by exact_mod_cast hc
      _ ≤ _ := by simpa only [mul_comm (n : ℝ)] using card_smallWords_le n hδ hδhalf
  let high : Finset G := V.ball n \ low
  let t : ℝ := (1 - δ / 10) * n + 1
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have : 0 ≤ (1 - δ / 10) := by linarith
    positivity
  have htn : t ≤ (n : ℝ) + 1 := by
    dsimp [t]
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hlength : ∀ g ∈ high, ∑ i, (V.length (sections g i) : ℝ) ≤ t := by
    intro g hg
    obtain ⟨hgn, hglow⟩ := Finset.mem_sdiff.1 hg
    obtain ⟨w, hw, hlen, heval⟩ := hcover n g hgn
    have hv : δ * n < (variation w : ℝ) := by
      by_contra h
      have hvar : (variation w : ℝ) ≤ δ * n := le_of_not_gt h
      apply hglow
      exact Finset.mem_filter.2 ⟨hgn, ⟨⟨w, hw, hlen, hvar⟩, heval⟩⟩
    have h := hshort w hw
    rw [heval] at h
    have hn : (w.length : ℝ) ≤ n := by exact_mod_cast hlen
    dsimp [t]
    linarith
  have hhigh := section_count_of_envelope V root sections hinj high n t C s
    ht0 htn hC hs hlength henv
  rw [hrootcard] at hhigh
  have hpartition : high.card + low.card = (V.ball n).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hp : (V.volume n : ℝ) = (high.card : ℝ) + low.card := by
    exact_mod_cast hpartition.symm
  change (V.volume n : ℝ) ≤ _
  rw [hp]
  dsimp [t] at hhigh
  linarith

theorem subexponential_of_word_shortening
    (V : WordGeometry G) (A B : G)
    (root : G → R) (sections : G → Fin 5 → G)
    (hinj : Function.Injective fun g => (root g, sections g))
    (hrootcard : Fintype.card R = 60)
    (hcover : ∀ n : ℕ, ∀ g ∈ V.ball n,
      ∃ w : Word, Alternating w ∧ w.length ≤ n ∧ evalWord A B w = g)
    (hshort : ∀ w : Word, Alternating w →
      (∑ i, (V.length (sections (evalWord A B w) i) : ℝ)) +
        (variation w : ℝ) / 10 ≤ (w.length : ℝ) + 1) :
    SubexponentialGrowth V.volume := by
  apply tendsto_log_div_zero_of_binary_entropy_recurrence
  · intro n
    exact_mod_cast V.volume_pos n
  · refine ⟨Real.log (V.volume 1 : ℝ) + 1, ?_, 1, by norm_num, ?_⟩
    · linarith [V.logVolume_nonneg 1]
    · intro n
      simpa only [one_mul] using V.volume_le_exp n
  · exact wordGrowth_recurrence V A B root sections hinj hrootcard hcover hshort

end
end Kourovka.P21_44
