import Kourovka.Problems.P21_44.Proof.RecurrentSections.WordGeometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card

/-!
# Counting bounded section tuples

A faithful root-and-sections encoding bounds a finite set by its admissible
length tuples and the corresponding products of word balls. All bounds concern
the actual word geometry supplied to the theorem.
-/

namespace Kourovka.P21_44

open RecurrentSections
open scoped BigOperators

/-- A finite family of elements with a bounded sum of five section lengths
inherits an exponential bound from the five word-ball envelopes. -/
theorem section_count_of_envelope
    {G R : Type*} [Group G] [DecidableEq G] [Fintype R]
    (V : WordGeometry G) (root : G → R) (sections : G → Fin 5 → G)
    (hinj : Function.Injective fun g => (root g, sections g))
    (B : Finset G) (n : ℕ) (t C s : ℝ)
    (_ht0 : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) (hC : 0 < C) (hs : 0 < s)
    (hlen : ∀ g ∈ B, ∑ i, (V.length (sections g i) : ℝ) ≤ t)
    (henv : ∀ k : ℕ, (V.volume k : ℝ) ≤ C * Real.exp (s * k)) :
    (B.card : ℝ) ≤ (Fintype.card R : ℝ) * ((n : ℝ) + 2) ^ 5 * C ^ 5 *
      Real.exp (s * t) := by
  classical
  let Tuple := Fin 5 → Fin (n + 2)
  let GoodTuple := {k : Tuple // (∑ i, ((k i).val : ℝ)) ≤ t}
  let Fiber (k : Tuple) := R × (∀ i : Fin 5, {g : G // g ∈ V.ball (k i).val})
  let Encoding := Σ k : GoodTuple, Fiber k.val
  have hlenBound (g : G) (hg : g ∈ B) (i : Fin 5) :
      V.length (sections g i) < n + 2 := by
    have hsingle : (V.length (sections g i) : ℝ) ≤
        ∑ j, (V.length (sections g j) : ℝ) :=
      Finset.single_le_sum (f := fun j : Fin 5 => (V.length (sections g j) : ℝ))
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hle : (V.length (sections g i) : ℝ) ≤ (n : ℝ) + 1 :=
      hsingle.trans ((hlen g hg).trans htn)
    have hnat : V.length (sections g i) ≤ n + 1 := by exact_mod_cast hle
    omega
  let code (g : {g : G // g ∈ B}) : Encoding :=
    ⟨⟨fun i => ⟨V.length (sections g.val i), hlenBound g.val g.property i⟩,
      hlen g.val g.property⟩,
      root g.val, fun i => ⟨sections g.val i, (V.mem_ball_iff_length_le _ _).mpr le_rfl⟩⟩
  let forget : Encoding → R × (Fin 5 → G) :=
    fun z => (z.2.1, fun i => (z.2.2 i).val)
  have hcode : Function.Injective code := by
    intro g h heq
    apply Subtype.ext
    exact hinj (congrArg forget heq)
  have hcard : B.card ≤ Fintype.card Encoding := by
    simpa using Fintype.card_le_of_injective code hcode
  have hfiber (k : GoodTuple) :
      (Fintype.card (Fiber k.val) : ℝ) ≤
        (Fintype.card R : ℝ) * C ^ 5 * Real.exp (s * t) := by
    have hprod : (∏ i : Fin 5, (V.volume (k.val i).val : ℝ)) ≤
        C ^ 5 * Real.exp (s * t) := by
      calc
        (∏ i : Fin 5, (V.volume (k.val i).val : ℝ))
            ≤ ∏ i : Fin 5, C * Real.exp (s * ((k.val i).val : ℝ)) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _; exact henv _
        _ = C ^ 5 * Real.exp (s * ∑ i : Fin 5, ((k.val i).val : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, ← Real.exp_sum, Finset.mul_sum]
        _ ≤ C ^ 5 * Real.exp (s * t) := by
          gcongr
          exact k.property
    have hc : (Fintype.card (Fiber k.val) : ℝ) =
        (Fintype.card R : ℝ) * ∏ i : Fin 5, (V.volume (k.val i).val : ℝ) := by
      simp [Fiber, Fintype.card_pi, WordGeometry.volume]
    rw [hc]
    exact (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)).trans_eq (by ring)
  have htuples : Fintype.card GoodTuple ≤ (n + 2) ^ 5 := by
    calc
      Fintype.card GoodTuple ≤ Fintype.card Tuple := Fintype.card_subtype_le _
      _ = (n + 2) ^ 5 := by simp [Tuple]
  calc
    (B.card : ℝ) ≤ (Fintype.card Encoding : ℝ) := by exact_mod_cast hcard
    _ = ∑ k : GoodTuple, (Fintype.card (Fiber k.val) : ℝ) := by
      simp [Encoding, Fintype.card_sigma]
    _ ≤ ∑ _k : GoodTuple, (Fintype.card R : ℝ) * C ^ 5 * Real.exp (s * t) :=
      Finset.sum_le_sum fun k _ => hfiber k
    _ = (Fintype.card GoodTuple : ℝ) *
        ((Fintype.card R : ℝ) * C ^ 5 * Real.exp (s * t)) := by simp
    _ ≤ ((n : ℝ) + 2) ^ 5 *
        ((Fintype.card R : ℝ) * C ^ 5 * Real.exp (s * t)) := by
      gcongr
      exact_mod_cast htuples
    _ = (Fintype.card R : ℝ) * ((n : ℝ) + 2) ^ 5 * C ^ 5 *
        Real.exp (s * t) := by ring

end Kourovka.P21_44
