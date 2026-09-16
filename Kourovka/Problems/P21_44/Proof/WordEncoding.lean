import Kourovka.Problems.P21_44.Proof.WordEvaluation
import Kourovka.Problems.P21_44.Proof.BinomialCounting

/-!
# Encoding alternating signed words by their sign changes

An alternating word is determined by its length, its first generator family,
the initial sign in each of the two alternating positions, and the positions
where signs at distance two differ.
-/

namespace Kourovka.P21_44

private def succEmbedding : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

/-- Positions at which the sign differs from the sign two letters later. -/
def changePositions : Word → Finset ℕ
  | x :: y :: z :: w =>
      let tail := (changePositions (y :: z :: w)).map succEmbedding
      if x.2 = z.2 then tail else insert 0 tail
  | _ => ∅

@[simp] theorem zero_mem_changePositions (x y z : Letter) (w : Word) :
    0 ∈ changePositions (x :: y :: z :: w) ↔ x.2 ≠ z.2 := by
  by_cases h : x.2 = z.2 <;> simp [changePositions, h, succEmbedding, Finset.mem_map]

@[simp] theorem succ_mem_changePositions (x y z : Letter) (w : Word) (i : ℕ) :
    i + 1 ∈ changePositions (x :: y :: z :: w) ↔
      i ∈ changePositions (y :: z :: w) := by
  by_cases h : x.2 = z.2 <;> simp [changePositions, h, succEmbedding]

/-- All encoded positions are inside the word. -/
theorem mem_changePositions_lt_length (w : Word) {i : ℕ}
    (hi : i ∈ changePositions w) : i < w.length := by
  induction w generalizing i with
  | nil => simp [changePositions] at hi
  | cons x w ih =>
    cases w with
    | nil => simp [changePositions] at hi
    | cons y w =>
      cases w with
      | nil => simp [changePositions] at hi
      | cons z w =>
        cases i with
        | zero => simp
        | succ i =>
          have h := ih ((succ_mem_changePositions x y z w i).1 hi)
          simp only [List.length_cons] at h ⊢
          omega

/-- The number of encoded positions is exactly the variation statistic. -/
theorem card_changePositions (w : Word) : (changePositions w).card = variation w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases w with
    | nil => rfl
    | cons y w =>
      cases w with
      | nil => rfl
      | cons z w =>
        have hzero : 0 ∉ (changePositions (y :: z :: w)).map succEmbedding := by
          simp [succEmbedding, Finset.mem_map]
        by_cases h : x.2 = z.2
        · simp only [changePositions, h, ↓reduceIte, Finset.card_map, ih,
            variation, changes, Nat.zero_add]
        · simp only [changePositions, h, ↓reduceIte,
            Finset.card_insert_of_notMem hzero, Finset.card_map, ih,
            variation, changes, Nat.add_comm]

/-- The family of the first letter and the signs of the first two letters. -/
def wordInitialBits : Word → Bool × Bool × Bool
  | [] => (false, false, false)
  | [x] => (x.1, x.2, false)
  | x :: y :: _ => (x.1, x.2, y.2)

private theorem bool_eq_of_ne {x y z : Bool} (hy : x ≠ y) (hz : x ≠ z) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

private theorem bool_eq_of_same_change {x y z : Bool}
    (h : (x ≠ y) ↔ (x ≠ z)) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Decoding is unique, including words of lengths zero, one, and two. -/
theorem alternating_word_eq_of_code {w v : Word}
    (hw : Alternating w) (hv : Alternating v) (hlen : w.length = v.length)
    (hbits : wordInitialBits w = wordInitialBits v)
    (hpositions : changePositions w = changePositions v) : w = v := by
  induction w generalizing v with
  | nil => simpa using hlen.symm
  | cons x w ih =>
    cases v with
    | nil => simp at hlen
    | cons x' v =>
      cases w with
      | nil =>
        cases v with
        | nil =>
          have hx : x = x' := by
            apply Prod.ext
            · simpa only [wordInitialBits] using
                congrArg (fun b : Bool × Bool × Bool => b.1) hbits
            · simpa only [wordInitialBits] using
                congrArg (fun b : Bool × Bool × Bool => b.2.1) hbits
          simp [hx]
        | cons y' v => simp at hlen
      | cons y w =>
        cases v with
        | nil => simp at hlen
        | cons y' v =>
          have hx : x = x' := by
            apply Prod.ext
            · simpa only [wordInitialBits] using
                congrArg (fun b : Bool × Bool × Bool => b.1) hbits
            · simpa only [wordInitialBits] using
                congrArg (fun b : Bool × Bool × Bool => b.2.1) hbits
          subst x'
          have hy : y = y' := by
            apply Prod.ext
            · exact bool_eq_of_ne hw.1 hv.1
            · simpa only [wordInitialBits] using
                congrArg (fun b : Bool × Bool × Bool => b.2.2) hbits
          subst y'
          cases w with
          | nil =>
            cases v with
            | nil => rfl
            | cons z' v => simp at hlen
          | cons z w =>
            cases v with
            | nil => simp at hlen
            | cons z' v =>
              have hsign : z.2 = z'.2 := by
                apply bool_eq_of_same_change (x := x.2)
                simpa only [zero_mem_changePositions] using
                  (show (0 ∈ changePositions (x :: y :: z :: w)) ↔
                    (0 ∈ changePositions (x :: y :: z' :: v)) by rw [hpositions])
              have htailpositions : changePositions (y :: z :: w) =
                  changePositions (y :: z' :: v) := by
                ext i
                simpa only [succ_mem_changePositions] using
                  (show (i + 1 ∈ changePositions (x :: y :: z :: w)) ↔
                    (i + 1 ∈ changePositions (x :: y :: z' :: v)) by rw [hpositions])
              have htail := ih hw.2 hv.2 (by simpa using hlen)
                (by simp only [wordInitialBits, hsign]) htailpositions
              exact congrArg (List.cons x) htail

private def changePositionEmbedding (w : Word) {n : ℕ} (hlen : w.length ≤ n) :
    {i : ℕ // i ∈ changePositions w} ↪ Fin n where
  toFun i := ⟨i.1, lt_of_lt_of_le (mem_changePositions_lt_length w i.2) hlen⟩
  inj' := by
    intro i j h
    exact Subtype.ext (congrArg Fin.val h)

/-- Change positions regarded as elements of a common ambient `Fin n`. -/
def boundedChangePositions (w : Word) {n : ℕ} (hlen : w.length ≤ n) : Finset (Fin n) :=
  (changePositions w).attach.map (changePositionEmbedding w hlen)

@[simp] theorem card_boundedChangePositions (w : Word) {n : ℕ} (hlen : w.length ≤ n) :
    (boundedChangePositions w hlen).card = variation w := by
  simp only [boundedChangePositions, Finset.card_map, Finset.card_attach, card_changePositions]

@[simp] theorem map_boundedChangePositions (w : Word) {n : ℕ} (hlen : w.length ≤ n) :
    (boundedChangePositions w hlen).map Fin.valEmbedding = changePositions w := by
  unfold boundedChangePositions
  rw [Finset.map_map]
  exact Finset.attach_map_val

private noncomputable def threeBitsEquiv : (Bool × Bool × Bool) ≃ Fin 8 :=
  Fintype.equivFinOfCardEq (by decide)

/-- Alternating words of length at most `n` and variation at most `δ * n`. -/
def SmallWord (n : ℕ) (δ : ℝ) :=
  {w : Word // Alternating w ∧ w.length ≤ n ∧ (variation w : ℝ) ≤ δ * n}

/-- The finite code consists of length, three initial bits, and change positions. -/
noncomputable def smallWordCode {n : ℕ} {δ : ℝ} (w : SmallWord n δ) :
    Fin (n + 1) × Fin 8 × {s : Finset (Fin n) // (s.card : ℝ) ≤ δ * n} :=
  (⟨w.1.length, Nat.lt_succ_of_le w.2.2.1⟩,
    threeBitsEquiv (wordInitialBits w.1),
    ⟨boundedChangePositions w.1 w.2.2.1, by
      rw [card_boundedChangePositions]
      exact w.2.2.2⟩)

theorem smallWordCode_injective (n : ℕ) (δ : ℝ) :
    Function.Injective (@smallWordCode n δ) := by
  intro w v h
  apply Subtype.ext
  apply alternating_word_eq_of_code w.2.1 v.2.1
  · exact congrArg (fun c => c.1.val) h
  · exact threeBitsEquiv.injective (congrArg (fun c => c.2.1) h)
  · have hm := congrArg (fun c => c.2.2.val.map Fin.valEmbedding) h
    simpa only [smallWordCode, map_boundedChangePositions] using hm

noncomputable instance smallWordFintype (n : ℕ) (δ : ℝ) : Fintype (SmallWord n δ) :=
  Fintype.ofInjective smallWordCode (smallWordCode_injective n δ)

/-- The sparse-variation count for actual alternating signed words. -/
theorem card_smallWords_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (Fintype.card (SmallWord n δ) : ℝ) ≤
      8 * ((n : ℝ) + 1) * Real.exp ((n : ℝ) * Real.binEntropy δ) :=
  card_le_entropy_of_injective_encoding n hδ hδhalf
    smallWordCode (smallWordCode_injective n δ)

/-- Finite-set version, useful when choosing representatives of group elements. -/
theorem card_finset_smallWords_le (s : Finset Word) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hs : ∀ w ∈ s, Alternating w ∧ w.length ≤ n ∧ (variation w : ℝ) ≤ δ * n) :
    (s.card : ℝ) ≤ 8 * ((n : ℝ) + 1) *
      Real.exp ((n : ℝ) * Real.binEntropy δ) := by
  let code : s → SmallWord n δ := fun w => ⟨w.1, hs w.1 w.2⟩
  have hcode : Function.Injective code := by
    intro w v h
    exact Subtype.ext (congrArg (fun a : SmallWord n δ => a.1) h)
  have hc : s.card ≤ Fintype.card (SmallWord n δ) := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective code hcode
  exact (Nat.cast_le.2 hc).trans (card_smallWords_le n hδ hδhalf)

end Kourovka.P21_44
