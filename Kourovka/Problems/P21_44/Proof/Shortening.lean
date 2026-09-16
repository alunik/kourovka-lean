import Kourovka.Problems.P21_44.Proof.SectionWords

/-! # Disjoint five-letter shortenings

The finite certificate checks the sixteen signed shortening blocks. The global
bound uses disjoint occurrences, so a cancellation is never counted twice.
-/

namespace Kourovka.P21_44

/-- Each of the sixteen five-letter blocks saves at least one section letter.
This is a finite kernel computation of the explicit word-routing algorithm. -/
theorem five_letter_shortening (f sx sy sz : Bool) :
    (∑ i : Alphabet,
      (normalize (rawSections [(f,sx),(!f,true),(f,sy),(!f,false),(f,sz)] i)).length) ≤ 4 := by
  cases f <;> cases sx <;> cases sy <;> cases sz <;> decide

lemma alternating_drop (w : Word) (h : Alternating w) (n : ℕ) :
    Alternating (w.drop n) := by
  induction n generalizing w with
  | zero => exact h
  | succ n ih =>
    cases w with
    | nil => trivial
    | cons l w => exact ih w (alternating_tail _ h)

lemma alternating_take (w : Word) (h : Alternating w) (n : ℕ) :
    Alternating (w.take n) := by
  induction n generalizing w with
  | zero => trivial
  | succ n ih =>
    cases w with
    | nil => trivial
    | cons l w =>
      cases n with
      | zero => trivial
      | succ n =>
        cases w with
        | nil => trivial
        | cons k w => exact ⟨h.1, ih _ h.2⟩

/-- Any alternating prefix selected by `isPattern` is one of the sixteen
explicit blocks above. -/
theorem pattern_shortening (w : Word) (h : Alternating w) (hp : isPattern w = true) :
    ∑ i : Alphabet, (normalize (rawSections (w.take 5) i)).length ≤ 4 := by
  rcases w with _ | ⟨x,w⟩ <;> try contradiction
  rcases w with _ | ⟨y,w⟩ <;> try contradiction
  rcases w with _ | ⟨z,w⟩ <;> try contradiction
  rcases w with _ | ⟨t,w⟩ <;> try contradiction
  rcases w with _ | ⟨u,w⟩ <;> try contradiction
  rcases x with ⟨fx,sx⟩
  rcases y with ⟨fy,sy⟩
  rcases z with ⟨fz,sz⟩
  rcases t with ⟨ft,st⟩
  rcases u with ⟨fu,su⟩
  simp only [Alternating] at h
  simp only [isPattern, Bool.and_eq_true, Bool.not_eq_true'] at hp
  have hy : fy = !fx := Bool.eq_not_iff.mpr h.1.symm
  have hz : fz = fx := by
    have hz := Bool.eq_not_iff.mpr h.2.1.symm
    simpa only [hy, Bool.not_not] using hz
  have ht : ft = !fx := by
    have ht := Bool.eq_not_iff.mpr h.2.2.1.symm
    simpa only [hz] using ht
  have hu : fu = fx := by
    have hu := Bool.eq_not_iff.mpr h.2.2.2.1.symm
    simpa only [ht, Bool.not_not] using hu
  obtain ⟨rfl,rfl⟩ := hp
  subst fy; subst fz; subst ft; subst fu
  exact five_letter_shortening fx sx sz su

lemma pattern_length (w : Word) (hp : isPattern w = true) : 5 ≤ w.length := by
  rcases w with _ | ⟨x,w⟩ <;> try contradiction
  rcases w with _ | ⟨y,w⟩ <;> try contradiction
  rcases w with _ | ⟨z,w⟩ <;> try contradiction
  rcases w with _ | ⟨t,w⟩ <;> try contradiction
  rcases w with _ | ⟨u,w⟩ <;> try contradiction
  simp

lemma sum_routed_append_length (f g : Alphabet → Word) (σ : A5) :
    (∑ i : Alphabet, (f i ++ g (σ.val⁻¹ i)).length) =
      (∑ i : Alphabet, (f i).length) + ∑ i : Alphabet, (g i).length := by
  simp only [List.length_append, Finset.sum_add_distrib]
  rw [Equiv.sum_comp σ.val⁻¹ (fun i => (g i).length)]

/-- Every selected disjoint pattern saves one letter in the total section
budget. All five witnesses evaluate in the actual tree group. -/
theorem exists_short_sections (w : Word) (h : Alternating w) :
    ∃ f : Alphabet → Word,
      (∀ i, evalWord a b (f i) = evalWord a b (rawSections w i)) ∧
      (∑ i : Alphabet, (f i).length) + disjointPatterns w ≤ w.length := by
  induction n : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    cases w with
    | nil => exact ⟨fun _ => [], fun _ => rfl, by simp [disjointPatterns]⟩
    | cons l w =>
      by_cases hp : isPattern (l :: w) = true
      · let u := (l :: w).take 5
        let v := w.drop 4
        have hv : Alternating v := alternating_drop w (alternating_tail _ h) 4
        obtain ⟨g, hge, hgl⟩ := ih v.length (by dsimp [v]; simp at n; simp; omega) v hv rfl
        let f : Alphabet → Word := fun i =>
          normalize (rawSections u i) ++ g ((rootWord u).val⁻¹ i)
        refine ⟨f, ?_, ?_⟩
        · intro i
          have heq : u ++ v = l :: w := by
            dsimp [u, v]
            simp
          dsimp [f]
          rw [evalWord_append, evalWord_normalize a b a_cube b_cube, hge]
          rw [← evalWord_append]
          exact congrArg (evalWord a b) ((rawSections_append u v i).symm.trans
            (congrArg (fun w => rawSections w i) heq))
        · rw [← n]
          have hshort := pattern_shortening (l :: w) h hp
          have hlen := pattern_length (l :: w) hp
          have hlenv : v.length = (l :: w).length - 5 := by simp [v]
          change (∑ i, (normalize (rawSections u i) ++ g ((rootWord u).val⁻¹ i)).length) +
            disjointPatterns (l :: w) ≤ (l :: w).length
          rw [sum_routed_append_length, disjointPatterns, ite_eq_left hp]
          change (∑ i, (normalize (rawSections u i)).length) +
            (∑ i, (g i).length) + (1 + disjointPatterns v) ≤ (l :: w).length
          change (∑ i, (normalize (rawSections u i)).length) ≤ 4 at hshort
          omega
      · have ht : Alternating w := alternating_tail _ h
        obtain ⟨g,hge,hgl⟩ := ih w.length (by simp at n; omega) w ht rfl
        refine ⟨fun i => letterSection l i ++ g ((rootLetter l).val⁻¹ i), ?_, ?_⟩
        · intro i
          rw [evalWord_append, hge]
          exact (evalWord_append a b _ _).symm
        · rw [← n]
          rw [sum_routed_append_length, sum_letterSection_length,
            disjointPatterns, ite_eq_right hp]
          simp only [List.length_cons]
          omega

/-- Sign variation forces uniform shortening of the actual five sections. -/
theorem section_shortening (w : Word) (h : Alternating w) :
    ∃ f : Alphabet → Word,
      (∀ i, evalWord a b (f i) = treeSection (evalWord a b w) i) ∧
      ((∑ i : Alphabet, (f i).length : ℕ) : ℝ) + (variation w : ℝ) / 10 ≤
        (w.length : ℝ) + 1 := by
  obtain ⟨f,hf,hlen⟩ := exists_short_sections w h
  refine ⟨f, fun i => (hf i).trans (treeSection_evalWord w i).symm, ?_⟩
  have hv := variation_le_ten_disjoint w
  have hlen' : ((∑ i : Alphabet, (f i).length : ℕ) : ℝ) + disjointPatterns w ≤ w.length := by
    exact_mod_cast hlen
  have hv' : (variation w : ℝ) ≤ 10 * (disjointPatterns w : ℝ) + 6 := by
    exact_mod_cast hv
  linarith

end Kourovka.P21_44
