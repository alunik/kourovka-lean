import Kourovka2135.WordHeight
import Kourovka2135.WordSections
import Mathlib.Data.Finset.Prod

/-!
# Same-height proper extensions and the derived-word section bound

A section insertion need not itself refine the original word or preserve its
height. At a suitable cut, its verbal subgroup is instead contained in that of
a separate proper refinement with the required height bound.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135.OuterWord

variable {G : Type u} [Group G]

/-- Stop after the given number of edges, or earlier on reaching a leaf. -/
def Section.atDepth : (w : OuterWord) → ℕ → Section w
  | w, 0 => .root w
  | leaf, _ + 1 => .root leaf
  | bracket l r, d + 1 => .branch (Section.atDepth l d) (Section.atDepth r d)

@[simp]
theorem Section.atDepth_zero (w : OuterWord) : Section.atDepth w 0 = .root w := by
  cases w <;> rfl

@[simp]
theorem Section.atDepth_leaf (d : ℕ) : Section.atDepth leaf d = .root leaf := by
  cases d <;> rfl

@[simp]
theorem Section.atDepth_bracket (l r : OuterWord) (d : ℕ) :
    Section.atDepth (bracket l r) (d + 1) =
      .branch (Section.atDepth l d) (Section.atDepth r d) := rfl

/-- Early leaves are dominated by completing them to the inserted derived word. -/
theorem sectionInsertion_leaf_dominated (i d : ℕ) (hi : 1 ≤ i) {π : OuterWord}
    (hπ : π ∈ sectionInsertions (Section.atDepth leaf d) (derivedWord i)) :
    ∃ v : OuterWord, Refines v leaf ∧ v ≠ leaf ∧ v.height ≤ i + d + 1 ∧
      π.verbalSubgroup G ≤ v.verbalSubgroup G := by
  simp only [Section.atDepth_leaf, sectionInsertions, Finset.mem_singleton] at hπ
  subst π
  refine ⟨derivedWord i, .leaf _, ?_, ?_, verbalSubgroup_bracket_le_right _ _⟩
  · intro heq
    have := congrArg height heq
    simp only [height_derivedWord, height_leaf] at this
    omega
  · rw [height_derivedWord]
    omega

/-- A section insertion at a cut with no aligned full subtree at the next level
is dominated by a proper refinement satisfying the ambient height bound. -/
theorem sectionInsertion_dominated (w : OuterWord) (i d : ℕ) (hi : 1 ≤ i)
    (hh : w.height ≤ i + d + 1)
    (hcut : ¬ FullAt w (i + d + 1) (i + 1)) {π : OuterWord}
    (hπ : π ∈ sectionInsertions (Section.atDepth w d) (derivedWord i)) :
    ∃ v : OuterWord, Refines v w ∧ v ≠ w ∧ v.height ≤ i + d + 1 ∧
      π.verbalSubgroup G ≤ v.verbalSubgroup G := by
  induction d generalizing w π with
  | zero =>
      cases w with
      | leaf => exact sectionInsertion_leaf_dominated i 0 hi hπ
      | bracket l r =>
          simp only [Section.atDepth_zero, sectionInsertions, Finset.mem_singleton] at hπ
          subst π
          have hmax : max l.height r.height ≤ i := Nat.le_of_succ_le_succ hh
          have hl : l.height ≤ i := (Nat.le_max_left _ _).trans hmax
          have hr : r.height ≤ i := (Nat.le_max_right _ _).trans hmax
          by_cases hrfull : r = derivedWord i
          · subst r
            have hln : l ≠ derivedWord i := by
              intro hlfull
              apply hcut
              subst l
              exact FullAt.here (i + 1)
            refine ⟨bracket (derivedWord i) (derivedWord i),
              .bracket (derivedWord_refines_of_height_le l i hl) (.refl _), ?_, ?_, ?_⟩
            · intro heq
              exact hln (bracket.inj heq).1.symm
            · simp only [height_bracket, height_derivedWord, Nat.max_self, Nat.add_zero]
              exact le_rfl
            · simpa only [verbalSubgroup_bracket] using
                (Subgroup.commutator_mono
                  (verbalSubgroup_bracket_le_right (G := G) l (derivedWord i))
                  (le_refl ((derivedWord i).verbalSubgroup G)))
          · refine ⟨bracket l (derivedWord i),
              .bracket (.refl _) (derivedWord_refines_of_height_le r i hr), ?_, ?_, ?_⟩
            · intro heq
              exact hrfull (bracket.inj heq).2.symm
            · simp only [height_bracket, height_derivedWord]
              omega
            · simpa only [verbalSubgroup_bracket] using
                (Subgroup.commutator_mono
                  (verbalSubgroup_bracket_le_left (G := G) l r)
                  (le_refl ((derivedWord i).verbalSubgroup G)))
  | succ d ih =>
      cases w with
      | leaf => exact sectionInsertion_leaf_dominated i (d + 1) hi hπ
      | bracket l r =>
          have hl : l.height ≤ i + d + 1 := by
            simp only [height_bracket] at hh
            omega
          have hr : r.height ≤ i + d + 1 := by
            simp only [height_bracket] at hh
            omega
          have hcutl : ¬ FullAt l (i + d + 1) (i + 1) := by
            intro h
            apply hcut
            simpa only [Nat.add_assoc] using (FullAt.left (r := r) h)
          have hcutr : ¬ FullAt r (i + d + 1) (i + 1) := by
            intro h
            apply hcut
            simpa only [Nat.add_assoc] using (FullAt.right (l := l) h)
          simp only [Section.atDepth_bracket, sectionInsertions,
            Finset.mem_union, Finset.mem_image] at hπ
          rcases hπ with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
          · obtain ⟨v, hv, hvne, hvheight, hvle⟩ := ih l hl hcutl ha
            refine ⟨bracket v r, .bracket hv (.refl _), ?_, ?_, ?_⟩
            · intro heq
              exact hvne (bracket.inj heq).1
            · simp only [height_bracket]
              omega
            · simpa only [verbalSubgroup_bracket] using
                (Subgroup.commutator_mono hvle (le_refl (r.verbalSubgroup G)))
          · obtain ⟨v, hv, hvne, hvheight, hvle⟩ := ih r hr hcutr hb
            refine ⟨bracket l v, .bracket (.refl _) hv, ?_, ?_, ?_⟩
            · intro heq
              exact hvne (bracket.inj heq).2
            · simp only [height_bracket]
              omega
            · simpa only [verbalSubgroup_bracket] using
                (Subgroup.commutator_mono (le_refl (l.verbalSubgroup G)) hvle)

/-- All ordered binary words with height at most the specified bound. -/
def boundedWords : ℕ → Finset OuterWord
  | 0 => {leaf}
  | h + 1 => {leaf} ∪
      ((boundedWords h).product (boundedWords h)).image (fun lr => bracket lr.1 lr.2)

@[simp]
theorem mem_boundedWords (w : OuterWord) (h : ℕ) :
    w ∈ boundedWords h ↔ w.height ≤ h := by
  induction h generalizing w with
  | zero =>
      cases w <;> simp [boundedWords, height]
  | succ h ih =>
      cases w with
      | leaf => simp [boundedWords]
      | bracket l r =>
          simp [boundedWords, Finset.mem_product, ih, height]

/-- The finite family of all proper refinements preserving the original height. -/
noncomputable def properExtensions (w : OuterWord) : Finset OuterWord := by
  classical
  exact (boundedWords w.height).filter (fun v => ProperSameHeightExtension v w)

@[simp]
theorem mem_properExtensions (v w : OuterWord) :
    v ∈ properExtensions w ↔ ProperSameHeightExtension v w := by
  classical
  simp only [properExtensions, Finset.mem_filter, mem_boundedWords]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1.le, h⟩⟩

/-- The join of the verbal subgroups of all proper same-height extensions. -/
def properExtensionSubgroup (w : OuterWord) (G : Type u) [Group G] : Subgroup G :=
  ⨆ v ∈ properExtensions w, v.verbalSubgroup G

instance properExtensionSubgroup_normal (w : OuterWord) :
    (properExtensionSubgroup w G).Normal := by
  unfold properExtensionSubgroup
  infer_instance

theorem properExtensionSubgroup_le (w : OuterWord) :
    properExtensionSubgroup w G ≤ w.verbalSubgroup G := by
  refine iSup_le fun v => iSup_le fun hv => ?_
  exact ((mem_properExtensions v w).mp hv).1.verbalSubgroup_le

/-- Every non-derived bracket admits a specified derived-word constituent in
one branch whose commutator with the original verbal subgroup is bounded by
the join of all proper same-height extensions. -/
theorem exists_derived_extension_bound (α β : OuterWord)
    (hne : bracket α β ≠ derivedWord (bracket α β).height) :
    ∃ i, 1 ≤ i ∧ i < (bracket α β).height ∧
      (Constituent (derivedWord i) α ∨ Constituent (derivedWord i) β) ∧
      ⁅(bracket α β).verbalSubgroup G, (derivedWord i).verbalSubgroup G⁆ ≤
        properExtensionSubgroup (bracket α β) G := by
  let w := bracket α β
  have hw : 0 < w.height := by simp [w]
  obtain ⟨i, hi, hih, hfull, _, hcut⟩ := exists_max_fullAt_lt w hw hne
  let d := w.height - (i + 1)
  have hd : w.height = i + d + 1 := by dsimp [d]; omega
  have hcut' : ¬ FullAt w (i + d + 1) (i + 1) := by rwa [← hd]
  have hsection : sectionSubgroup (Section.atDepth w d) (derivedWord i) G ≤
      properExtensionSubgroup w G := by
    refine iSup_le fun π => iSup_le fun hπ => ?_
    obtain ⟨v, href, hvne, hvheight, hle⟩ :=
      sectionInsertion_dominated (G := G) w i d hi hd.le hcut' hπ
    have hheight : v.height = w.height :=
      le_antisymm (hvheight.trans hd.ge) href.height_le
    have hv : v ∈ properExtensions w :=
      (mem_properExtensions v w).mpr ⟨href, hheight, hvne⟩
    exact hle.trans (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
  exact ⟨i, hi, hih, hfull.constituent_child hih,
    (commutator_verbalSubgroup_le_section (Section.atDepth w d) (derivedWord i)).trans hsection⟩

end Kourovka2135.OuterWord
