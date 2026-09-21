import Kourovka2135.LeafSection

/-!
# Full sections of outer commutator word trees

A section meets every root-to-leaf path exactly once: it either stops at the
root or consists of sections of both branches. Inserting `[u,t]` at each
selected subtree `u` bounds `[w(G),t(G)]` by the join of the inserted verbal
subgroups, as in the outer-word section lemma.

Every inserted word contains `t` as a constituent. Refinement of `w` requires
a local compatibility condition at the selected nodes; arbitrary internal
root insertions do not automatically refine the original tree.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135.OuterWord

variable {G : Type u} [Group G]

/-- A full section of a word tree, retaining the positions of selected subtrees. -/
inductive Section : OuterWord → Type where
  | root (w : OuterWord) : Section w
  | branch {l r : OuterWord} : Section l → Section r → Section (bracket l r)

/-- Insert `[u,t]` at one selected subtree `u`, ranging over a full section.
Coincident output tree shapes are deduplicated by the finite set. -/
def sectionInsertions {w : OuterWord} (s : Section w) (t : OuterWord) : Finset OuterWord :=
  match s with
  | .root w => {bracket w t}
  | @Section.branch l r sl sr =>
      (sectionInsertions sl t).image (fun v => bracket v r) ∪
      (sectionInsertions sr t).image (fun v => bracket l v)

/-- The join of the verbal subgroups obtained from section insertions. -/
def sectionSubgroup {w : OuterWord} (s : Section w) (t : OuterWord)
    (G : Type u) [Group G] : Subgroup G :=
  ⨆ v ∈ sectionInsertions s t, v.verbalSubgroup G

instance sectionSubgroup_normal {w : OuterWord} (s : Section w) (t : OuterWord) :
    (sectionSubgroup s t G).Normal := by
  unfold sectionSubgroup
  infer_instance

/-- The full-section outer-word commutator inequality. -/
theorem commutator_verbalSubgroup_le_section {w : OuterWord}
    (s : Section w) (t : OuterWord) :
    ⁅w.verbalSubgroup G, t.verbalSubgroup G⁆ ≤ sectionSubgroup s t G := by
  induction s with
  | root w =>
      rw [← verbalSubgroup_bracket]
      exact le_iSup_of_le (bracket w t)
        (le_iSup_of_le (by simp [sectionInsertions]) le_rfl)
  | @branch l r sl sr ihl ihr =>
      rw [verbalSubgroup_bracket]
      apply (commutator_commutator_le_sup _ _ _).trans
      apply sup_le
      · apply (Subgroup.commutator_mono ihl le_rfl).trans
        apply commutator_iSup_le
        intro v
        apply commutator_iSup_le
        intro hv
        rw [← verbalSubgroup_bracket]
        apply le_iSup_of_le (bracket v r)
        apply le_iSup_of_le
          (show bracket v r ∈ sectionInsertions (.branch sl sr) t from by
            simp only [sectionInsertions, Finset.mem_union, Finset.mem_image]
            exact Or.inl ⟨v, hv, rfl⟩)
        exact le_rfl
      · apply (Subgroup.commutator_mono le_rfl ihr).trans
        apply commutator_iSup_right_le
        intro v
        apply commutator_iSup_right_le
        intro hv
        rw [← verbalSubgroup_bracket]
        apply le_iSup_of_le (bracket l v)
        apply le_iSup_of_le
          (show bracket l v ∈ sectionInsertions (.branch sl sr) t from by
            simp only [sectionInsertions, Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨v, hv, rfl⟩)
        exact le_rfl

/-- The inserted word is a constituent of every resulting tree. -/
theorem constituent_of_sectionInsertion {w v t : OuterWord} (s : Section w)
    (h : v ∈ sectionInsertions s t) : Constituent t v := by
  induction s generalizing v with
  | root w =>
      simp only [sectionInsertions, Finset.mem_singleton] at h
      subst v
      exact .right (.refl t)
  | @branch l r sl sr ihl ihr =>
      simp only [sectionInsertions, Finset.mem_union, Finset.mem_image] at h
      rcases h with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact .left (ihl ha)
      · exact .right (ihr hb)

/-- Every section-inserted value belongs to the inserted word's verbal subgroup. -/
theorem sectionInsertion_value_mem_inserted_verbalSubgroup
    {w v t : OuterWord} (s : Section w) (h : v ∈ sectionInsertions s t)
    {x : G} (hx : x ∈ v.values G) : x ∈ t.verbalSubgroup G :=
  verbalSubgroup_le_of_constituent (constituent_of_sectionInsertion s h)
    (v.mem_verbalSubgroup_of_mem_values hx)

/-- The local condition needed for insertions to refine the original word. -/
def Section.RefinementCompatible {w : OuterWord} (s : Section w) (t : OuterWord) : Prop :=
  match s with
  | .root w => Refines (bracket w t) w
  | .branch sl sr => sl.RefinementCompatible t ∧ sr.RefinementCompatible t

/-- Local refinement at selected nodes propagates through the entire tree. -/
theorem sectionInsertion_refines {w v t : OuterWord} (s : Section w)
    (hcompatible : s.RefinementCompatible t) (h : v ∈ sectionInsertions s t) :
    Refines v w := by
  induction s generalizing v with
  | root w =>
      simp only [sectionInsertions, Finset.mem_singleton] at h
      subst v
      exact hcompatible
  | @branch l r sl sr ihl ihr =>
      simp only [sectionInsertions, Finset.mem_union, Finset.mem_image] at h
      rcases h with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact .bracket (ihl hcompatible.1 ha) (.refl r)
      · exact .bracket (.refl l) (ihr hcompatible.2 hb)

/-- Under the local compatibility condition, each auxiliary value is both a single
original-word value and an element of the inserted word's verbal subgroup. -/
theorem sectionInsertion_value_mem {w v t : OuterWord} (s : Section w)
    (hcompatible : s.RefinementCompatible t) (h : v ∈ sectionInsertions s t)
    {x : G} (hx : x ∈ v.values G) : x ∈ w.values G ∧ x ∈ t.verbalSubgroup G :=
  ⟨(sectionInsertion_refines s hcompatible h).values_subset hx,
    sectionInsertion_value_mem_inserted_verbalSubgroup s h hx⟩

/-- The full section consisting of all leaves. -/
def Section.leaves : (w : OuterWord) → Section w
  | leaf => .root leaf
  | bracket l r => .branch (Section.leaves l) (Section.leaves r)

/-- The original leaf insertion construction is a special case of full sections. -/
theorem sectionInsertions_leaves (w t : OuterWord) :
    sectionInsertions (Section.leaves w) t = leafInsertions w t := by
  induction w with
  | leaf => rfl
  | bracket l r ihl ihr => simp only [Section.leaves, sectionInsertions, leafInsertions, ihl, ihr]

/-- All-leaf sections satisfy the refinement condition for every inserted word. -/
theorem Section.leaves_refinementCompatible (w t : OuterWord) :
    (Section.leaves w).RefinementCompatible t := by
  induction w with
  | leaf => exact .leaf _
  | bracket l r ihl ihr => exact ⟨ihl, ihr⟩

end Kourovka2135.OuterWord
