import Kourovka2135.WordCalculus
import Mathlib.Data.Finset.Image

/-!
# The all-leaf case of the outer-word section lemma

For every leaf of w, replace that leaf by `[leaf,r]`. Then `[w(G),r(G)]`
lies in the join of the resulting verbal subgroups. This is exactly the
all-leaf instance of Detomi–Morigi–Shumyatsky, Lemma 2.7, used in the
soluble-case proof (On the rank of a verbal subgroup of a finite group,
DOI 10.1017/S1446788721000069).

The proof here uses mathlib's Hall–Witt/three-subgroups lemma in a quotient.
No published word theorem is assumed.
-/

set_option autoImplicit false

universe u v

namespace Kourovka2135

variable {G : Type u} [Group G]

/-- The three-subgroups lemma modulo a normal subgroup. -/
theorem commutator_commutator_le_of_rotate
    (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ N) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ N) :
    ⁅⁅A, B⁆, C⁆ ≤ N := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have quotient_eq (X Y Z : Subgroup G) (h : ⁅⁅X, Y⁆, Z⁆ ≤ N) :
      ⁅⁅X.map f, Y.map f⁆, Z.map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff]
    simpa only [f, QuotientGroup.ker_mk'] using h
  have h := Subgroup.commutator_commutator_eq_bot_of_rotate
    (quotient_eq B C A h₁) (quotient_eq C A B h₂)
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff] at h
  simpa only [f, QuotientGroup.ker_mk'] using h

theorem commutator_commutator_le_sup (A B C : Subgroup G)
    [A.Normal] [B.Normal] [C.Normal] :
    ⁅⁅A, B⁆, C⁆ ≤ ⁅⁅A, C⁆, B⁆ ⊔ ⁅A, ⁅B, C⁆⁆ := by
  apply commutator_commutator_le_of_rotate
  · rw [Subgroup.commutator_comm ⁅B, C⁆ A]
    exact le_sup_right
  · rw [Subgroup.commutator_comm C A]
    exact le_sup_left

/-- Bounds modulo a normal subgroup extend from a family to its join. -/
theorem commutator_iSup_le {ι : Sort v} (A : ι → Subgroup G)
    (B N : Subgroup G) [N.Normal] (h : ∀ i, ⁅A i, B⁆ ≤ N) :
    ⁅⨆ i, A i, B⁆ ≤ N := by
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
    Subgroup.map_commutator, Subgroup.map_iSup,
    Subgroup.commutator_eq_bot_iff_le_centralizer]
  apply iSup_le
  intro i
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
    ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact h i

theorem commutator_iSup_right_le {ι : Sort v} (A : Subgroup G)
    (B : ι → Subgroup G) (N : Subgroup G) [N.Normal]
    (h : ∀ i, ⁅A, B i⁆ ≤ N) : ⁅A, ⨆ i, B i⁆ ≤ N := by
  rw [Subgroup.commutator_comm]
  apply commutator_iSup_le
  intro i
  simpa only [Subgroup.commutator_comm] using h i

namespace OuterWord

/-- Replace exactly one leaf of w by `[leaf,r]`, ranging over all leaves.
Coincident tree shapes may be deduplicated: this does not change the join. -/
def leafInsertions : OuterWord → OuterWord → Finset OuterWord
  | leaf, r => {bracket leaf r}
  | bracket l s, r =>
      (leafInsertions l r).image (fun v => bracket v s) ∪
      (leafInsertions s r).image (fun v => bracket l v)

/-- The product, equivalently join, of the leaf-inserted verbal subgroups. -/
def leafSectionSubgroup (w r : OuterWord) (G : Type u) [Group G] : Subgroup G :=
  ⨆ v ∈ leafInsertions w r, v.verbalSubgroup G

instance leafSectionSubgroup_normal (w r : OuterWord) :
    (leafSectionSubgroup w r G).Normal := by
  unfold leafSectionSubgroup
  infer_instance

theorem commutator_verbalSubgroup_le_leafSection (w r : OuterWord) :
    ⁅w.verbalSubgroup G, r.verbalSubgroup G⁆ ≤ leafSectionSubgroup w r G := by
  induction w with
  | leaf =>
      rw [← verbalSubgroup_bracket]
      exact le_iSup_of_le (bracket leaf r) (le_iSup_of_le (by simp [leafInsertions]) le_rfl)
  | bracket l s ihl ihs =>
      rw [verbalSubgroup_bracket]
      apply (commutator_commutator_le_sup _ _ _).trans
      apply sup_le
      · apply (Subgroup.commutator_mono ihl le_rfl).trans
        apply commutator_iSup_le
        intro v
        apply commutator_iSup_le
        intro hv
        rw [← verbalSubgroup_bracket]
        apply le_iSup_of_le (bracket v s)
        apply le_iSup_of_le
          (show bracket v s ∈ leafInsertions (bracket l s) r from by
            simp only [leafInsertions, Finset.mem_union, Finset.mem_image]
            exact Or.inl ⟨v, hv, rfl⟩)
        exact le_rfl
      · apply (Subgroup.commutator_mono le_rfl ihs).trans
        apply commutator_iSup_right_le
        intro v
        apply commutator_iSup_right_le
        intro hv
        rw [← verbalSubgroup_bracket]
        apply le_iSup_of_le (bracket l v)
        apply le_iSup_of_le
          (show bracket l v ∈ leafInsertions (bracket l s) r from by
            simp only [leafInsertions, Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨v, hv, rfl⟩)
        exact le_rfl

theorem leafInsertion_refines {v w r : OuterWord} (h : v ∈ leafInsertions w r) :
    Refines v w := by
  induction w generalizing v with
  | leaf => exact .leaf _
  | bracket l s ihl ihs =>
      simp only [leafInsertions, Finset.mem_union, Finset.mem_image] at h
      rcases h with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact .bracket (ihl ha) (.refl s)
      · exact .bracket (.refl l) (ihs hb)

theorem constituent_of_leafInsertion {v w r : OuterWord} (h : v ∈ leafInsertions w r) :
    Constituent r v := by
  induction w generalizing v with
  | leaf =>
      simp only [leafInsertions, Finset.mem_singleton] at h
      subst v
      exact .right (.refl r)
  | bracket l s ihl ihs =>
      simp only [leafInsertions, Finset.mem_union, Finset.mem_image] at h
      rcases h with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact .left (ihl ha)
      · exact .right (ihs hb)

/-- The auxiliary values are simultaneously single w-values and elements of
the verbal subgroup r(G), as required by the Hall adjustment step. -/
theorem leafInsertion_value_mem {v w r : OuterWord} (h : v ∈ leafInsertions w r)
    {x : G} (hx : x ∈ v.values G) : x ∈ w.values G ∧ x ∈ r.verbalSubgroup G := by
  exact ⟨(leafInsertion_refines h).values_subset hx,
    verbalSubgroup_le_of_constituent (constituent_of_leafInsertion h)
      (v.mem_verbalSubgroup_of_mem_values hx)⟩

end OuterWord
end Kourovka2135
