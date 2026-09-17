import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-!+A local rank-one proof of the Bruhat multiplication inclusion. All assumptions
are explicit matrix identities or elementary subgroup factorizations. This is
not an instantiation for the Wilson group and does not assert its simplicity.
-/

namespace ReeStructural

variable {G : Type*} [Group G]

open scoped Pointwise

/-- The central algebraic step. A factorization of `B` at a simple root and the
rank-one identity turn either orientation of the root into a two-cell bound. -/
theorem rankOne_middle_step
    (B R : Subgroup G) (s w : G)
    (factor : ∀ b ∈ B, ∃ u ∈ R, ∃ c : G,
      b = u * c ∧ s⁻¹ * c * s ∈ B)
    (rankOne : ∀ u ∈ R, u ≠ 1 → ∃ u' ∈ R, ∃ b' ∈ B,
      s⁻¹ * u * s = u' * s⁻¹ * b')
    (orientation :
      (∀ u ∈ R, w * u * w⁻¹ ∈ B) ∨
      (∀ u ∈ R, (w * s) * u * (w * s)⁻¹ ∈ B))
    (b : G) (hb : b ∈ B) :
    ∃ v : G, (v = w * s ∨ v = w) ∧
      ∃ l ∈ B, ∃ r ∈ B, w * b * s = l * v * r := by
  obtain ⟨u, hu, c, rfl, hc⟩ := factor b hb
  rcases orientation with hpos | hneg
  · refine ⟨w * s, Or.inl rfl, w * u * w⁻¹, hpos u hu,
      s⁻¹ * c * s, hc, ?_⟩
    group
  · by_cases hu1 : u = 1
    · subst u
      refine ⟨w * s, Or.inl rfl, 1, B.one_mem, s⁻¹ * c * s, hc, ?_⟩
      group
    · obtain ⟨u', hu', b', hb', heq⟩ := rankOne u hu hu1
      refine ⟨w, Or.inr rfl, (w * s) * u' * (w * s)⁻¹, hneg u' hu',
        b' * (s⁻¹ * c * s), B.mul_mem hb' hc, ?_⟩
      calc
        w * (u * c) * s = w * s * (s⁻¹ * u * s) * (s⁻¹ * c * s) := by group
        _ = w * s * (u' * s⁻¹ * b') * (s⁻¹ * c * s) := by rw [heq]
        _ = (w * s * u' * (w * s)⁻¹) * w * (b' * (s⁻¹ * c * s)) := by group

/-- Right multiplication of a Weyl cell by a simple cell stays in the two
prescribed cells. Inversion converts this to the left multiplication axiom in
`TauCeti.TitsSystem`. -/
theorem rankOne_doubleCoset_mul_subset
    (B R : Subgroup G) (s w : G)
    (factor : ∀ b ∈ B, ∃ u ∈ R, ∃ c : G,
      b = u * c ∧ s⁻¹ * c * s ∈ B)
    (rankOne : ∀ u ∈ R, u ≠ 1 → ∃ u' ∈ R, ∃ b' ∈ B,
      s⁻¹ * u * s = u' * s⁻¹ * b')
    (orientation :
      (∀ u ∈ R, w * u * w⁻¹ ∈ B) ∨
      (∀ u ∈ R, (w * s) * u * (w * s)⁻¹ ∈ B)) :
    DoubleCoset.doubleCoset w B B * DoubleCoset.doubleCoset s B B ⊆
      DoubleCoset.doubleCoset (w * s) B B ∪ DoubleCoset.doubleCoset w B B := by
  rintro g ⟨a, ha, c, hc, rfl⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ha
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hc
  obtain ⟨v, hv, l, hl, r, hr, hproduct⟩ :=
    rankOne_middle_step B R s w factor rankOne orientation (a₂ * c₁) (B.mul_mem ha₂ hc₁)
  have hg : a₁ * w * a₂ * (c₁ * s * c₂) ∈ DoubleCoset.doubleCoset v B B := by
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨a₁ * l, B.mul_mem ha₁ hl, r * c₂, B.mul_mem hr hc₂, ?_⟩
    calc
      a₁ * w * a₂ * (c₁ * s * c₂) = a₁ * (w * (a₂ * c₁) * s) * c₂ := by group
      _ = a₁ * (l * v * r) * c₂ := by rw [hproduct]
      _ = (a₁ * l) * v * (r * c₂) := by group
  rcases hv with rfl | rfl
  · exact Or.inl hg
  · exact Or.inr hg

/-- Inversion reverses a double-coset representative. -/
theorem inv_mem_doubleCoset {B : Subgroup G} {g w : G}
    (hg : g ∈ DoubleCoset.doubleCoset w B B) :
    g⁻¹ ∈ DoubleCoset.doubleCoset w⁻¹ B B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨b⁻¹, B.inv_mem hb, a⁻¹, B.inv_mem ha, by group⟩

/-- Adapter from the right rank-one law to the left law used by TauCeti. -/
theorem left_doubleCoset_mul_subset_of_right
    (B : Subgroup G) (s w : G)
    (rightStep :
      DoubleCoset.doubleCoset w⁻¹ B B * DoubleCoset.doubleCoset s⁻¹ B B ⊆
        DoubleCoset.doubleCoset (w⁻¹ * s⁻¹) B B ∪
          DoubleCoset.doubleCoset w⁻¹ B B) :
    DoubleCoset.doubleCoset s B B * DoubleCoset.doubleCoset w B B ⊆
      DoubleCoset.doubleCoset (s * w) B B ∪ DoubleCoset.doubleCoset w B B := by
  rintro g ⟨a, ha, b, hb, rfl⟩
  have hinv : (a * b)⁻¹ ∈
      DoubleCoset.doubleCoset w⁻¹ B B * DoubleCoset.doubleCoset s⁻¹ B B := by
    exact ⟨b⁻¹, inv_mem_doubleCoset hb, a⁻¹, inv_mem_doubleCoset ha, by group⟩
  rcases rightStep hinv with hnew | hold
  · exact Or.inl (by simpa only [mul_inv_rev, inv_inv] using inv_mem_doubleCoset hnew)
  · exact Or.inr (by simpa only [inv_inv] using inv_mem_doubleCoset hold)

#print axioms rankOne_middle_step
#print axioms rankOne_doubleCoset_mul_subset
#print axioms left_doubleCoset_mul_subset_of_right

end ReeStructural
