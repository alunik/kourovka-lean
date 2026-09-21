import Kourovka2135.OuterWord

/-!
# A conjugacy-class certificate for single values of every outer word

A single commutator relation within one conjugacy class can be transported by
simultaneous conjugation to every member of the class. This supplies the exact
recursive property needed by `OuterWord.subset_values_of_commutator_closed`.
No generation of the ambient group is asserted.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

variable {G : Type u} [Group G]

/-- One commutator with both inputs and its output in a single conjugacy class
makes every element of that class a commutator of two class members. -/
theorem conjugatesOf_commutator_surjective {c a b t : G}
    (ha : a ∈ conjugatesOf c) (hb : b ∈ conjugatesOf c)
    (ht : t ∈ conjugatesOf c) (hab : a⁻¹ * b⁻¹ * a * b = t) :
    ∀ x ∈ conjugatesOf c,
      ∃ u ∈ conjugatesOf c, ∃ v ∈ conjugatesOf c,
        u⁻¹ * v⁻¹ * u * v = x := by
  intro x hx
  have htx : IsConj t x := (ht : IsConj c t).symm.trans hx
  obtain ⟨g, hg⟩ := isConj_iff.mp htx
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hfa : f a ∈ conjugatesOf c := by
    exact (ha : IsConj c a).trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hfb : f b ∈ conjugatesOf c := by
    exact (hb : IsConj c b).trans (isConj_iff.mpr ⟨g, rfl⟩)
  refine ⟨f a, hfa, f b, hfb, ?_⟩
  calc
    (f a)⁻¹ * (f b)⁻¹ * f a * f b = f (a⁻¹ * b⁻¹ * a * b) := by
      simp only [map_mul, map_inv]
    _ = f t := congrArg f hab
    _ = x := hg

/-- Such a class is contained in the single-value set of every outer word. -/
theorem conjugatesOf_subset_values {c a b t : G}
    (ha : a ∈ conjugatesOf c) (hb : b ∈ conjugatesOf c)
    (ht : t ∈ conjugatesOf c) (hab : a⁻¹ * b⁻¹ * a * b = t)
    (w : OuterWord) : conjugatesOf c ⊆ w.values G :=
  OuterWord.subset_values_of_commutator_closed _
    (conjugatesOf_commutator_surjective ha hb ht hab) w

/-- Version with an explicitly specified conjugacy-class subset. -/
theorem conjugacyClass_subset_values (B : Set G)
    (hB : ∃ c : G, B = conjugatesOf c) {a b t : G}
    (ha : a ∈ B) (hb : b ∈ B) (ht : t ∈ B)
    (hab : a⁻¹ * b⁻¹ * a * b = t) (w : OuterWord) : B ⊆ w.values G := by
  obtain ⟨c, rfl⟩ := hB
  exact conjugatesOf_subset_values ha hb ht hab w

/-- A fixed relation `[a,a^s] = a^t`, using right conjugation, certifies the
whole conjugacy class as single values of every outer commutator word. -/
theorem conjugatesOf_subset_values_of_certificate (a s t : G)
    (h : a⁻¹ * (s⁻¹ * a * s)⁻¹ * a * (s⁻¹ * a * s) = t⁻¹ * a * t)
    (w : OuterWord) : conjugatesOf a ⊆ w.values G := by
  have hs : s⁻¹ * a * s ∈ conjugatesOf a := by
    exact isConj_iff.mpr ⟨s⁻¹, by simp only [inv_inv]⟩
  have ht : t⁻¹ * a * t ∈ conjugatesOf a := by
    exact isConj_iff.mpr ⟨t⁻¹, by simp only [inv_inv]⟩
  exact conjugatesOf_subset_values (IsConj.refl a) hs ht h w

theorem mem_values_of_conjugate_commutator_certificate (a s t : G)
    (h : a⁻¹ * (s⁻¹ * a * s)⁻¹ * a * (s⁻¹ * a * s) = t⁻¹ * a * t)
    (w : OuterWord) : a ∈ w.values G :=
  conjugatesOf_subset_values_of_certificate a s t h w (IsConj.refl a)

end Kourovka2135
