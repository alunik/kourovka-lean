import Kourovka2135.OddPSLTwoSplitDihedral
import Kourovka2135.Vendor.CFSG.ElementaryAbelian

/-! Centralizers of actual split elements in PSL2.

The checked projective action identifies the fixed set of a nonidentity
split element with the two coordinate points. Its centralizer preserves
that pair, so the existing actual diagonal/Weyl decomposition applies.
No new CFSG proof slice or classification import is needed: the imported
`OddPSLTwoSplitDihedral` already records the Apache-2.0 provenance of its
two concrete Weyl identities from the pinned Dickson matrix file.

The elementary-abelian consequences below concern subgroups containing a
specified split involution. Conjugacy of an arbitrary involution to this
form is a separate obligation, not an implicit input.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoSplitCentralizer

open OddPSLTwoProjectiveChart OddPSLTwoTorusMovingRank
open OddPSLTwoSplitDihedral
open scoped IsMulCommutative

variable (F : Type*) [Field F]

theorem eq_of_chart_action_eq {g h : Q F}
    (he : ∀ x : Option F, g • x = h • x) : g = h := by
  apply (eq_of_smul_eq_smul (α := Point F))
  intro x
  obtain ⟨y, rfl⟩ := point_surjective F x
  rw [← point_smul, ← point_smul, he y]

theorem torus_eq_iff_square (r s : Fˣ) :
    projectiveTorusHom F r = projectiveTorusHom F s ↔
      (r : F) ^ 2 = (s : F) ^ 2 := by
  constructor
  · intro h
    have he := congrArg (fun g : Q F => g • (some (1 : F) : Option F)) h
    simpa only [projectiveTorusHom_apply, tor_smul_some, mul_one,
      Option.some.injEq] using he
  · intro h
    apply eq_of_chart_action_eq F
    intro x
    cases x with
    | none => simp only [projectiveTorusHom_apply, tor_smul_none]
    | some x => simp only [projectiveTorusHom_apply, tor_smul_some, h]

theorem torus_eq_one_iff (r : Fˣ) :
    projectiveTorusHom F r = 1 ↔ (r : F) ^ 2 = 1 := by
  simpa only [map_one, Units.val_one, one_pow] using torus_eq_iff_square F r 1

theorem torus_fixed_iff (r : Fˣ) (hr : (r : F) ^ 2 ≠ 1) (x : Option F) :
    projectiveTorusHom F r • x = x ↔ x = none ∨ x = some 0 := by
  cases x with
  | none => simp only [projectiveTorusHom_apply, tor_smul_none, true_or]
  | some x =>
    simp only [projectiveTorusHom_apply, tor_smul_some, Option.some.injEq,
      Option.some_ne_none, false_or]
    constructor
    · intro h
      have hp : ((r : F) ^ 2 - 1) * x = 0 := by rw [sub_mul, one_mul, h, sub_self]
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hr)
    · rintro rfl
      exact mul_zero _

theorem mem_splitDihedral_of_commute (r : Fˣ) (hr : (r : F) ^ 2 ≠ 1)
    (g : Q F) (hg : Commute g (projectiveTorusHom F r)) :
    g ∈ subgroup F := by
  have hfixed (x : Option F) (hx : projectiveTorusHom F r • x = x) :
      projectiveTorusHom F r • (g • x) = g • x := by
    calc
      _ = (projectiveTorusHom F r * g) • x := (mul_smul _ _ _).symm
      _ = (g * projectiveTorusHom F r) • x := congrArg (fun a : Q F => a • x) hg.eq.symm
      _ = g • (projectiveTorusHom F r • x) := mul_smul _ _ _
      _ = g • x := congrArg (fun y : Option F => g • y) hx
  have hnone := (torus_fixed_iff F r hr (g • none)).mp
    (hfixed none (tor_smul_none F r))
  have hzero := (torus_fixed_iff F r hr (g • some 0)).mp
    (hfixed (some 0) (by simp only [projectiveTorusHom_apply, tor_smul_some, mul_zero]))
  apply (mem_subgroup_iff F g).mpr
  rcases hnone with hn | hn <;> rcases hzero with hz | hz
  · have he : (none : Option F) = some 0 := MulAction.injective g (hn.trans hz.symm)
    cases he
  · exact Or.inl ⟨hn, hz⟩
  · exact Or.inr ⟨hn, hz⟩
  · have he : (none : Option F) = some 0 := MulAction.injective g (hn.trans hz.symm)
    cases he

theorem torus_commute (r s : Fˣ) :
    Commute (projectiveTorusHom F r) (projectiveTorusHom F s) :=
  (Commute.all r s).map (projectiveTorusHom F)

theorem reflection_conj_torus (r s : Fˣ) :
    (weyl F * projectiveTorusHom F s) * projectiveTorusHom F r *
      (weyl F * projectiveTorusHom F s)⁻¹ = (projectiveTorusHom F r)⁻¹ := by
  calc
    _ = weyl F * (projectiveTorusHom F s * projectiveTorusHom F r *
        (projectiveTorusHom F s)⁻¹) * (weyl F)⁻¹ := by group
    _ = weyl F * projectiveTorusHom F r * (weyl F)⁻¹ := by
      rw [(torus_commute F s r).eq, mul_inv_cancel_right]
    _ = _ := weyl_conj F r

/-- The actual projective centralizer consists of torus elements, with the
Weyl coset present exactly when the split element squares to one. -/
theorem commute_torus_iff (r : Fˣ) (hr : (r : F) ^ 2 ≠ 1) (g : Q F) :
    Commute g (projectiveTorusHom F r) ↔
      (∃ s : Fˣ, g = projectiveTorusHom F s) ∨
      ((projectiveTorusHom F r) ^ 2 = 1 ∧
        ∃ s : Fˣ, g = weyl F * projectiveTorusHom F s) := by
  constructor
  · intro hg
    obtain ⟨s, hs | hs⟩ := exists_torus_or_weyl_torus F
      ⟨g, mem_splitDihedral_of_commute F r hr g hg⟩
    · exact Or.inl ⟨s, hs⟩
    · change g = weyl F * projectiveTorusHom F s at hs
      refine Or.inr ⟨?_, s, hs⟩
      have he : projectiveTorusHom F r = (projectiveTorusHom F r)⁻¹ := by
        calc
          _ = g * projectiveTorusHom F r * g⁻¹ := by rw [hg.eq, mul_inv_cancel_right]
          _ = _ := by rw [hs]; exact reflection_conj_torus F r s
      simpa only [pow_two] using eq_inv_iff_mul_eq_one.mp he
  · rintro (⟨s, rfl⟩ | ⟨hsq, s, rfl⟩)
    · exact torus_commute F s r
    · have he : (projectiveTorusHom F r)⁻¹ = projectiveTorusHom F r := by
        exact (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hsq)).symm
      change (weyl F * projectiveTorusHom F s) * projectiveTorusHom F r =
        projectiveTorusHom F r * (weyl F * projectiveTorusHom F s)
      have h := reflection_conj_torus F r s
      rw [he] at h
      exact mul_inv_eq_iff_eq_mul.mp h

theorem centralizer_torus_eq_range (r : Fˣ)
    (hr : (projectiveTorusHom F r) ^ 2 ≠ 1) :
    Subgroup.centralizer ({projectiveTorusHom F r} : Set (Q F)) =
      (projectiveTorusHom F).range := by
  have hr' : (r : F) ^ 2 ≠ 1 := by
    intro he
    apply hr
    rw [(torus_eq_one_iff F r).mpr he, one_pow]
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  change Commute g (projectiveTorusHom F r) ↔ ∃ s, projectiveTorusHom F s = g
  rw [commute_torus_iff F r hr']
  constructor
  · rintro (⟨s, hs⟩ | ⟨he, _⟩)
    · exact ⟨s, hs.symm⟩
    · exact (hr he).elim
  · rintro ⟨s, rfl⟩
    exact Or.inl ⟨s, rfl⟩

theorem centralizer_split_involution (r : Fˣ)
    (hr : (r : F) ^ 2 ≠ 1) (hsq : (projectiveTorusHom F r) ^ 2 = 1) :
    Subgroup.centralizer ({projectiveTorusHom F r} : Set (Q F)) = subgroup F := by
  apply le_antisymm
  · intro g hg
    exact mem_splitDihedral_of_commute F r hr g
      (Subgroup.mem_centralizer_singleton_iff.mp hg)
  · intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply (commute_torus_iff F r hr g).mpr
    obtain ⟨s, hs | hs⟩ := exists_torus_or_weyl_torus F ⟨g, hg⟩
    · exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨hsq, s, hs⟩

/-- The projective torus has at most two elements that square to one,
when a specified unit supplies the square root of minus one. -/
theorem torus_sq_eq_one_iff (i r : Fˣ) (hi : (i : F) ^ 2 = -1) :
    (projectiveTorusHom F r) ^ 2 = 1 ↔
      projectiveTorusHom F r = 1 ∨ projectiveTorusHom F r = projectiveTorusHom F i := by
  rw [← map_pow, torus_eq_one_iff]
  change ((r : F) ^ 2) ^ 2 = 1 ↔ _
  rw [sq_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((torus_eq_one_iff F r).mpr h)
    · exact Or.inr ((torus_eq_iff_square F r i).mpr (h.trans hi.symm))
  · rintro (h | h)
    · exact Or.inl ((torus_eq_one_iff F r).mp h)
    · exact Or.inr (((torus_eq_iff_square F r i).mp h).trans hi)

theorem weyl_mul_torus_not_mem_range (r : Fˣ) :
    weyl F * projectiveTorusHom F r ∉ (projectiveTorusHom F).range := by
  rintro ⟨s, hs⟩
  have he := congrArg (fun g : Q F => g • (none : Option F)) hs
  simp only [mul_smul, projectiveTorusHom_apply, tor_smul_none, weyl_smul_none] at he
  cases he

theorem torus_sq_eq_one_of_commute_reflection (r s : Fˣ)
    (h : Commute (projectiveTorusHom F r) (weyl F * projectiveTorusHom F s)) :
    (projectiveTorusHom F r) ^ 2 = 1 := by
  have he : projectiveTorusHom F r = (projectiveTorusHom F r)⁻¹ := by
    calc
      _ = (weyl F * projectiveTorusHom F s) * projectiveTorusHom F r *
          (weyl F * projectiveTorusHom F s)⁻¹ := by
        rw [h.eq.symm, mul_inv_cancel_right]
      _ = _ := reflection_conj_torus F r s
  simpa only [pow_two] using eq_inv_iff_mul_eq_one.mp he

/-- The centralizer of a split involution and a commuting element outside
the torus is contained in the four explicitly named elements. -/
theorem centralizer_pair_four (i : Fˣ) (hi : (i : F) ^ 2 = -1)
    (hine : (i : F) ^ 2 ≠ 1) (a : Q F)
    (ha : Commute a (projectiveTorusHom F i))
    (haout : a ∉ (projectiveTorusHom F).range) (g : Q F)
    (hgi : Commute g (projectiveTorusHom F i)) (hga : Commute g a) :
    g = 1 ∨ g = projectiveTorusHom F i ∨ g = a ∨ g = a * projectiveTorusHom F i := by
  obtain ⟨s, hs | hs⟩ := exists_torus_or_weyl_torus F
    ⟨a, mem_splitDihedral_of_commute F i hine a ha⟩
  · exact (haout ⟨s, hs.symm⟩).elim
  change a = weyl F * projectiveTorusHom F s at hs
  obtain ⟨r, hr | hr⟩ := exists_torus_or_weyl_torus F
    ⟨g, mem_splitDihedral_of_commute F i hine g hgi⟩
  · change g = projectiveTorusHom F r at hr
    have hp := torus_sq_eq_one_of_commute_reflection F r s (by simpa only [hr, hs] using hga)
    rcases (torus_sq_eq_one_iff F i r hi).mp hp with h | h
    · exact Or.inl (hr.trans h)
    · exact Or.inr (Or.inl (hr.trans h))
  · change g = weyl F * projectiveTorusHom F r at hr
    have he : a⁻¹ * g = projectiveTorusHom F (s⁻¹ * r) := by
      rw [hs, hr, map_mul, map_inv]
      group
    have hc : Commute (a⁻¹ * g) a := by
      change (a⁻¹ * g) * a = a * (a⁻¹ * g)
      calc
        _ = a⁻¹ * (g * a) := by group
        _ = a⁻¹ * (a * g) := congrArg (fun z : Q F => a⁻¹ * z) hga.eq
        _ = _ := by group
    have hp := torus_sq_eq_one_of_commute_reflection F (s⁻¹ * r) s
      (by rw [he, hs] at hc; exact hc)
    rcases (torus_sq_eq_one_iff F i (s⁻¹ * r) hi).mp hp with h | h
    · exact Or.inr (Or.inr (Or.inl (by
        have hh : a⁻¹ * g = 1 := he.trans h
        exact (inv_mul_eq_one.mp hh).symm)))
    · exact Or.inr (Or.inr (Or.inr (inv_mul_eq_iff_eq_mul.mp (he.trans h))))

/-- A commutative subgroup containing the split involution and an element
outside the torus is its own actual projective centralizer. -/
theorem centralizer_eq_self_of_split_involution (E : Subgroup (Q F))
    [IsMulCommutative E] (i : Fˣ) (hi : (i : F) ^ 2 = -1)
    (hine : (i : F) ^ 2 ≠ 1) (hiE : projectiveTorusHom F i ∈ E)
    (a : Q F) (haE : a ∈ E) (haout : a ∉ (projectiveTorusHom F).range) :
    Subgroup.centralizer (E : Set (Q F)) = E := by
  have hcomm {x y : Q F} (hx : x ∈ E) (hy : y ∈ E) : Commute x y :=
    setLike_mul_comm hx hy
  apply le_antisymm
  · intro g hg
    have hgi : Commute g (projectiveTorusHom F i) :=
      ((Subgroup.mem_centralizer_iff.mp hg) _ hiE).symm
    have hga : Commute g a := ((Subgroup.mem_centralizer_iff.mp hg) a haE).symm
    rcases centralizer_pair_four F i hi hine a (hcomm haE hiE) haout g hgi hga with
      rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hiE
    · exact haE
    · exact E.mul_mem haE hiE
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact (hcomm hx hg).eq

theorem elementary_two_four_cover (E : Subgroup (Q F)) [IsElementaryAbelian 2 E]
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1)
    (hiE : projectiveTorusHom F i ∈ E) :
    ∃ a ∈ E, ∀ g ∈ E,
      g = 1 ∨ g = projectiveTorusHom F i ∨ g = a ∨ g = a * projectiveTorusHom F i := by
  classical
  by_cases hle : E ≤ (projectiveTorusHom F).range
  · refine ⟨1, E.one_mem, ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := hle hg
    have hp : (projectiveTorusHom F r) ^ 2 = 1 := by
      rw [hr]
      exact elemPow_eq_one_of_isElementaryAbelian g hg
    rcases (torus_sq_eq_one_iff F i r hi).mp hp with h | h
    · exact Or.inl (hr.symm.trans h)
    · exact Or.inr (Or.inl (hr.symm.trans h))
  · change ¬ (E : Set (Q F)) ⊆ ((projectiveTorusHom F).range : Set (Q F)) at hle
    obtain ⟨a, haE, haout⟩ := Set.not_subset.mp hle
    refine ⟨a, haE, ?_⟩
    intro g hg
    exact centralizer_pair_four F i hi hine a (setLike_mul_comm haE hiE) haout g
      (setLike_mul_comm hg hiE) (setLike_mul_comm hg haE)

/-- Once a split involution is present, an elementary abelian two-subgroup
has at most four elements. Finiteness of the ambient field is unnecessary. -/
theorem card_elementary_two_le_four (E : Subgroup (Q F)) [IsElementaryAbelian 2 E]
    (i : Fˣ) (hi : (i : F) ^ 2 = -1) (hine : (i : F) ^ 2 ≠ 1)
    (hiE : projectiveTorusHom F i ∈ E) : Nat.card E ≤ 4 := by
  classical
  obtain ⟨a, haE, hcover⟩ := elementary_two_four_cover F E i hi hine hiE
  let f : Fin 4 → E := ![1, ⟨projectiveTorusHom F i, hiE⟩,
    ⟨a, haE⟩, ⟨a * projectiveTorusHom F i, E.mul_mem haE hiE⟩]
  have hf : Function.Surjective f := by
    intro g
    rcases hcover g g.property with h | h | h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
    · exact ⟨2, Subtype.ext h.symm⟩
    · exact ⟨3, Subtype.ext h.symm⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

end Kourovka2135.OddPSLTwoSplitCentralizer
