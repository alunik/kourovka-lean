/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Kourovka2135.SolubleStructure

/-! Normal p-subgroups and proper supplements in finite soluble groups. -/

namespace Kourovka2135.Soluble

universe u

/-- A normal p-subgroup of the Frattini quotient is the image of a normal p-subgroup.
This lifting statement does not require the ambient group to be soluble. -/
theorem exists_normal_pSubgroup_lift_frattini
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Subgroup (G ⧸ frattini G)) [R.Normal] (hR : IsPGroup p R) :
    ∃ P : Subgroup G, P.Normal ∧ IsPGroup p P ∧
      P.map (QuotientGroup.mk' (frattini G)) = R := by
  classical
  let q : G →* G ⧸ frattini G := QuotientGroup.mk' (frattini G)
  let N : Subgroup G := R.comap q
  let : N.Normal := inferInstance
  let f : N →* R := (q.comp N.subtype).codRestrict R (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (frattini G) (y : G ⧸ frattini G)
    have hxN : x ∈ N := by
      change q x ∈ R
      rw [show q x = y from hx]
      exact y.property
    exact ⟨⟨x, hxN⟩, Subtype.ext hx⟩
  let S : Sylow p N := Sylow.nonempty.some
  have hStop : (S : Subgroup N).map f = ⊤ := by
    exact ((S.mapSurjective hf).is_maximal' (hR.to_subgroup ⊤) le_top).symm
  let P : Subgroup G := (S : Subgroup N).map N.subtype
  have hmap : P.map q = R := by
    calc
      P.map q = ((S : Subgroup N).map f).map R.subtype := by
        change ((S : Subgroup N).map N.subtype).map q = _
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = R := by rw [hStop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hN : P ⊔ frattini G = N := by
    calc
      P ⊔ frattini G = (P.map q).comap q := by
        simpa [q] using (Subgroup.comap_map_eq q P).symm
      _ = N := by rw [hmap]
  have hsup : Subgroup.normalizer (P : Set G) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top S
  have hfrattini : Subgroup.normalizer (P : Set G) ⊔ frattini G = ⊤ := by
    rw [← hN, ← sup_assoc, sup_eq_left.mpr P.le_normalizer] at hsup
    exact hsup
  have hnormal : P.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (frattini_nongenerating hfrattini)
  exact ⟨P, hnormal, S.isPGroup'.map N.subtype, hmap⟩

/-- A nontrivial finite soluble group has a nontrivial normal p-subgroup for some prime p. -/
theorem exists_nontrivial_normal_pSubgroup
    {G : Type u} [Group G] [Finite G] [Nontrivial G] (hsolv : Group.IsSolvable G) :
    ∃ p : ℕ, p.Prime ∧ ∃ P : Subgroup G, P.Normal ∧ IsPGroup p P ∧ P ≠ ⊥ := by
  classical
  have : Group.IsSolvable G := hsolv
  have hfit : fittingSubgroup G ≠ ⊥ := by
    intro h
    have hcard := (fitting_eq_bot_iff_card_eq_one_of_solvable G).mp h
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := G))) hcard
  obtain ⟨p, hp⟩ : ∃ p : (Nat.card G).primeFactors.attach, pCore p.1.1 G ≠ ⊥ := by
    by_contra! h
    apply hfit
    rw [fitting_eq_sup_pCore]
    simp [h]
  exact ⟨p.1.1, Fact.out, pCore p.1.1 G, inferInstance, pCore_isPGroup, hp⟩

/-- A subgroup not contained in the Frattini subgroup has a maximal proper supplement. -/
theorem exists_coatom_sup_eq_top_of_not_le_frattini
    {G : Type u} [Group G] (P : Subgroup G) (hP : ¬ P ≤ frattini G) :
    ∃ M : Subgroup G, IsCoatom M ∧ P ⊔ M = ⊤ := by
  classical
  obtain ⟨M, hM, hPM⟩ : ∃ M : Subgroup G, IsCoatom M ∧ ¬ P ≤ M := by
    by_contra! h
    apply hP
    change P ≤ ⨅ M ∈ {H : Subgroup G | IsCoatom H}, M
    exact le_iInf (fun M => le_iInf (fun hM => h M hM))
  refine ⟨M, hM, hM.2 _ ?_⟩
  refine lt_of_le_of_ne le_sup_right ?_
  intro heq
  apply hPM
  rw [heq]
  exact le_sup_left

/-- A nontrivial finite soluble group has a normal p-subgroup supplemented by a maximal
proper subgroup. The p-subgroup is not contained in the Frattini subgroup. -/
theorem exists_normal_pSubgroup_maximal_supplement
    {G : Type u} [Group G] [Finite G] [Nontrivial G] (hsolv : Group.IsSolvable G) :
    ∃ p : ℕ, p.Prime ∧ ∃ P M : Subgroup G,
      P.Normal ∧ IsPGroup p P ∧ ¬ P ≤ frattini G ∧ IsCoatom M ∧ P ⊔ M = ⊤ := by
  classical
  have : Group.IsSolvable G := hsolv
  have hfrattini : frattini G ≠ ⊤ := by
    intro h
    have hbot : (⊥ : Subgroup G) = ⊤ := frattini_nongenerating (by simp [h])
    exact bot_ne_top hbot
  have : Nontrivial (G ⧸ frattini G) := QuotientGroup.nontrivial_iff.mpr hfrattini
  obtain ⟨p, hp, R, hRnormal, hRp, hRbot⟩ :=
    exists_nontrivial_normal_pSubgroup (G := G ⧸ frattini G) (by infer_instance)
  have : Fact p.Prime := ⟨hp⟩
  have : R.Normal := hRnormal
  obtain ⟨P, hPnormal, hPp, hmap⟩ := exists_normal_pSubgroup_lift_frattini R hRp
  have hP : ¬ P ≤ frattini G := by
    intro h
    apply hRbot
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h
  obtain ⟨M, hM, hsup⟩ := exists_coatom_sup_eq_top_of_not_le_frattini P hP
  exact ⟨p, hp, P, M, hPnormal, hPp, hP, hM, hsup⟩

/-- The structural induction step: a normal p-subgroup and a proper subgroup generate G. -/
theorem exists_normal_pSubgroup_proper_supplement
    {G : Type u} [Group G] [Finite G] [Nontrivial G] (hsolv : Group.IsSolvable G) :
    ∃ p : ℕ, p.Prime ∧ ∃ P M : Subgroup G,
      P.Normal ∧ IsPGroup p P ∧ M ≠ ⊤ ∧ P ⊔ M = ⊤ := by
  obtain ⟨p, hp, P, M, hPnormal, hPp, _, hM, hsup⟩ :=
    exists_normal_pSubgroup_maximal_supplement hsolv
  exact ⟨p, hp, P, M, hPnormal, hPp, hM.1, hsup⟩

end Kourovka2135.Soluble
