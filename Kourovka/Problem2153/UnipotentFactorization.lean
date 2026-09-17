import Kourovka.Problem2153.RootCollection
import Kourovka.Problem2153.RankOne.Radicals
import Kourovka.Problem2153.Structure.BNBridge

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem

open RankOne RootRelations RootCollection WilsonModel.RootData.Relations

/-- In the actual 90 checked commutators between distinct positive root curves,
the three coordinates belonging to the two simple rank-one groups vanish.
This fact is checked on the data rather than inferred from the root ordering. -/
theorem commutator_representative_radical_support : ∀ k : Fin 90,
    (commutatorData k).coords 0 = 0 ∧ (commutatorData k).coords 1 = 0 ∧
      (commutatorData k).coords 3 = 0 := by decide +kernel

theorem commutator_radical_support (i j : Fin 12) (a b : Fin 8) :
    commutatorCoordinates i j a b 0 = 0 ∧
      commutatorCoordinates i j a b 1 = 0 ∧ commutatorCoordinates i j a b 3 = 0 := by
  by_cases hz : a = 0 ∨ b = 0
  · simp [commutatorCoordinates, hz]
  obtain ⟨h0, h1, h3⟩ :=
    commutator_representative_radical_support (commutatorSelector i j a b).1
  simp [commutatorCoordinates, hz, transportCoordinates, h0, h1, h3, parameterAction_zero]

theorem coordinateGroup_mem_Vr (v : Coordinates) (h1 : v 1 = 0) (h3 : v 3 = 0) :
    coordinateGroup v ∈ Vr := by
  apply coordinateGroup_mem
  intro i hi
  apply root_mem_Vr i
  · rintro rfl
    exact hi h1
  · rintro rfl
    exact hi h3

theorem coordinateGroup_mem_Vs (v : Coordinates) (h0 : v 0 = 0) :
    coordinateGroup v ∈ Vs := by
  apply coordinateGroup_mem
  intro i hi
  apply root_mem_Vs i
  rintro rfl
  exact hi h0

theorem root_commutator_mem_Vr (i j : Fin 12) (a b : Fin 8) (hij : i < j) :
    (root i a)⁻¹ * (root j b)⁻¹ * root i a * root j b ∈ Vr := by
  rw [root_commutator i j a b hij]
  have h := commutator_radical_support i j a b
  exact coordinateGroup_mem_Vr _ h.2.1 h.2.2

theorem root_commutator_mem_Vs (i j : Fin 12) (a b : Fin 8) (hij : i < j) :
    (root i a)⁻¹ * (root j b)⁻¹ * root i a * root j b ∈ Vs := by
  rw [root_commutator i j a b hij]
  exact coordinateGroup_mem_Vs _ (commutator_radical_support i j a b).1

theorem root_conj_mem_Vr (i j : Fin 12) (hi : i = 1 ∨ i = 3)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (a b : Fin 8) :
    rightConj (root j b) (root i a) ∈ Vr := by
  apply Collection.rightConj_mem_of_commutator Vr (root i a) (root j b)
    (root_mem_Vr j hj1 hj3 b)
  have hne : i ≠ j := by
    rintro rfl
    rcases hi with h | h
    · exact hj1 h
    · exact hj3 h
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact root_commutator_mem_Vr i j a b hij
  · simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      Vr.inv_mem (root_commutator_mem_Vr j i b a hji)

theorem root_conj_mem_Vs (j : Fin 12) (hj : j ≠ 0) (a b : Fin 8) :
    rightConj (root j b) (root 0 a) ∈ Vs := by
  apply Collection.rightConj_mem_of_commutator Vs (root 0 a) (root j b)
    (root_mem_Vs j hj b)
  exact root_commutator_mem_Vs 0 j a b (by omega)

/-- A one-sided conjugation inclusion is enough in this finite group: the
inverse conjugation is a nonnegative power of the original one. -/
theorem mem_normalizer_of_rightConj_stable (Q : Subgroup G) (g : G)
    (h : ∀ x ∈ Q, rightConj x g ∈ Q) : g ∈ Subgroup.normalizer (Q : Set G) := by
  have hpow : ∀ n : ℕ, ∀ x ∈ Q, rightConj x (g ^ n) ∈ Q := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa [rightConj] using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, rightConj_mul]
      exact h _ (ih x hx)
  have hinv : g ^ (orderOf g - 1) = g⁻¹ := by
    rw [pow_sub g (orderOf_pos g), pow_orderOf_eq_one, pow_one, one_mul]
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · exact h x
  · intro hx
    have hback := hpow (orderOf g - 1) (rightConj x g) hx
    rwa [hinv, rightConj_inv_cancel] at hback

theorem rank_root_mem_normalizer_Vr (i : Fin 12) (hi : i = 1 ∨ i = 3) (a : Fin 8) :
    root i a ∈ Subgroup.normalizer (Vr : Set G) := by
  apply mem_normalizer_of_rightConj_stable
  intro g hg
  apply Collection.rightConj_mem_closure_of_generators _ Vr (root i a) ?_ hg
  rintro _ ⟨j, hj1, hj3, b, rfl⟩
  exact root_conj_mem_Vr i j hi hj1 hj3 a b

theorem rank_root_mem_normalizer_Vs (a : Fin 8) :
    root 0 a ∈ Subgroup.normalizer (Vs : Set G) := by
  apply mem_normalizer_of_rightConj_stable
  intro g hg
  apply Collection.rightConj_mem_closure_of_generators _ Vs (root 0 a) ?_ hg
  rintro _ ⟨j, hj, b, rfl⟩
  exact root_conj_mem_Vs j hj a b

theorem Rr_le_normalizer_Vr : Rr ≤ Subgroup.normalizer (Vr : Set G) := by
  rw [Rr_eq]
  apply (Subgroup.closure_le _).mpr
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact rank_root_mem_normalizer_Vr 1 (Or.inl rfl) a
  · exact rank_root_mem_normalizer_Vr 3 (Or.inr rfl) a

theorem Rs_le_normalizer_Vs : Rs ≤ Subgroup.normalizer (Vs : Set G) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  exact rank_root_mem_normalizer_Vs a

private theorem U_le_of_root_mem (Q : Subgroup G) (h : ∀ i a, root i a ∈ Q) : U ≤ Q := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨curve, hcurve, a, rfl⟩
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hcurve
  rcases hcurve with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact h _ a

theorem U_eq_Rr_sup_Vr : U = Rr ⊔ Vr := by
  apply le_antisymm
  · apply U_le_of_root_mem
    intro i a
    by_cases hi1 : i = 1
    · subst i
      exact (show Rr ≤ Rr ⊔ Vr from le_sup_left) (root_one_mem_Rr a)
    by_cases hi3 : i = 3
    · subst i
      exact (show Rr ≤ Rr ⊔ Vr from le_sup_left) (root_three_mem_Rr a)
    exact (show Vr ≤ Rr ⊔ Vr from le_sup_right) (root_mem_Vr i hi1 hi3 a)
  · exact sup_le Rr_le_U Vr_le_U

theorem U_eq_Rs_sup_Vs : U = Rs ⊔ Vs := by
  apply le_antisymm
  · apply U_le_of_root_mem
    intro i a
    by_cases hi : i = 0
    · subst i
      exact (show Rs ≤ Rs ⊔ Vs from le_sup_left) (sRoot_mem_Rs a)
    exact (show Vs ≤ Rs ⊔ Vs from le_sup_right) (root_mem_Vs i hi a)
  · exact sup_le Rs_le_U Vs_le_U

/-- Every positive-unipotent element has a rank-one factor followed by a radical factor. -/
theorem U_factor_r (u : G) (hu : u ∈ U) : ∃ a ∈ Rr, ∃ v ∈ Vr, u = a * v := by
  apply ReeStructural.sup_factor_left Vr Rr Rr_le_normalizer_Vr
  rwa [sup_comm, ← U_eq_Rr_sup_Vr]

theorem U_factor_s (u : G) (hu : u ∈ U) : ∃ a ∈ Rs, ∃ v ∈ Vs, u = a * v := by
  apply ReeStructural.sup_factor_left Vs Rs Rs_le_normalizer_Vs
  rwa [sup_comm, ← U_eq_Rs_sup_Vs]

#print axioms U_factor_r
#print axioms U_factor_s

end Kourovka.Problem2153.RootSystem
