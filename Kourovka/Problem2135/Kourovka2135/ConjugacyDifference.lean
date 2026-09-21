import Kourovka2135.RelativeCongruence

/-!
# Conjugacy differences and single-value obstructions

These are group identities used in the conditional centralization argument.
The normal subgroup need not be abelian.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

def conjugacyDifferences (P : Subgroup G) (x : G) : Set G :=
  {d | ∃ t ∈ P, d = paperCommutator x t}

theorem conjugacyDifferences_subset (P : Subgroup G) [P.Normal] (x : G) :
    conjugacyDifferences P x ⊆ P := by
  rintro _ ⟨t, ht, rfl⟩
  change paperCommutator x t ∈ P
  have hh := (inferInstance : P.Normal).conj_mem t⁻¹ (P.inv_mem ht) x⁻¹
  simpa only [paperCommutator, inv_inv, mul_assoc] using P.mul_mem hh ht

/-- Conjugating a commutator with an element centralizing x returns a
conjugacy difference. The conjugator is the original t. -/
theorem conjugate_commutator_difference (x t b : G) (hxb : Commute x b) :
    t * paperCommutator (paperCommutator x t) b * t⁻¹ =
      paperCommutator x (b⁻¹ * t * b * t⁻¹) := by
  have h₁ : x * b⁻¹ * x⁻¹ = b⁻¹ := by
    rw [hxb.inv_right.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have h₂ : b * x * b⁻¹ = x := by
    rw [hxb.symm.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hl : t * paperCommutator (paperCommutator x t) b * t⁻¹ =
      x⁻¹ * t * (x * b⁻¹ * x⁻¹) * t⁻¹ * x * t * b * t⁻¹ := by
    simp only [paperCommutator]
    group
  have hr : paperCommutator x (b⁻¹ * t * b * t⁻¹) =
      x⁻¹ * t * b⁻¹ * t⁻¹ * (b * x * b⁻¹) * t * b * t⁻¹ := by
    simp only [paperCommutator]
    group
  rw [hl, hr, h₁, h₂]

theorem exists_conjugate_commutator_mem_differences
    (P : Subgroup G) [P.Normal] {x d b : G}
    (hd : d ∈ conjugacyDifferences P x) (hxb : Commute x b) :
    ∃ t ∈ P, t * paperCommutator d b * t⁻¹ ∈ conjugacyDifferences P x := by
  obtain ⟨t, ht, rfl⟩ := hd
  refine ⟨t, ht, b⁻¹ * t * b * t⁻¹, ?_, conjugate_commutator_difference x t b hxb⟩
  have hh := (inferInstance : P.Normal).conj_mem t ht b⁻¹
  exact P.mul_mem (by simpa only [inv_inv] using hh) (P.inv_mem ht)

theorem ProductOrderCondition.difference_value_eq_one
    {w : OuterWord} {p : ℕ} (hp : p.Prime)
    (h : ProductOrderCondition w p G) (P : Subgroup G) [P.Normal]
    (hP : IsPGroup p P) {x d : G} (hx : x ∈ w.values G)
    (hxp : ¬ p ∣ orderOf x) (hd : d ∈ conjugacyDifferences P x)
    (hdw : d ∈ w.values G) : d = 1 := by
  obtain ⟨t, ht, rfl⟩ := hd
  exact h.commutator_eq_one_of_mem_pSubgroup hp hx hxp hdw P hP
    (conjugacyDifferences_subset P x ⟨t, ht, rfl⟩)

theorem ProductOrderCondition.commutator_difference_value_eq_one
    {w : OuterWord} {p : ℕ} (hp : p.Prime)
    (h : ProductOrderCondition w p G) (P : Subgroup G) [P.Normal]
    (hP : IsPGroup p P) {x d b : G} (hx : x ∈ w.values G)
    (hxp : ¬ p ∣ orderOf x) (hd : d ∈ conjugacyDifferences P x)
    (hxb : Commute x b) (hc : paperCommutator d b ∈ w.values G) :
    paperCommutator d b = 1 := by
  obtain ⟨t, ht, hdiff⟩ := exists_conjugate_commutator_mem_differences P hd hxb
  have hc' : t * paperCommutator d b * t⁻¹ ∈ w.values G := by
    simpa only [inv_inv] using w.conj_mem_values hc t⁻¹
  have heq := h.difference_value_eq_one hp P hP hx hxp hdiff hc'
  have hh := congrArg (fun z : G => t⁻¹ * z * t) heq
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_one,
    inv_mul_cancel] using hh

end Kourovka2135
