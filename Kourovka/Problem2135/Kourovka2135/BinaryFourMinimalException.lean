import Kourovka2135.BinaryFourOrderObstruction
import Kourovka2135.BinarySLTwoMinimalException

/-! Eliminate the four-parameter simple quotient, completing the binary
SL2 family. Thompson is the explicitly permitted classification parameter;
all central-cover, representation, and word-value facts are proved imports. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem OrderMinimalException.false_of_binary_four_slTwo_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hcard : Fintype.card F = 4)
    (e : (G ⧸ solubleRadical G) ≃* SLTwo.SL2 F) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup (SLTwo.SL2 F) := e.symm.isSimpleGroup
  let pi := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hpi : Function.Surjective pi :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : pi.ker = solubleRadical G := by
    exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical G)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical G))
  have hR : IsPGroup 2 pi.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : pi.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact not_productOrderCondition_of_binary_four_frattini hcard
    (proper_subgroups_solvable_of_equiv e
      (h.quotient_radical_proper_subgroup_isSolvable_two classification))
    pi hpi hR hF w h.condition

/-- Every exponent at least two in the binary SL2 family is now included. -/
theorem OrderMinimalException.false_of_binary_slTwo_quotient_of_two_le
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃* SLTwo.SL2 F) : False := by
  by_cases heq : f = 2
  · subst f
    exact h.false_of_binary_four_slTwo_quotient classification hcard e
  · exact h.false_of_binary_slTwo_quotient classification f hcard (by omega) e

/-- The corresponding actual projective groups are included by the proved characteristic-two isomorphism. -/
theorem OrderMinimalException.false_of_binary_pslTwo_quotient_of_two_le
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : False :=
  h.false_of_binary_slTwo_quotient_of_two_le classification f hcard hf
    (e.trans (BinarySLTwoProjectiveEquiv.equiv F).symm)

end Kourovka2135
