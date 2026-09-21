import Kourovka2135.BinaryFrattiniOrderObstruction
import Kourovka2135.BinaryMinimalSimpleReduction
import Kourovka2135.BinarySLTwoProjectiveEquiv

/-! Eliminate the binary SL2 simple-quotient branch of a least exception.
The permitted Thompson classification supplies the already proved proper
subgroup solubility reduction at p=2; every family lifting/character fact is
proved separately. Central radicals are included.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem proper_subgroups_solvable_of_equiv
    {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : ∀ K : Subgroup S, K ≠ ⊤ → Group.IsSolvable K)
    (H : Subgroup T) (hH : H < ⊤) : Group.IsSolvable H := by
  let K := H.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro htop
    apply hH.ne
    apply Subgroup.comap_injective (f := e.toMonoidHom) e.surjective
    simpa only [Subgroup.comap_top] using htop
  let : Group.IsSolvable K := h K hK
  let f : K →* H := {
    toFun := fun x => ⟨e (x : S), x.property⟩
    map_one' := Subtype.ext (map_one e)
    map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨e.symm (y : T), ?_⟩, ?_⟩
    · change e (e.symm (y : T)) ∈ H
      simpa only [e.apply_symm_apply] using y.property
    · apply Subtype.ext
      exact e.apply_symm_apply (y : T)
  exact Group.isSolvable_of_surjective hf

theorem OrderMinimalException.false_of_binary_slTwo_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃* SLTwo.SL2 F) : False := by
  let : Group.IsPerfect G := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (G ⧸ solubleRadical G) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup (SLTwo.SL2 F) := e.symm.isSimpleGroup
  let pi := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical G))
  have hpi : Function.Surjective pi :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical G))
  have hker : pi.ker = solubleRadical G := by
    ext x
    change e (QuotientGroup.mk' (solubleRadical G) x) = 1 ↔ x ∈ solubleRadical G
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  have hR : IsPGroup 2 pi.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hΦ : pi.ker ≤ frattini G := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact not_productOrderCondition_of_binary_frattini_slTwo f hcard hf
    (proper_subgroups_solvable_of_equiv e
      (h.quotient_radical_proper_subgroup_isSolvable_two classification))
    pi hpi hR hΦ w h.condition

theorem OrderMinimalException.false_of_binary_pslTwo_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    False :=
  h.false_of_binary_slTwo_quotient classification f hcard hf
    (e.trans (BinarySLTwoProjectiveEquiv.equiv F).symm)

end Kourovka2135
