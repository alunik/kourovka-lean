import Kourovka2135.BinaryFourCentralCoverComparison
import Kourovka2135.BinaryFourAlternatingEquiv
import Kourovka2135.SLTwoFiveAlternating

/-! The actual finite matrix double cover supplies the reference extension.
Consequently every perfect central binary cover of SL2(4) is isomorphic to
SL2(4) or SL2(F5), without an assumed Schur multiplier or exceptional isomorphism. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryFourCentralCoverModels

abbrev C2 := Multiplicative (ZMod 2)
abbrev E := SLTwoFiveAlternating.S
abbrev A5 := alternatingGroup (Fin 5)

/-- Identify the proved two-element matrix kernel with the actual scalar kernel. -/
def matrixKernelEquiv : SLTwoFiveAlternating.toAlternating.ker ≃* C2 :=
  mulEquivOfPrimeCardEq SLTwoFiveAlternating.card_ker (by
    change Nat.card (ZMod 2) = 2
    rw [Nat.card_eq_fintype_card, ZMod.card])

/-- The actual short exact sequence of finite matrix groups and permutations. -/
def extensionA5 : GroupExtension C2 E A5 where
  inl := SLTwoFiveAlternating.toAlternating.ker.subtype.comp matrixKernelEquiv.symm.toMonoidHom
  rightHom := SLTwoFiveAlternating.toAlternating
  inl_injective := Subtype.val_injective.comp matrixKernelEquiv.symm.injective
  rightHom_surjective := SLTwoFiveAlternating.toAlternating_surjective
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      exact (matrixKernelEquiv.symm n).property
    · intro hg
      refine ⟨matrixKernelEquiv ⟨g, hg⟩, ?_⟩
      change (matrixKernelEquiv.symm (matrixKernelEquiv ⟨g, hg⟩)).val = g
      rw [matrixKernelEquiv.symm_apply_apply]

theorem extensionA5_central : extensionA5.inl.range ≤ Subgroup.center E := by
  rw [extensionA5.range_inl_eq_ker_rightHom]
  change SLTwoFiveAlternating.toAlternating.ker ≤ Subgroup.center E
  rw [SLTwoFiveAlternating.ker_eq_center]

/-- Reindex the actual quotient by the constructed four-parameter projective action. -/
def extensionSLTwo
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hcard : Fintype.card F = 4) :
    GroupExtension C2 E (SLTwo.SL2 F) :=
  GroupExtensionReindex.reindex extensionA5 (MulEquiv.refl C2)
    (BinaryFourAlternatingEquiv.equiv hcard).symm

theorem extensionSLTwo_central
    {F : Type} [Field F] [Fintype F] [CharP F 2] (hcard : Fintype.card F = 4) :
    (extensionSLTwo hcard).inl.range ≤ Subgroup.center E := by
  simpa only [extensionSLTwo, GroupExtensionReindex.reindex_inl_range] using extensionA5_central

/-- The actual matrix alternatives for every perfect central binary cover of SL2(4). -/
theorem quotient_or_matrix_cover
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hc : R ≤ Subgroup.center G)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* G ⧸ R) (hcard : Fintype.card F = 4) :
    Nonempty (G ≃* SLTwo.SL2 F) ∨
      ∃ j : G ≃* E, ∀ g, SLTwoFiveAlternating.toAlternating (j g) =
        BinaryFourAlternatingEquiv.equiv hcard (e.symm (QuotientGroup.mk' R g)) := by
  let : Group.IsPerfect E := SLTwoFiveAlternating.isPerfect
  rcases BinaryFourCentralCoverComparison.quotient_or_reference R hR hc e hcard
      (extensionSLTwo hcard) (extensionSLTwo_central hcard) with hs | hd
  · exact Or.inl hs
  · obtain ⟨j, hj⟩ := hd
    right
    refine ⟨j, fun g => ?_⟩
    have h := congrArg (BinaryFourAlternatingEquiv.equiv hcard) (hj g)
    simpa only [extensionSLTwo, GroupExtensionReindex.reindex_rightHom,
      MulEquiv.apply_symm_apply, extensionA5] using h

end Kourovka2135.BinaryFourCentralCoverModels
