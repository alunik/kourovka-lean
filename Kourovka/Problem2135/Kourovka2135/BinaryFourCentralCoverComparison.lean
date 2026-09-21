import Kourovka2135.BinaryFourCentralKernelBound
import Kourovka2135.CentralBinaryExtensionUniqueness
import Kourovka2135.GroupExtensionReindex
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Compare every perfect central binary cover of SL2(4) with any actual
perfect central C2 reference extension. The kernel bound and equality of
ordinary factor-set classes are proved; the reference is an actual short
exact sequence, to be constructed separately in the finite matrix model. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryFourCentralCoverComparison

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable {F : Type} [Field F] [Fintype F] [CharP F 2]

/-- An actual two-element kernel is isomorphic to the additive group of F2. -/
def kernelEquiv (R : Subgroup G) (hcard : Nat.card R = 2) :
    R ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq hcard (by
    change Nat.card (ZMod 2) = 2
    rw [Nat.card_eq_fintype_card, ZMod.card])

/-- Every central binary cover is the quotient itself or the chosen actual double cover. -/
theorem quotient_or_reference
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hc : R ≤ Subgroup.center G)
    (e : SLTwo.SL2 F ≃* G ⧸ R) (hcard : Fintype.card F = 4)
    {E : Type} [Group E] [Group.IsPerfect E]
    (T : GroupExtension (Multiplicative (ZMod 2)) E (SLTwo.SL2 F))
    (hT : T.inl.range ≤ Subgroup.center E) :
    Nonempty (G ≃* SLTwo.SL2 F) ∨
      ∃ j : G ≃* E, ∀ g, T.rightHom (j g) = e.symm (QuotientGroup.mk' R g) := by
  rcases BinaryFourCentralKernelBound.eq_bot_or_card_two R hR hc e hcard with hz | htwo
  · left
    have hq : Function.Bijective (QuotientGroup.mk' R) := by
      refine ⟨?_, QuotientGroup.mk'_surjective R⟩
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hz]
    exact ⟨(MulEquiv.ofBijective (QuotientGroup.mk' R) hq).trans e.symm⟩
  · right
    let a : Multiplicative (ZMod 2) ≃* Multiplicative (Additive R) :=
      (kernelEquiv R htwo).symm.trans (MulEquiv.toMultiplicative_toAdditive (G := R)).symm
    let S := GroupExtensionReindex.reindex (NormalSubgroupExtension.extension R) a e.symm
    have hS : S.inl.range ≤ Subgroup.center G := by
      simpa only [S, GroupExtensionReindex.reindex_inl_range,
        NormalSubgroupExtension.extension_inl_range] using hc
    obtain ⟨j, hj, _⟩ := CentralBinaryExtensionUniqueness.exists_equiv S T hS hT
      (BinaryFourTrivialH2.finrank_H2_le_one F hcard)
    exact ⟨j, hj⟩

end Kourovka2135.BinaryFourCentralCoverComparison
