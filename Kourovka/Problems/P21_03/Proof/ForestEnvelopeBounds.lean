import Kourovka.Problems.P21_03.Proof.TargetEnvelopeCore
import Kourovka.Problems.P21_03.Proof.ForestSliceEncoding
import Kourovka.Problems.P21_03.Proof.PortraitBoundArithmetic
import Kourovka.Problems.P21_03.Proof.LowerBound

namespace Kourovka213

universe u w z

open scoped BigOperators

namespace ActionEmbedding

/-- A permutation in an exact-support slice of the transported target envelope,
pulled back to the actor of the target action. -/
noncomputable def positiveTargetEnvelopeSupportSliceEmbedding
    {n : ℕ} (H : SolubleSubgroup n) (hn : 0 < n)
    {B : SolubleAction.{w, z}}
    (f : ActionEmbedding (H.positiveAction hn) B) (s : ℕ) :
    {p : Sym n // p ∈ supportSlice f.targetEnvelope s} ↪
      {g : B.Actor // B.supportCard g = s} where
  toFun p := by
    let q : f.targetEnvelope :=
      ⟨p.1, (mem_supportSlice.mp p.2).1⟩
    let g : B.Actor := f.targetEnvelopeMulEquiv.symm q
    refine ⟨g, ?_⟩
    rw [← f.targetEnvelopeMulEquiv_supportCard g]
    have heq : f.targetEnvelopeMulEquiv g = q :=
      f.targetEnvelopeMulEquiv.apply_symm_apply q
    rw [heq]
    exact (mem_supportSlice.mp p.2).2
  inj' := by
    intro p q hpq
    apply Subtype.ext
    have hactor :
        f.targetEnvelopeMulEquiv.symm
            ⟨p.1, (mem_supportSlice.mp p.2).1⟩ =
          f.targetEnvelopeMulEquiv.symm
            ⟨q.1, (mem_supportSlice.mp q.2).1⟩ :=
      congrArg Subtype.val hpq
    have htarget := congrArg f.targetEnvelopeMulEquiv hactor
    have hperm := congrArg Subtype.val htarget
    simp only [MulEquiv.apply_symm_apply] at hperm
    change p.1 = q.1 at hperm
    exact hperm

/-- The analogous pullback for the part of a support slice outside the
transposition core. -/
noncomputable def positiveTargetEnvelopeOutsideCoreSliceEmbedding
    {n : ℕ} (H : SolubleSubgroup n) (hn : 0 < n)
    {B : SolubleAction.{w, z}}
    (f : ActionEmbedding (H.positiveAction hn) B) (s : ℕ) :
    {p : Sym n // p ∈ outsideCoreSlice f.targetEnvelope s} ↪
      {g : B.Actor //
        B.supportCard g = s ∧
          B.toPermHom g ∉ transpositionCore B.toPermHom.range} where
  toFun p := by
    let q : f.targetEnvelope :=
      ⟨p.1, (mem_outsideCoreSlice.mp p.2).1⟩
    let g : B.Actor := f.targetEnvelopeMulEquiv.symm q
    refine ⟨g, ?_, ?_⟩
    · rw [← f.targetEnvelopeMulEquiv_supportCard g]
      have heq : f.targetEnvelopeMulEquiv g = q :=
        f.targetEnvelopeMulEquiv.apply_symm_apply q
      rw [heq]
      exact (mem_outsideCoreSlice.mp p.2).2.1
    · intro hg
      have hq :=
        (f.targetEnvelopeMulEquiv_mem_transpositionCore_iff g).mpr hg
      have heq : f.targetEnvelopeMulEquiv g = q :=
        f.targetEnvelopeMulEquiv.apply_symm_apply q
      rw [heq] at hq
      exact (mem_outsideCoreSlice.mp p.2).2.2 hq
  inj' := by
    intro p q hpq
    apply Subtype.ext
    have hactor :
        f.targetEnvelopeMulEquiv.symm
            ⟨p.1, (mem_outsideCoreSlice.mp p.2).1⟩ =
          f.targetEnvelopeMulEquiv.symm
            ⟨q.1, (mem_outsideCoreSlice.mp q.2).1⟩ :=
      congrArg Subtype.val hpq
    have htarget := congrArg f.targetEnvelopeMulEquiv hactor
    have hperm := congrArg Subtype.val htarget
    simp only [MulEquiv.apply_symm_apply] at hperm
    change p.1 = q.1 at hperm
    exact hperm

end ActionEmbedding


/-- The transported full forest group satisfies the two support estimates. -/
theorem SolubleSubgroup.forestEnvelope_supportBounds
    {n : ℕ} (H : SolubleSubgroup n) (hn : 0 < n) :
    SupportBoundsFor (16 * (256 ^ 2)) (H.forestEnvelope hn) := by
  classical
  let D := (H.positiveAction hn).forestRealizationData
  apply supportBoundsFor_of_weightedConfiguration_encodings
    (H.forestEnvelope hn) (ForestLocation D.1) (256 ^ 2)
  · calc
      Fintype.card (ForestLocation D.1) ≤ D.1.degree :=
        D.1.card_forestLocation_le
      _ = (H.positiveAction hn).degree := D.2.degree_eq.symm
      _ = n := H.positiveAction_degree hn
  · intro s _hs _hsn
    change (supportSlice D.2.targetEnvelope s).card ≤ _
    let e :=
      (ActionEmbedding.positiveTargetEnvelopeSupportSliceEmbedding H hn D.2 s).trans
        (ForestContainer.supportFiberCodeEmbedding D.1 s)
    have h := card_le_sum_weightedConfigurationCode_of_embedding
      (256 ^ 2) s (s / 2) e
    simpa only [Fintype.card_coe] using h
  · intro s _hs _hsn
    change (outsideCoreSlice D.2.targetEnvelope s).card ≤ _
    let e :=
      (ActionEmbedding.positiveTargetEnvelopeOutsideCoreSliceEmbedding H hn D.2 s).trans
        (ForestContainer.outsideCoreSupportFiberCodeEmbedding D.1 s)
    have h := card_le_sum_weightedConfigurationCode_of_embedding
      (256 ^ 2) s ((s - 1) / 2) e
    simpa only [Fintype.card_coe] using h

/-- Every positive-degree soluble subgroup is contained in a full forest
envelope with uniform support constant `16 * 256²`. -/
theorem positiveSupportEnvelopeBounds :
    PositiveSupportEnvelopeBounds (16 * (256 ^ 2)) := by
  intro n H hn
  exact ⟨H.forestEnvelope hn, H.le_forestEnvelope hn,
    H.forestEnvelope_supportBounds hn⟩


end Kourovka213
