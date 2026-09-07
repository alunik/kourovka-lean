import Kourovka.Problems.P21_03.Proof.ForestSupportBounds
import Kourovka.Problems.P21_03.Proof.SigmaCardBound

namespace Kourovka213

universe u

open scoped BigOperators

noncomputable local instance forestSupportFiberFintype
    (F : ForestContainer.{u}) (s : ℕ) :
    Fintype {g : F.action.Actor // F.action.supportCard g = s} :=
  Fintype.ofFinite _

noncomputable local instance forestOutsideCoreSupportFiberFintype
    (F : ForestContainer.{u}) (s : ℕ) :
    Fintype {g : F.action.Actor //
      F.action.supportCard g = s ∧
        F.action.toPermHom g ∉ transpositionCore F.action.toPermHom.range} :=
  Fintype.ofFinite _

/-- Restrict the injective raw forest portrait to any predicate whose elements
all have fixed support `s` and at most `q` selected portrait locations. -/
private noncomputable def boundedRawPortraitEmbedding
    (F : ForestContainer.{u}) (s q : ℕ) (P : F.action.Actor → Prop)
    (hs : ∀ g, P g → F.action.supportCard g = s)
    (hcard : ∀ g, P g → (F.portraitLocations g).card < q + 1) :
    {g : F.action.Actor // P g} ↪
      (Σ k : Fin (q + 1),
        RawWeightedConfiguration (ForestLocation F) (256 ^ 2) s k) := by
  classical
  let pack : {g : F.action.Actor // P g} →
      (Σ k : Fin (q + 1),
        RawWeightedConfiguration (ForestLocation F) (256 ^ 2) s k) :=
    fun g ↦
      ⟨⟨(F.portraitLocations g.1).card, hcard g.1 g.2⟩,
        hs g.1 g.2 ▸ F.rawPortrait g.1⟩
  let forget :
      (Σ k : Fin (q + 1),
        RawWeightedConfiguration (ForestLocation F) (256 ^ 2) s k) →
        (Σ t : ℕ, Σ k : ℕ,
          RawWeightedConfiguration (ForestLocation F) (256 ^ 2) t k) :=
    fun c ↦ ⟨s, c.1, c.2⟩
  have hforget : ∀ g : {g : F.action.Actor // P g},
      forget (pack g) = F.packedRawPortrait g.1 := by
    rintro ⟨g, hg⟩
    dsimp only [forget, pack, ForestContainer.packedRawPortrait]
    cases hs g hg
    rfl
  refine ⟨pack, ?_⟩
  intro g h hgh
  apply Subtype.ext
  apply F.packedRawPortrait_injective
  calc
    F.packedRawPortrait g.1 = forget (pack g) := (hforget g).symm
    _ = forget (pack h) := congrArg forget hgh
    _ = F.packedRawPortrait h.1 := hforget h

/-- Applying the canonical code independently in every sigma fibre is an
embedding of bounded raw configurations into bounded finite codes. -/
private noncomputable def sigmaRawWeightedConfigurationEmbedding
    (Site : Type u) [Fintype Site] [LinearOrder Site]
    (D s q : ℕ) :
    (Σ k : Fin (q + 1), RawWeightedConfiguration Site D s k) ↪
      (Σ k : Fin (q + 1), WeightedConfigurationCode Site D s k) where
  toFun c := ⟨c.1, c.2.toCode⟩
  inj' := by
    rintro ⟨k, c⟩ ⟨l, d⟩ h
    have hkl : k = l := congrArg Sigma.fst h
    subst l
    have hcode : c.toCode = d.toCode :=
      eq_of_heq (Sigma.ext_iff.mp h).2
    have hcd : c = d := RawWeightedConfiguration.toCode_injective hcode
    subst d
    rfl

/-- Fixed-support forest actors embed into codes with at most `s / 2`
locations. -/
noncomputable def ForestContainer.supportFiberCodeEmbedding
    (F : ForestContainer.{u}) (s : ℕ) :
    {g : F.action.Actor // F.action.supportCard g = s} ↪
      (Σ k : Fin (s / 2 + 1),
        WeightedConfigurationCode (ForestLocation F) (256 ^ 2) s k) := by
  classical
  letI : LinearOrder (ForestLocation F) :=
    LinearOrder.lift' (Fintype.equivFin (ForestLocation F))
      (Fintype.equivFin (ForestLocation F)).injective
  let raw := boundedRawPortraitEmbedding F s (s / 2)
    (fun g ↦ F.action.supportCard g = s)
    (fun _ hg ↦ hg)
    (by
      intro g hg
      have h := F.two_mul_card_portraitLocations_le_supportCard g
      rw [hg] at h
      omega)
  exact raw.trans
    (sigmaRawWeightedConfigurationEmbedding (ForestLocation F)
      (256 ^ 2) s (s / 2))

/-- Fixed-support actors outside the transposition core embed into codes with
at most `(s - 1) / 2` locations. -/
noncomputable def ForestContainer.outsideCoreSupportFiberCodeEmbedding
    (F : ForestContainer.{u}) (s : ℕ) :
    {g : F.action.Actor //
      F.action.supportCard g = s ∧
        F.action.toPermHom g ∉ transpositionCore F.action.toPermHom.range} ↪
      (Σ k : Fin ((s - 1) / 2 + 1),
        WeightedConfigurationCode (ForestLocation F) (256 ^ 2) s k) := by
  classical
  letI : LinearOrder (ForestLocation F) :=
    LinearOrder.lift' (Fintype.equivFin (ForestLocation F))
      (Fintype.equivFin (ForestLocation F)).injective
  let raw := boundedRawPortraitEmbedding F s ((s - 1) / 2)
    (fun g ↦ F.action.supportCard g = s ∧
      F.action.toPermHom g ∉ transpositionCore F.action.toPermHom.range)
    (fun _ hg ↦ hg.1)
    (by
      intro g hg
      have h :=
        F.two_mul_card_portraitLocations_le_supportCard_sub_one_of_not_core
          g hg.2
      rw [hg.1] at h
      omega)
  exact raw.trans
    (sigmaRawWeightedConfigurationEmbedding (ForestLocation F)
      (256 ^ 2) s ((s - 1) / 2))

/-- Cardinal form of `supportFiberCodeEmbedding`. -/
theorem ForestContainer.card_supportFiber_le_sum_weightedConfigurationCode
    (F : ForestContainer.{u}) (s : ℕ) :
    Fintype.card {g : F.action.Actor // F.action.supportCard g = s} ≤
      ∑ k ∈ Finset.range (s / 2 + 1),
        Fintype.card
          (WeightedConfigurationCode (ForestLocation F) (256 ^ 2) s k) := by
  classical
  exact card_le_sum_weightedConfigurationCode_of_embedding
    (256 ^ 2) s (s / 2) (F.supportFiberCodeEmbedding s)

/-- Cardinal form of `outsideCoreSupportFiberCodeEmbedding`. -/
theorem ForestContainer.card_outsideCoreSupportFiber_le_sum_weightedConfigurationCode
    (F : ForestContainer.{u}) (s : ℕ) :
    Fintype.card {g : F.action.Actor //
      F.action.supportCard g = s ∧
        F.action.toPermHom g ∉ transpositionCore F.action.toPermHom.range} ≤
      ∑ k ∈ Finset.range ((s - 1) / 2 + 1),
        Fintype.card
          (WeightedConfigurationCode (ForestLocation F) (256 ^ 2) s k) := by
  classical
  exact card_le_sum_weightedConfigurationCode_of_embedding
    (256 ^ 2) s ((s - 1) / 2)
      (F.outsideCoreSupportFiberCodeEmbedding s)

end Kourovka213
