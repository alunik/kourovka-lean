import Kourovka2135.SuzukiLargeBinaryNoncentral
import Kourovka2135.SuzukiEightTensorCohomology
import Kourovka2135.SuzukiEightCentralBase

/-! The actual binary noncentral Sz(8) branch. The proved two-generator norm
bound supplies the tensor cohomology estimate, and the actual paired central
cover supplies the central base. The endpoint has no representation, cohomology,
or central-cover hypotheses. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Kourovka2135.SuzukiEightBinaryNoncentral

open SuzukiTorusMovingRank SuzukiTensorNatural SuzukiTensorMovingRank

private theorem scale_correction (d H R : ℕ) (h : 2 + 2 * H ≤ R) :
    2 * d + 2 * (d * H) ≤ d * R := by nlinarith

/-- Every actual Sz(8) tensor satisfies the correction alternative. -/
theorem tensor_alternative (k : Type) [Field k] [CharP k 2]
    (σ : K 1 →+* k) [Group.IsPerfect (G 1)] (I : Finset (Fin 3))
    (u : (K 1)ˣ) (hu : u ≠ 1) :
    Module.finrank k (groupCohomology (Rep.of (representation k 1 I σ)) 1) = 0 ∨
      2 + 2 * Module.finrank k (groupCohomology (Rep.of (representation k 1 I σ)) 1) ≤
        Module.finrank k (representation k 1 I σ (torusHom 1 u) - LinearMap.id).range := by
  by_cases h0 : I.card = 0
  · have hI : I = ∅ := Finset.card_eq_zero.mp h0
    subst I
    left
    let : Subsingleton (groupCohomology (Rep.of (representation k 1 ∅ σ)) 1) :=
      PerfectIrreducibleCohomology.subsingleton_H1_of_trivial _
        (SuzukiIrreducibleClassification.emptyRepresentation k 1 σ)
    exact Module.finrank_zero_of_subsingleton
  have hI : I.Nonempty := Finset.card_pos.mp (by omega)
  have hH := SuzukiEightTensorCohomology.finrank_H1_le_quarter k σ I hI
  right
  by_cases h1 : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    have he := RepresentationMovingConjugacy.finrank_moving_eq_of_equiv
      (representation k 1 {i} σ) (naturalTwist k 1 σ i.val)
      (SuzukiLargeBinaryNoncentral.singletonEquiv k 1 σ i) (torusHom 1 u)
    rw [SuzukiLargeBinaryNoncentral.naturalTwist_moving_eq_four k 1 σ i.val u hu] at he
    simp only [Finset.card_singleton, Nat.sub_self, pow_zero] at hH
    omega
  · have hr := three_quarters_le_rank k 1 σ u I hu hI
    have hp : 4 ≤ 4 ^ (I.card - 1) := by
      calc
        4 = 4 ^ (1 : ℕ) := by norm_num
        _ ≤ 4 ^ (I.card - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

section Descent
variable [Group.IsPerfect (G 1)]
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (ρ : Representation (ZMod 2) (G 1) V) [ρ.IsIrreducible]

open IrreducibleEndCohomology MinimalEndMovingRank

theorem binary_bound_torus (u : (K 1)ˣ) (hu : u ≠ 1)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) :
    BinaryRepresentationCorrection.Bound ρ (torusHom 1 u) := by
  obtain ⟨I, ⟨e⟩⟩ := SuzukiIrreducibleClassification.exists_tensor_equiv
    (ClosedField ρ) 1 (SuzukiLargeBinaryNoncentral.parameterEmbedding 1 ρ) (extended ρ)
  have ha := tensor_alternative (ClosedField ρ) (SuzukiLargeBinaryNoncentral.parameterEmbedding 1 ρ) I u hu
  rw [← RepresentationCohomologyAlternative.finrank_cohomology_eq _ _ e 1,
    ← RepresentationMovingConjugacy.finrank_moving_eq_of_equiv _ _ e] at ha
  rcases ha with hz | hr
  · left
    let : FiniteDimensional (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) :=
      GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρ.dual 0
    apply (Module.finrank_zero_iff (R := ZMod 2)
      (M := groupCohomology (Rep.of ρ.dual) 1)).mp
    rw [hdual, finrank_cohomology_eq_closed ρ 0, hz, mul_zero]
  · right
    rw [hdual, finrank_cohomology_eq_closed ρ 0, finrank_moving_eq_closed ρ]
    change 2 * Module.finrank (ZMod 2) (EndField ρ) + _ ≤ _
    exact scale_correction (Module.finrank (ZMod 2) (EndField ρ)) _ _ hr

theorem binary_bound_split_prime (r : ℕ) [Fact r.Prime]
    (hr : r ∣ SuzukiGeometry.q 1 - 1) (g : G 1) (hg : orderOf g = r)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) :
    BinaryRepresentationCorrection.Bound ρ g := by
  obtain ⟨u, hu, hc⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime 1 hr g hg
  have hne : u ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hu
    exact (Fact.out : r.Prime).ne_one hu.symm
  rcases binary_bound_torus ρ u hne hdual with hz | hmoving
  · exact Or.inl hz
  · right
    rwa [RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hc] at hmoving
end Descent

section Fiber
open scoped IsMulCommutative
variable {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
variable (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup A, L.Normal → L < N → L ≤ Subgroup.center A)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup A) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini A)
variable [IsSimpleGroup (A ⧸ R)] (e : (A ⧸ R) ≃* G 1)

include hN hmin hnonabelian hR hRΦ e in
theorem full_fiber (r : ℕ) [Fact r.Prime] (hr : r ∣ SuzukiGeometry.q 1 - 1)
    (a b : A) (hgen : Subgroup.closure ({a, b} : Set A) = ⊤)
    (hc : orderOf (e (QuotientGroup.mk' R (paperCommutator a b))) = r) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsPerfect (G 1) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let τ : Representation (ZMod 2) (G 1) (Additive (N ⧸ Subgroup.center N)) :=
    ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e.symm
  have hd := BinaryRepresentationCorrection.dual_finrank_eq_of_comp ρ e.symm
    (minimalCenterDualCohomology_finrank_eq N hN hmin R hR hnonabelian 1)
  have hs := binary_bound_split_prime τ r hr
    (e (QuotientGroup.mk' R (paperCommutator a b))) hc hd
  have hb := BinaryRepresentationCorrection.of_comp ρ e.symm
    (QuotientGroup.mk' R (paperCommutator a b)) hs
  have hne : QuotientGroup.mk' R (paperCommutator a b) ≠ 1 := by
    intro he
    rw [he, map_one, orderOf_one] at hc
    exact (Fact.out : r.Prime).ne_one hc.symm
  exact exists_paperCommutator_mul_eq_of_minimal_binary_bound
    N hN hmin hnonabelian R hR hRΦ a b hgen hne hb t
end Fiber

section Frattini
open BinaryFrattiniFullFiberInduction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_dvd : 7 ∣ SuzukiGeometry.q 1 - 1 := by decide

theorem preimage_good
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G 1) [IsSimpleGroup (A ⧸ pi.ker)]
    (hpi : Function.Surjective pi) (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A)
    (N : Subgroup A) [N.Normal] (hNR : N ≤ pi.ker)
    (hmin : ∀ L : Subgroup A, L.Normal → L < N → L ≤ Subgroup.center A)
    (hnon : ¬ IsMulCommutative N) (Y : Set (A ⧸ N)) (hY : IsGeneratingGoodSet Y)
    (hsub : Y ⊆ (QuotientGroup.lift N pi hNR) ⁻¹' SuzukiSplitGoodSet.orderSet 1 7) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  refine IsGeneratingGoodSet.preimage_quotient_of_full_fiber
    (G := A) N (hNR.trans hF) hY ?_
  intro a b hgen hc t
  let e : (A ⧸ pi.ker) ≃* G 1 := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have hmem := hsub hc
  change orderOf ((QuotientGroup.lift N pi hNR)
    (QuotientGroup.mk' N (paperCommutator a b))) = 7 at hmem
  have hlift : (QuotientGroup.lift N pi hNR)
      (QuotientGroup.mk' N (paperCommutator a b)) = pi (paperCommutator a b) := rfl
  rw [hlift] at hmem
  have he : e (QuotientGroup.mk' pi.ker (paperCommutator a b)) =
      pi (paperCommutator a b) := rfl
  have horder : orderOf (e (QuotientGroup.mk' pi.ker (paperCommutator a b))) = 7 := by
    rw [he]
    exact hmem
  exact full_fiber N (hR.to_le hNR) hmin hnon pi.ker hR hF e 7 seven_dvd a b hgen horder t

theorem minimal_nonabelian_lift :
    MinimalNonabelianLift (G 1) (SuzukiSplitGoodSet.orderSet 1 7) := by
  intro A _ _ _ pi _ hpi hR hF N _ hNR hmin hnon Y hY hsub
  exact preimage_good pi hpi hR hF N hNR hmin hnon Y hY hsub

/-- Every finite perfect binary Frattini cover has an actual odd persistent value. -/
theorem hasOddGeneratingGoodSetOver [IsSimpleGroup (G 1)]
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G 1) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A) :
    HasOddGeneratingGoodSetOver pi (SuzukiSplitGoodSet.orderSet 1 7) :=
  BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (G 1)
    (SuzukiSplitGoodSet.orderSet 1 7)
    SuzukiEightCentralBase.centralBase
    minimal_nonabelian_lift pi hpi hR hF

/-- The actual root normalizer contradicts every outer-word order condition. -/
theorem not_productOrderCondition [IsSimpleGroup (G 1)]
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G 1) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 A := by
  intro h
  have hgood := hasOddGeneratingGoodSetOver pi hpi hR hF
  obtain ⟨x, hx, himage, hodd⟩ := hgood.exists_value (OuterWord.derivedWord w.height)
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 A := by
    intro a ha b hb hap hbp
    exact h a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  obtain ⟨u, hu, hc⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime 1 seven_dvd (pi x) himage
  have hne : u ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hu
    exact (Fact.out : Nat.Prime 7).ne_one hu.symm
  exact SuzukiBinaryGoodSetObstruction.false_of_odd_derived_value_torus_image
    1 pi hpi hR w.height hd x hx hodd u hne hc
end Frattini
end Kourovka2135.SuzukiEightBinaryNoncentral

namespace Kourovka2135
open SuzukiTorusMovingRank

/-- No binary least exception has actual quotient Sz(8), whether its soluble
radical is central or noncentral. -/
theorem OrderMinimalException.false_of_binary_suzuki_eight_quotient
    {A : Type} [Group A] [Finite A] {w : OuterWord}
    (h : OrderMinimalException w 2 A)
    (e : (A ⧸ solubleRadical A) ≃* G 1) : False := by
  let : Group.IsPerfect A := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (A ⧸ solubleRadical A) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup (G 1) := e.symm.isSimpleGroup
  let pi := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical A))
  have hpi : Function.Surjective pi :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical A))
  have hker : pi.ker = solubleRadical A :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical A)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical A))
  have hR : IsPGroup 2 pi.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : pi.ker ≤ frattini A := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact SuzukiEightBinaryNoncentral.not_productOrderCondition pi hpi hR hF w h.condition

/-- The actual binary noncentral Suzuki family, including Sz(8). -/
theorem OrderMinimalException.false_of_binary_noncentral_suzuki_quotient
    {A : Type} [Group A] [Finite A] {w : OuterWord}
    (h : OrderMinimalException w 2 A)
    (hnoncentral : ¬ solubleRadical A ≤ Subgroup.center A)
    (m : ℕ) (hm : 1 ≤ m) (e : (A ⧸ solubleRadical A) ≃* G m) : False := by
  by_cases hm1 : m = 1
  · subst m
    exact h.false_of_binary_suzuki_eight_quotient e
  · exact h.false_of_binary_noncentral_large_suzuki_quotient hnoncentral m (by omega) e

end Kourovka2135
