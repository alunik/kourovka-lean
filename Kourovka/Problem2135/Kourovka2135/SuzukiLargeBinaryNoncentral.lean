import Kourovka2135.SuzukiTensorMovingRank
import Kourovka2135.SuzukiIrreducibleClassification
import Kourovka2135.BinaryRepresentationCorrection
import Kourovka2135.PerfectIrreducibleCohomology
import Kourovka2135.CentralMaximalGoodSet
import Kourovka2135.SuzukiSplitGoodSet
import Kourovka2135.SuzukiBinaryGoodSetObstruction
import Kourovka2135.MinimalBinaryCorrectionBound
import Kourovka2135.GeneratingGoodSetFullFiber
import Kourovka2135.MinimalFrattini
import Kourovka2135.SuzukiOddNormalizerBranch

/-! The actual large-Suzuki binary correction bound and its Frattini-cover
application. Tensor classification, scalar extension, cohomology, and moving
ranks are proved inputs, not hypotheses of the least-exception endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Kourovka2135.SuzukiLargeBinaryNoncentral

open SuzukiTorusMovingRank SuzukiTensorNatural SuzukiTensorMovingRank
open scoped TensorProduct PiTensorProduct

private theorem scale_correction (d H R : ℕ) (h : 2 + 2 * H ≤ R) :
    2 * d + 2 * (d * H) ≤ d * R := by nlinarith

section Natural
variable (k : Type) [Field k] [CharP k 2] (m : ℕ) [Algebra (K m) k]

/-- The actual base change of the natural four-space, on its coordinate basis. -/
def naturalLinearEquiv : k ⊗[K m] (Fin 4 → K m) ≃ₗ[k] (Fin 4 → k) :=
  ((Pi.basisFun (K m) (Fin 4)).baseChange k).equiv (Pi.basisFun k (Fin 4)) (Equiv.refl _)

omit [CharP k 2] in
theorem repr_naturalLinearEquiv (x : k ⊗[K m] (Fin 4 → K m)) (a : Fin 4) :
    naturalLinearEquiv k m x a = ((Pi.basisFun (K m) (Fin 4)).baseChange k).repr x a := by
  change (Pi.basisFun k (Fin 4)).repr (naturalLinearEquiv k m x) a = _
  simp [naturalLinearEquiv, Module.Basis.equiv]

def naturalBaseChangeEquiv :
    (RepresentationDensityBaseChange.baseChange k (natural m)).Equiv
      (naturalTwist k m (algebraMap (K m) k) 0) := by
  refine Representation.Equiv.mk (naturalLinearEquiv k m) ?_
  intro g
  apply ((Pi.basisFun (K m) (Fin 4)).baseChange k).ext
  intro a
  change naturalLinearEquiv k m
      (RepresentationDensityBaseChange.baseChange k (natural m) g
        (((Pi.basisFun (K m) (Fin 4)).baseChange k) a)) =
    naturalTwist k m (algebraMap (K m) k) 0 g
      (naturalLinearEquiv k m (((Pi.basisFun (K m) (Fin 4)).baseChange k) a))
  rw [show naturalLinearEquiv k m (((Pi.basisFun (K m) (Fin 4)).baseChange k) a) =
      Pi.basisFun k (Fin 4) a by
    simp only [naturalLinearEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]]
  rw [Module.Basis.baseChange_apply, RepresentationDensityBaseChange.baseChange_apply,
    LinearMap.baseChange_tmul]
  ext b
  rw [repr_naturalLinearEquiv, Module.Basis.baseChange_repr_tmul]
  simp [natural_apply, naturalTwist_apply, matrixHom, Pi.basisFun_apply,
    Pi.single_apply, Algebra.smul_def]

omit [Algebra (K m) k] in
theorem naturalTwist_H1_le_one (σ : K m →+* k) (n : ℕ) (hm : 2 ≤ m) :
    Module.finrank k (groupCohomology (Rep.of (naturalTwist k m σ n)) 1) ≤ 1 := by
  let τ := twistEmbedding k m σ n
  let : Algebra (K m) k := τ.toAlgebra
  have he : naturalTwist k m τ 0 = naturalTwist k m σ n := by
    ext g v j
    simp [naturalTwist_apply, τ]
  rw [← he]
  change Module.finrank k (groupCohomology
    (Rep.of (naturalTwist k m (algebraMap (K m) k) 0)) 1) ≤ 1
  rw [← RepresentationCohomologyAlternative.finrank_cohomology_eq _ _
    (naturalBaseChangeEquiv k m) 1]
  rw [GroupCohomologyFieldExtension.finrank_H1_baseChange]
  exact SuzukiNaturalH1.finrank_H1_le_one m hm
end Natural

section Singleton
variable (k : Type) [Field k] [CharP k 2] (m : ℕ) (σ : K m →+* k)

def singletonEquiv (i : Fin (2 * m + 1)) :
    (representation k m {i} σ).Equiv (naturalTwist k m σ i.val) := by
  let i₀ : ({i} : Finset (Fin (2 * m + 1))) := ⟨i, Finset.mem_singleton_self i⟩
  refine Representation.Equiv.mk (PiTensorProduct.subsingletonEquiv i₀) ?_
  intro g
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change PiTensorProduct.subsingletonEquiv i₀
      (representation k m {i} σ g (PiTensorProduct.tprod k x)) =
    naturalTwist k m σ i.val g
      (PiTensorProduct.subsingletonEquiv i₀ (PiTensorProduct.tprod k x))
  rw [representation_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

theorem singleton_H1_le_one (i : Fin (2 * m + 1)) (hm : 2 ≤ m) :
    Module.finrank k (groupCohomology (Rep.of (representation k m {i} σ)) 1) ≤ 1 := by
  rw [RepresentationCohomologyAlternative.finrank_cohomology_eq _ _
    (singletonEquiv k m σ i) 1]
  exact naturalTwist_H1_le_one k m σ i.val hm

theorem naturalTwist_moving_eq_four (n : ℕ) (u : (K m)ˣ) (hu : u ≠ 1) :
    Module.finrank k (naturalTwist k m σ n (torusHom m u) - LinearMap.id).range = 4 := by
  have hk : (naturalTwist k m σ n (torusHom m u) - LinearMap.id).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he : naturalTwist k m σ n (torusHom m u) v = v := sub_eq_zero.mp hv
    funext j
    have hh := congrFun he j
    have hdiag : naturalTwist k m σ n (torusHom m u) v j =
        factorWeight k m σ u n j * v j := by
      fin_cases j <;> simp [naturalTwist_apply, matrixHom, torusHom,
        BenderSuzuki.MatrixGroups.SuzukiTorusGL,
        BenderSuzuki.MatrixGroups.SuzukiTorusMatrix,
        Fin.sum_univ_four, factorWeight, torusWeights]
    rw [hdiag] at hh
    have hz : (factorWeight k m σ u n j - 1) * v j = 0 := by
      simpa only [sub_mul, one_mul] using sub_eq_zero.mpr hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (factorWeight_ne_one k m σ u hu n j))
  have hr := (naturalTwist k m σ n (torusHom m u) - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hr
  simpa using hr

/-- Every actual model satisfies the numerical correction alternative. -/
theorem tensor_alternative [Group.IsPerfect (G m)] (I : Finset (Fin (2 * m + 1)))
    (hm : 2 ≤ m) (u : (K m)ˣ) (hu : u ≠ 1) :
    Module.finrank k (groupCohomology (Rep.of (representation k m I σ)) 1) = 0 ∨
      2 + 2 * Module.finrank k (groupCohomology (Rep.of (representation k m I σ)) 1) ≤
        Module.finrank k (representation k m I σ (torusHom m u) - LinearMap.id).range := by
  by_cases h0 : I.card = 0
  · have hI : I = ∅ := Finset.card_eq_zero.mp h0
    subst I
    left
    let : Subsingleton (groupCohomology (Rep.of (representation k m ∅ σ)) 1) :=
      PerfectIrreducibleCohomology.subsingleton_H1_of_trivial _
        (SuzukiIrreducibleClassification.emptyRepresentation k m σ)
    exact Module.finrank_zero_of_subsingleton
  by_cases h1 : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    right
    have hH := singleton_H1_le_one k m σ i hm
    have he := RepresentationMovingConjugacy.finrank_moving_eq_of_equiv
      (representation k m {i} σ) (naturalTwist k m σ i.val) (singletonEquiv k m σ i)
      (torusHom m u)
    rw [naturalTwist_moving_eq_four k m σ i.val u hu] at he
    omega
  · exact Or.inr (tensor_correction_inequality k m σ u I hu hm (by omega))
end Singleton

section Descent
variable (m : ℕ) [Group.IsPerfect (G m)]
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (ρ : Representation (ZMod 2) (G m) V) [ρ.IsIrreducible]

open IrreducibleEndCohomology MinimalEndMovingRank

def parameterEmbedding : K m →+* ClosedField ρ := by
  let : Algebra (ZMod 2) (K m) := ZMod.algebra (K m) 2
  let : Algebra (ZMod 2) (ClosedField ρ) := ZMod.algebra (ClosedField ρ) 2
  exact (IsAlgClosed.lift : K m →ₐ[ZMod 2] ClosedField ρ).toRingHom

theorem binary_bound_torus (hm : 2 ≤ m) (u : (K m)ˣ) (hu : u ≠ 1)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) :
    BinaryRepresentationCorrection.Bound ρ (torusHom m u) := by
  obtain ⟨I, ⟨e⟩⟩ := SuzukiIrreducibleClassification.exists_tensor_equiv
    (ClosedField ρ) m (parameterEmbedding m ρ) (extended ρ)
  have ha := tensor_alternative (ClosedField ρ) m (parameterEmbedding m ρ) I hm u hu
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

theorem binary_bound_split_prime (hm : 2 ≤ m) (r : ℕ) [Fact r.Prime]
    (hr : r ∣ SuzukiGeometry.q m - 1) (g : G m) (hg : orderOf g = r)
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) :
    BinaryRepresentationCorrection.Bound ρ g := by
  obtain ⟨u, hu, hc⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime m hr g hg
  have hne : u ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hu
    exact (Fact.out : r.Prime).ne_one hu.symm
  rcases binary_bound_torus m ρ hm u hne hdual with hz | hmoving
  · exact Or.inl hz
  · right
    rwa [RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hc] at hmoving
end Descent

section Fiber
open scoped IsMulCommutative
variable (m : ℕ) (hm : 2 ≤ m)
variable {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
variable (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup A, L.Normal → L < N → L ≤ Subgroup.center A)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup A) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini A)
variable [IsSimpleGroup (A ⧸ R)] (e : (A ⧸ R) ≃* G m)

include hm hN hmin hnonabelian hR hRΦ e in
theorem full_fiber (r : ℕ) [Fact r.Prime] (hr : r ∣ SuzukiGeometry.q m - 1)
    (a b : A) (hgen : Subgroup.closure ({a, b} : Set A) = ⊤)
    (hc : orderOf (e (QuotientGroup.mk' R (paperCommutator a b))) = r) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsPerfect (G m) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let τ : Representation (ZMod 2) (G m) (Additive (N ⧸ Subgroup.center N)) :=
    ρ.comp e.symm.toMonoidHom
  let : τ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e.symm
  have hd := BinaryRepresentationCorrection.dual_finrank_eq_of_comp ρ e.symm
    (minimalCenterDualCohomology_finrank_eq N hN hmin R hR hnonabelian 1)
  have hs := binary_bound_split_prime m τ hm r hr
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
variable (m : ℕ) (hm : 2 ≤ m) (r : ℕ) [Fact r.Prime]
variable (hr : r ∣ SuzukiGeometry.q m - 1)

include hm hr in
theorem preimage_good
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G m) [IsSimpleGroup (A ⧸ pi.ker)]
    (hpi : Function.Surjective pi) (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A)
    (N : Subgroup A) [N.Normal] (hNR : N ≤ pi.ker)
    (hmin : ∀ L : Subgroup A, L.Normal → L < N → L ≤ Subgroup.center A)
    (hnon : ¬ IsMulCommutative N) (Y : Set (A ⧸ N)) (hY : IsGeneratingGoodSet Y)
    (hsub : Y ⊆ (QuotientGroup.lift N pi hNR) ⁻¹' SuzukiSplitGoodSet.orderSet m r) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  refine IsGeneratingGoodSet.preimage_quotient_of_full_fiber
    (G := A) N (hNR.trans hF) hY ?_
  intro a b hgen hc t
  let e : (A ⧸ pi.ker) ≃* G m := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have hmem := hsub hc
  change orderOf ((QuotientGroup.lift N pi hNR)
    (QuotientGroup.mk' N (paperCommutator a b))) = r at hmem
  have hlift : (QuotientGroup.lift N pi hNR)
      (QuotientGroup.mk' N (paperCommutator a b)) = pi (paperCommutator a b) := rfl
  rw [hlift] at hmem
  have he : e (QuotientGroup.mk' pi.ker (paperCommutator a b)) =
      pi (paperCommutator a b) := rfl
  have horder : orderOf (e (QuotientGroup.mk' pi.ker (paperCommutator a b))) = r := by
    rw [he]
    exact hmem
  exact full_fiber m hm N (hR.to_le hNR) hmin hnon pi.ker hR hF e r hr a b hgen horder t

include hm hr in
theorem minimal_nonabelian_lift :
    MinimalNonabelianLift (G m) (SuzukiSplitGoodSet.orderSet m r) := by
  intro A _ _ _ pi _ hpi hR hF N _ hNR hmin hnon Y hY hsub
  exact preimage_good m hm r hr pi hpi hR hF N hNR hmin hnon Y hY hsub

include hr in
omit [Fact r.Prime] in
theorem odd_prime : Odd r := SuzukiSplitSylow.split_prime_odd m hr

include hr in
theorem base_good
    (hsolv : ∀ H : Subgroup (G m), H < ⊤ → Group.IsSolvable H) :
    HasOddGeneratingGoodSetOver (MonoidHom.id (G m)) (SuzukiSplitGoodSet.orderSet m r) := by
  have hdiv : r ∣ Nat.card (K m)ˣ := by
    rw [Nat.card_units, card_field]
    exact hr
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (K m)ˣ) r hdiv
  refine ⟨SuzukiSplitGoodSet.orderSet m r,
    SuzukiSplitGoodSet.isGeneratingGoodSet m hr hsolv, fun _ h => h,
    torusHom m u, ?_, ?_⟩
  · exact (orderOf_torus m u).trans hu
  · rw [orderOf_torus, hu]
    exact odd_prime m r hr

include hm hr in
/-- Every finite perfect binary Frattini cover has an actual odd persistent value. -/
theorem hasOddGeneratingGoodSetOver [IsSimpleGroup (G m)]
    (hsolv : ∀ H : Subgroup (G m), H < ⊤ → Group.IsSolvable H)
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G m) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A) :
    HasOddGeneratingGoodSetOver pi (SuzukiSplitGoodSet.orderSet m r) :=
  BinaryFrattiniFullFiberInduction.hasOddGeneratingGoodSetOver (G m)
    (SuzukiSplitGoodSet.orderSet m r)
    (CentralMaximalGoodSet.suzuki_large m hm _ (base_good m r hr hsolv))
    (minimal_nonabelian_lift m hm r hr) pi hpi hR hF

include hm hr in
/-- The actual root normalizer contradicts every outer-word order condition. -/
theorem not_productOrderCondition [IsSimpleGroup (G m)]
    (hsolv : ∀ H : Subgroup (G m), H < ⊤ → Group.IsSolvable H)
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (pi : A →* G m) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini A) (w : OuterWord) :
    ¬ ProductOrderCondition w 2 A := by
  intro h
  have hgood := hasOddGeneratingGoodSetOver m hm r hr hsolv pi hpi hR hF
  obtain ⟨x, hx, himage, hodd⟩ := hgood.exists_value (OuterWord.derivedWord w.height)
  have hd : ProductOrderCondition (OuterWord.derivedWord w.height) 2 A := by
    intro a ha b hb hap hbp
    exact h a (w.derivedWord_values_subset w.height le_rfl ha)
      b (w.derivedWord_values_subset w.height le_rfl hb) hap hbp
  obtain ⟨u, hu, hc⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime m hr (pi x) himage
  have hne : u ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hu
    exact (Fact.out : r.Prime).ne_one hu.symm
  exact SuzukiBinaryGoodSetObstruction.false_of_odd_derived_value_torus_image
    m pi hpi hR w.height hd x hx hodd u hne hc
end Frattini
end Kourovka2135.SuzukiLargeBinaryNoncentral

namespace Kourovka2135
open SuzukiTorusMovingRank

/-- The large-Suzuki binary noncentral least-exception branch is impossible. -/
theorem OrderMinimalException.false_of_binary_noncentral_large_suzuki_quotient
    {A : Type} [Group A] [Finite A] {w : OuterWord}
    (h : OrderMinimalException w 2 A)
    (hnoncentral : ¬ solubleRadical A ≤ Subgroup.center A)
    (m : ℕ) (hm : 2 ≤ m) (e : (A ⧸ solubleRadical A) ≃* G m) : False := by
  let : Group.IsPerfect A := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (A ⧸ solubleRadical A) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup (G m) := e.symm.isSimpleGroup
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable Nat.prime_two hnoncentral)
  obtain ⟨r, hr, hrd⟩ := SuzukiOddNormalizerBranch.exists_split_prime m (by omega)
  let : Fact r.Prime := ⟨hr⟩
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
  exact SuzukiLargeBinaryNoncentral.not_productOrderCondition m hm r hrd hsolv
    pi hpi hR hF w h.condition

end Kourovka2135
