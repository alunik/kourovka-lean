import Kourovka2135.OddPSLTwoProjectiveChart
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Complement

/-!
# An actual nonsplit torus and reflection in odd PSL₂

Selective adaptation of Qiuzhen-CFSG/CFSG, Apache-2.0,
commit `96b2a02085dc678f3e0a97b334c31ada599c55fd`,
`Glauberman/DicksonNonsplitTorus.lean`, lines 130–713.
Upstream SHA256: `3279e7052c20e2bffce05177f82bb297b3ecc7e3b67002678f9ee38661540e65`.
See `Vendor/CFSG/LICENSE`. Only the explicit quadratic-extension, norm,
and Frobenius construction is retained. No classification theorem is imported.
The odd-characteristic root count replaces the upstream prime-power/gcd prelude.
-/

set_option autoImplicit false

noncomputable section

namespace Kourovka2135.OddPSLTwoNonsplitNormTorus

open OddPSLTwoProjectiveChart
open scoped Pointwise LinearAlgebra.Projectivization

universe u

/-- The norm-one torus in the genuine quadratic field extension, together with
its determinant-corrected Frobenius reflection in the actual projective group. -/
theorem norm_torus_reflection_data
    (F : Type u) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) :
    ∃ T : Subgroup (Q F), ∃ w : Q F,
      IsCyclic T ∧ Nat.card T = (Nat.card F + 1) / 2 ∧
      Nat.card T * 2 = Nat.card F + 1 ∧
      w ∈ Subgroup.normalizer (T : Set (Q F)) ∧ w ∉ T ∧
      w * w = 1 ∧
      (∀ t : Q F, t ∈ T → w * t * w⁻¹ = t⁻¹) ∧
      Nat.card (T ⊔ Subgroup.zpowers w : Subgroup (Q F)) = 2 * Nat.card T := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hcard_roots : Nat.card (rootsOfUnity 2 F) = 2 :=
    (IsPrimitiveRoot.neg_one p hp2).card_rootsOfUnity
  have hreflection_candidate_data
      (T : Subgroup (Q F)) (w : Q F)
      (hw_normalizer : w ∈ Subgroup.normalizer (T : Set _))
      (hw_sq : w * w = 1) (hw_not_mem : w ∉ T) :
      Nat.card (Subgroup.zpowers w) = 2 ∧
        Disjoint T (Subgroup.zpowers w) ∧
        Nat.card (T ⊔ (Subgroup.zpowers w : Subgroup (Q F)) : Subgroup (Q F)) = 2 * Nat.card T := by
    let Z : Subgroup (Q F) := Subgroup.zpowers w
    have hw_ne_one : w ≠ 1 := by
      intro hw_one
      apply hw_not_mem
      rw [hw_one]
      exact Subgroup.one_mem T
    have hw_zpowers_card : Nat.card Z = 2 := by
      change Nat.card (Subgroup.zpowers w) = 2
      rw [Nat.card_zpowers]
      have hw_pow : w ^ 2 = 1 := by
        simpa [pow_two] using hw_sq
      have hord_dvd : orderOf w ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hw_pow
      rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
      · exact False.elim (hw_ne_one (orderOf_eq_one_iff.mp hord))
      · exact hord
    have hdisjoint : Disjoint T Z := by
      let R : Subgroup Z := T.comap Z.subtype
      let : Fact (Nat.card Z).Prime := ⟨by
        rw [show Nat.card Z = 2 by exact hw_zpowers_card]
        exact Nat.prime_two⟩
      rcases R.eq_bot_or_eq_top_of_prime_card with hR | hR
      · rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have hxR : (⟨x, hx.2⟩ : Z) ∈ R := hx.1
        rw [hR] at hxR
        have hxone : (⟨x, hx.2⟩ : Z) = 1 := by simpa using hxR
        exact congrArg Subtype.val hxone
      · exfalso
        apply hw_not_mem
        have hwR : (⟨w, Subgroup.mem_zpowers w⟩ : Z) ∈ R := by
          rw [hR]
          simp
        exact hwR
    let D : Subgroup (Q F) := T ⊔ Z
    have hD_le_normalizer : D ≤ Subgroup.normalizer (T : Set _) := by
      apply sup_le Subgroup.le_normalizer
      exact Subgroup.zpowers_le.2 hw_normalizer
    let TD : Subgroup D := T.subgroupOf D
    let ZD : Subgroup D := Z.subgroupOf D
    let : TD.Normal := by
      change (T.subgroupOf D).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer hD_le_normalizer
    have hTDZD : Disjoint TD ZD := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxAmbient : (x : Q F) ∈ T ⊓ Z := by
        change (x : Q F) ∈ T ∧ (x : Q F) ∈ Z
        exact ⟨hx.1, hx.2⟩
      have hxone : (x : Q F) = 1 := by
        rw [hdisjoint.eq_bot] at hxAmbient
        simpa using hxAmbient
      apply Subtype.ext
      exact hxone
    have hsup : TD ⊔ ZD = ⊤ := by
      change T.subgroupOf D ⊔ Z.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup (show T ≤ D from le_sup_left)
        (show Z ≤ D from le_sup_right)]
      exact Subgroup.subgroupOf_self D
    have hZD_le_normalizer : ZD ≤ Subgroup.normalizer (TD : Set D) := by
      rw [Subgroup.normalizer_eq_top TD]
      exact le_top
    have hmul : (ZD : Set D) * (TD : Set D) = Set.univ := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right ZD TD
        hZD_le_normalizer, sup_comm, hsup]
      rfl
    have hcomp : ZD.IsComplement' TD :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hTDZD.symm hmul
    have hZDcard : Nat.card ZD = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ D from le_sup_right)).toEquiv
    have hTDcard : Nat.card TD = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
    refine ⟨hw_zpowers_card, hdisjoint, ?_⟩
    calc
      Nat.card (T ⊔ Z : Subgroup (Q F)) = Nat.card D := rfl
      _ = Nat.card ZD * Nat.card TD := hcomp.card_mul_card.symm
      _ = 2 * Nat.card T := by
        rw [hZDcard, hTDcard, hw_zpowers_card]
  let E := FiniteField.Extension F p 2
  let : Fintype E := Fintype.ofFinite E
  let normUnits : Eˣ →* Fˣ := Units.map (Algebra.norm F)
  let K : Subgroup Eˣ := normUnits.ker
  have hnormUnits_surjective : Function.Surjective normUnits := by
    exact FiniteField.unitsMap_norm_surjective F E
  have hnormUnits_range : normUnits.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hnormUnits_surjective
  have hK_index : K.index = Nat.card F - 1 := by
    calc
      K.index = Nat.card normUnits.range := Subgroup.index_ker normUnits
      _ = Nat.card Fˣ := by rw [hnormUnits_range]; simp
      _ = Nat.card F - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := F))
  have hE_card : Nat.card E = Nat.card F ^ 2 := by
    exact FiniteField.natCard_extension F p 2
  have hK_mul_card :
      (Nat.card F - 1) * Nat.card K = Nat.card F ^ 2 - 1 := by
    calc
      (Nat.card F - 1) * Nat.card K = K.index * Nat.card K := by rw [hK_index]
      _ = Nat.card Eˣ := K.index_mul_card
      _ = Nat.card E - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Fintype.card_units (α := E))
      _ = Nat.card F ^ 2 - 1 := by rw [hE_card]
  have hq_factor :
      (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa [mul_comm] using
      (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have hdegree_exp :
      (Nat.card E - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [hE_card, ← hq_factor]
    simpa [mul_comm] using Nat.mul_div_left (Nat.card F + 1)
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
  have hfrob_inv (x : K) :
      FiniteField.Extension.frob F p 2 (x.1 : E) = ((x.1 : E)⁻¹) := by
    have hxker := x.property
    change normUnits x.1 = 1 at hxker
    have hxnorm := congrArg Units.val hxker
    change Algebra.norm F (x.1 : E) = 1 at hxnorm
    have hpow : (x.1 : E) ^ (Nat.card F + 1) = 1 := by
      have h := FiniteField.algebraMap_norm_eq_pow
        (K := F) (K' := E) (x := (x.1 : E))
      rw [hxnorm, map_one, hdegree_exp] at h
      exact h.symm
    rw [FiniteField.Extension.frob_apply]
    apply mul_right_cancel₀ (x.1.ne_zero)
    calc
      (x.1 : E) ^ Nat.card F * (x.1 : E) =
          (x.1 : E) ^ (Nat.card F + 1) := (pow_succ _ _).symm
      _ = 1 := hpow
      _ = (x.1 : E)⁻¹ * (x.1 : E) := by
        rw [inv_mul_cancel₀ x.1.ne_zero]
  have hK_card : Nat.card K = Nat.card F + 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := F)))
    exact hK_mul_card.trans hq_factor.symm
  have hK_cyclic : IsCyclic K := isCyclic_subgroup_units K
  have hidx :
      Fintype.card (Module.Free.ChooseBasisIndex F E) =
        Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Fintype.card_fin]
    simpa [E] using (FiniteField.finrank_extension F p 2)
  let eidx : Module.Free.ChooseBasisIndex F E ≃ Fin 2 :=
    Fintype.equivOfCardEq hidx
  let b : Module.Basis (Fin 2) F E :=
    (Module.Free.chooseBasis F E).reindex eidx
  let nonsplitSL : K →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun x =>
        ⟨Algebra.leftMulMatrix b (x.1 : E), by
          rw [← Algebra.norm_eq_matrix_det b]
          have hxker := x.property
          change normUnits x.1 = 1 at hxker
          simpa [normUnits] using congrArg Units.val hxker⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (Algebra.leftMulMatrix b) ((x.1 : E) * (y.1 : E)) =
          (Algebra.leftMulMatrix b) (x.1 : E) * (Algebra.leftMulMatrix b) (y.1 : E)
        exact (Algebra.leftMulMatrix b).map_mul _ _ }
  let nonsplitTorus : K →* Q F :=
    (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        nonsplitSL
  have hnonsplit_mem_ker_iff (x : K) :
      x ∈ nonsplitTorus.ker ↔
        ∃ r : F, r ^ 2 = 1 ∧ algebraMap F E r = (x.1 : E) := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hcenter : nonsplitSL x ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
        (QuotientGroup.eq_one_iff (nonsplitSL x)).mp hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hcenter
      rcases hcenter with ⟨r, hr, hscalar⟩
      refine ⟨r, by simpa using hr, ?_⟩
      apply Algebra.leftMulMatrix_injective b
      calc
        Algebra.leftMulMatrix b (algebraMap F E r) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r :=
          (Algebra.leftMulMatrix b).commutes r
        _ = Matrix.scalar (Fin 2) r := rfl
        _ = (nonsplitSL x : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
        _ = Algebra.leftMulMatrix b (x.1 : E) := rfl
    · rintro ⟨r, hr, hxr⟩
      apply (QuotientGroup.eq_one_iff (nonsplitSL x)).mpr
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨r, by simpa using hr, ?_⟩
      change Matrix.scalar (Fin 2) r = Algebra.leftMulMatrix b (x.1 : E)
      rw [← hxr]
      calc
        Matrix.scalar (Fin 2) r =
            algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = Algebra.leftMulMatrix b (algebraMap F E r) :=
          ((Algebra.leftMulMatrix b).commutes r).symm
  let RootF := {r : F // r ^ 2 = 1}
  let kerScalar (x : nonsplitTorus.ker) : F :=
    Classical.choose ((hnonsplit_mem_ker_iff x.1).mp x.property)
  have hkerScalar_spec (x : nonsplitTorus.ker) :
      kerScalar x ^ 2 = 1 ∧
        algebraMap F E (kerScalar x) = (x.1.1 : E) :=
    Classical.choose_spec ((hnonsplit_mem_ker_iff x.1).mp x.property)
  let scalarK (r : RootF) : K :=
    ⟨Units.map (algebraMap F E)
        (Units.mk0 r.1 (by
          intro hr0
          have hr := r.property
          simp [hr0] at hr)), by
      change normUnits
        (Units.map (algebraMap F E)
          (Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr))) = 1
      apply Units.ext
      change Algebra.norm F (algebraMap F E r.1) = 1
      rw [Algebra.norm_algebraMap_of_basis b]
      simpa using r.property⟩
  let scalarKer (r : RootF) : nonsplitTorus.ker :=
    ⟨scalarK r, (hnonsplit_mem_ker_iff (scalarK r)).mpr
      ⟨r.1, r.property, by simp [scalarK]⟩⟩
  let eKerRoot : nonsplitTorus.ker ≃ RootF :=
    { toFun := fun x => ⟨kerScalar x, (hkerScalar_spec x).1⟩
      invFun := scalarKer
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        simpa [scalarKer, scalarK] using (hkerScalar_spec x).2
      right_inv := by
        intro r
        apply Subtype.ext
        apply (algebraMap F E).injective
        calc
          algebraMap F E (kerScalar (scalarKer r)) =
              ((scalarKer r).1.1 : E) :=
            (hkerScalar_spec (scalarKer r)).2
          _ = algebraMap F E r.1 := by simp [scalarKer, scalarK] }
  let rootVal : rootsOfUnity 2 F ≃ RootF :=
    { toFun := fun a =>
        ⟨(a.1 : F), by simpa using congrArg Units.val a.property⟩
      invFun := fun r =>
        ⟨Units.mk0 r.1 (by
            intro hr0
            have hr := r.property
            simp [hr0] at hr),
          by
            rw [mem_rootsOfUnity]
            apply Units.ext
            simpa using r.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Units.ext
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }
  have hnonsplit_ker_card :
      Nat.card nonsplitTorus.ker =
        2 := by
    calc
      Nat.card nonsplitTorus.ker = Nat.card RootF :=
        Nat.card_congr eKerRoot
      _ = Nat.card (rootsOfUnity 2 F) :=
        (Nat.card_congr rootVal).symm
      _ = 2 := hcard_roots
  have hnonsplit_range_mul :
      Nat.card nonsplitTorus.range * 2 =
        Nat.card F + 1 := by
    calc
      Nat.card nonsplitTorus.range * 2 =
          nonsplitTorus.ker.index * Nat.card nonsplitTorus.ker := by
        rw [Subgroup.index_ker, hnonsplit_ker_card]
      _ = Nat.card K := nonsplitTorus.ker.index_mul_card
      _ = Nat.card F + 1 := hK_card
  have hnonsplit_range_card :
      Nat.card nonsplitTorus.range =
        (Nat.card F + 1) / 2 := by
    apply Nat.eq_div_of_mul_eq_left
    · rw [← hcard_roots]
      exact Nat.ne_of_gt Nat.card_pos
    · exact hnonsplit_range_mul
  have hnonsplitTorus_cyclic : IsCyclic nonsplitTorus.range := by
    let : IsCyclic K := hK_cyclic
    exact isCyclic_of_surjective nonsplitTorus.rangeRestrict
      nonsplitTorus.rangeRestrict_surjective
  let sigma : E ≃ₐ[F] E :=
    FiniteField.Extension.frob F p 2
  have hsigma_sq (x : E) : sigma (sigma x) = x := by
    change FiniteField.Extension.frob F p 2
      (FiniteField.Extension.frob F p 2 x) = x
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply,
      ← pow_mul]
    have hcard : Nat.card F * Nat.card F = Fintype.card E := by
      rw [← pow_two, ← FiniteField.natCard_extension F p 2,
        Nat.card_eq_fintype_card]
    rw [hcard]
    exact FiniteField.pow_card x
  have hsigma_ne_one : sigma ≠ 1 := by
    intro hsigma
    change FiniteField.Extension.frob F p 2 = 1 at hsigma
    have hall : ∀ g : E ≃ₐ[F] E, g = 1 := by
      intro g
      obtain ⟨i, hi, hpow⟩ :=
        FiniteField.Extension.exists_frob_pow_eq
          (k := F) (p := p) (n := 2) g
      rw [← hpow, hsigma, one_pow]
    let : Subsingleton (E ≃ₐ[F] E) :=
      ⟨fun a d => (hall a).trans (hall d).symm⟩
    have hone : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_unique
    have htwo : Nat.card (E ≃ₐ[F] E) = 2 :=
      FiniteField.natCard_algEquiv_extension F p 2
    omega
  let sigmaMat : Matrix (Fin 2) (Fin 2) F :=
    LinearMap.toMatrix b b sigma.toLinearEquiv
  have hsigma_inv (x : K) :
      sigma (x.1 : E) = ((x⁻¹ : K).1 : E) := by
    rw [show sigma = FiniteField.Extension.frob F p 2 from rfl,
      hfrob_inv x]
    simp
  have hsigmaMat_mul (x : E) :
      sigmaMat * Algebra.leftMulMatrix b x =
        Algebra.leftMulMatrix b (sigma x) * sigmaMat := by
    dsimp [sigmaMat]
    rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
      ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext y
    simp [LinearMap.comp_apply, Algebra.lmul]
  have hsigmaMat_sq : sigmaMat * sigmaMat = 1 := by
    dsimp [sigmaMat]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b,
      (LinearMap.toMatrix b b).injective.eq_iff]
    ext x
    exact hsigma_sq x
  have hsigma_det_unit : IsUnit (Matrix.det sigmaMat) := by
    simpa [sigmaMat] using
      (LinearEquiv.isUnit_det sigma.toLinearEquiv b b)
  have hsigma_det_ne : Matrix.det sigmaMat ≠ 0 :=
    hsigma_det_unit.ne_zero
  obtain ⟨c, hc⟩ :=
    FiniteField.norm_surjective F E (Matrix.det sigmaMat)⁻¹
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst c
    simp only [Algebra.norm_zero] at hc
    exact hsigma_det_ne (inv_eq_zero.mp hc.symm)
  let frobSL : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨Algebra.leftMulMatrix b c * sigmaMat, by
      rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b, hc]
      exact inv_mul_cancel₀ hsigma_det_ne⟩
  have hc_sigma :
      c * sigma c = algebraMap F E (Algebra.norm F c) := by
    have h := FiniteField.algebraMap_norm_eq_pow
      (K := F) (K' := E) (x := c)
    rw [hdegree_exp] at h
    calc
      c * sigma c = c * c ^ Nat.card F := by
        change c * FiniteField.Extension.frob F p 2 c = _
        rw [FiniteField.Extension.frob_apply]
      _ = c ^ (Nat.card F + 1) := by rw [pow_succ, mul_comm]
      _ = algebraMap F E (Algebra.norm F c) := h.symm
  have hfrobSL_sq_matrix :
      ((frobSL * frobSL : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        Algebra.leftMulMatrix b
          (algebraMap F E (Algebra.norm F c)) := by
    change (Algebra.leftMulMatrix b c * sigmaMat) *
        (Algebra.leftMulMatrix b c * sigmaMat) =
      Algebra.leftMulMatrix b
        (algebraMap F E (Algebra.norm F c))
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          (Algebra.leftMulMatrix b c * sigmaMat) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b c) * sigmaMat := by
              simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma c) * sigmaMat) *
              sigmaMat := by rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma c)) *
              (sigmaMat * sigmaMat) := by
                simp only [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b (c * sigma c) := by
            rw [hsigmaMat_sq, mul_one, ← map_mul]
      _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) := by rw [hc_sigma]
  have hfrobSL_sq_center :
      frobSL * frobSL ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨Algebra.norm F c, ?_, ?_⟩
    · have hdet := (frobSL * frobSL).property
      rw [hfrobSL_sq_matrix] at hdet
      have hscalar :
          Algebra.leftMulMatrix b
              (algebraMap F E (Algebra.norm F c)) =
            Matrix.scalar (Fin 2) (Algebra.norm F c) := by
        calc
          _ = algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) :=
            (Algebra.leftMulMatrix b).commutes (Algebra.norm F c)
          _ = _ := rfl
      rw [hscalar] at hdet
      simpa [Matrix.det_fin_two, pow_two] using hdet
    · calc
        Matrix.scalar (Fin 2) (Algebra.norm F c) =
            algebraMap F (Matrix (Fin 2) (Fin 2) F)
              (Algebra.norm F c) := rfl
        _ = Algebra.leftMulMatrix b
            (algebraMap F E (Algebra.norm F c)) :=
          ((Algebra.leftMulMatrix b).commutes (Algebra.norm F c)).symm
        _ = ((frobSL * frobSL :
            Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := hfrobSL_sq_matrix.symm
  have hleftMul_comm (a d : E) :
      Algebra.leftMulMatrix b a * Algebra.leftMulMatrix b d =
        Algebra.leftMulMatrix b d * Algebra.leftMulMatrix b a := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hfrobSL_mul (x : K) :
      frobSL * nonsplitSL x = nonsplitSL x⁻¹ * frobSL := by
    apply Subtype.ext
    change (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
        Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
          (Algebra.leftMulMatrix b c * sigmaMat)
    calc
      (Algebra.leftMulMatrix b c * sigmaMat) *
          Algebra.leftMulMatrix b (x.1 : E) =
          Algebra.leftMulMatrix b c *
            (sigmaMat * Algebra.leftMulMatrix b (x.1 : E)) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b c *
            (Algebra.leftMulMatrix b (sigma (x.1 : E)) * sigmaMat) := by
              rw [hsigmaMat_mul]
      _ = (Algebra.leftMulMatrix b c *
            Algebra.leftMulMatrix b (sigma (x.1 : E))) * sigmaMat := by
              rw [Matrix.mul_assoc]
      _ = (Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            Algebra.leftMulMatrix b c) * sigmaMat := by
              rw [hleftMul_comm]
      _ = Algebra.leftMulMatrix b (sigma (x.1 : E)) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [Matrix.mul_assoc]
      _ = Algebra.leftMulMatrix b ((x⁻¹ : K).1 : E) *
            (Algebra.leftMulMatrix b c * sigmaMat) := by
              rw [hsigma_inv]
  have hfrobSL_conj (x : K) :
      frobSL * nonsplitSL x * frobSL⁻¹ = nonsplitSL x⁻¹ := by
    calc
      frobSL * nonsplitSL x * frobSL⁻¹ =
          nonsplitSL x⁻¹ * (frobSL * frobSL⁻¹) := by
        rw [hfrobSL_mul, mul_assoc]
      _ = nonsplitSL x⁻¹ := by rw [mul_inv_cancel, mul_one]
  let frobPSL : Q F :=
    QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL
  have hfrobPSL_sq : frobPSL ^ 2 = 1 := by
    change (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) frobSL) ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (frobSL ^ 2)).mpr
    simpa [pow_two] using hfrobSL_sq_center
  have hfrobPSL_not_mem_torus :
      frobPSL ∉ nonsplitTorus.range := by
    rintro ⟨x, hx⟩
    change (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          (nonsplitSL x) =
      (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
          frobSL at hx
    rcases (QuotientGroup.mk'_eq_mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).mp hx with
      ⟨z, hz_center, hz_eq⟩
    have hscalar :=
      Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center
        hz_center (0 : Fin 2)
    let r : F := (z : Matrix (Fin 2) (Fin 2) F) 0 0
    have hscalar' :
        Matrix.scalar (Fin 2) r =
          (z : Matrix.SpecialLinearGroup (Fin 2) F) := hscalar
    have hmat := congrArg Subtype.val hz_eq
    change Algebra.leftMulMatrix b (x.1 : E) *
        (z : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix b c * sigmaMat at hmat
    rw [← hscalar'] at hmat
    have hscalarLM :
        Matrix.scalar (Fin 2) r =
          Algebra.leftMulMatrix b (algebraMap F E r) := by
      calc
        _ = algebraMap F (Matrix (Fin 2) (Fin 2) F) r := rfl
        _ = _ := ((Algebra.leftMulMatrix b).commutes r).symm
    rw [hscalarLM, ← map_mul] at hmat
    rw [Algebra.leftMulMatrix_apply] at hmat
    change (LinearMap.toMatrix b b)
        (Algebra.lmul F E ((x.1 : E) * algebraMap F E r)) =
      Algebra.leftMulMatrix b c *
        (LinearMap.toMatrix b b) sigma.toLinearEquiv at hmat
    rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp,
      (LinearMap.toMatrix b b).injective.eq_iff] at hmat
    have hone := LinearMap.congr_fun hmat (1 : E)
    have hxr : (x.1 : E) * algebraMap F E r = c := by
      simpa [LinearMap.comp_apply, Algebra.lmul] using hone
    have hall : ∀ y : E, sigma y = y := by
      intro y
      have hy := LinearMap.congr_fun hmat y
      change ((x.1 : E) * algebraMap F E r) * y =
        c * sigma y at hy
      rw [hxr] at hy
      exact (mul_left_cancel₀ hc_ne hy).symm
    apply hsigma_ne_one
    ext y
    exact hall y
  have hfrobPSL_conj (x : K) :
      frobPSL * nonsplitTorus x * frobPSL⁻¹ =
        nonsplitTorus x⁻¹ := by
    simpa [frobPSL, nonsplitTorus] using congrArg
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F)))
      (hfrobSL_conj x)
  have hfrobPSL_mem_normalizer :
      frobPSL ∈ Subgroup.normalizer (nonsplitTorus.range : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x⁻¹, (hfrobPSL_conj x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x⁻¹, ?_⟩
      calc
        nonsplitTorus x⁻¹ =
            frobPSL⁻¹ *
              (frobPSL * nonsplitTorus x⁻¹ * frobPSL⁻¹) *
                frobPSL := by simp [mul_assoc]
        _ = frobPSL⁻¹ * nonsplitTorus x * frobPSL := by
          rw [hfrobPSL_conj]
          rw [inv_inv]
        _ = y := by rw [hx]; simp [mul_assoc]
  rcases hreflection_candidate_data nonsplitTorus.range frobPSL
      hfrobPSL_mem_normalizer (by simpa [pow_two] using hfrobPSL_sq)
        hfrobPSL_not_mem_torus with ⟨_, _, hcard⟩
  refine ⟨nonsplitTorus.range, frobPSL, hnonsplitTorus_cyclic,
    hnonsplit_range_card, hnonsplit_range_mul, hfrobPSL_mem_normalizer,
    hfrobPSL_not_mem_torus, ?_, ?_, hcard⟩
  · simpa only [pow_two] using hfrobPSL_sq
  · rintro t ⟨x, rfl⟩
    simpa only [map_inv] using hfrobPSL_conj x

end Kourovka2135.OddPSLTwoNonsplitNormTorus
