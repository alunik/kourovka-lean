/-
Selected matrix and cardinality proofs adapted from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Sources: GorensteinWalter/PSL2Cardinality.lean (SL2 cardinality) and
BenderSuzuki/Converse/PSL2.lean (root/torus homomorphisms and conjugation).
The original mathematical source has no per-file author declaration.
See Vendor/CFSG/LICENSE and verification/sl-two-unipotent/provenance.json.
Only the indicated elementary proofs are selected; no CFSG classification
or Borel-recognition package is imported.
-/
import Kourovka2135.CohomologyNormalizer
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic

/-! The actual SL2 root subgroup, its diagonal torus, and odd-index
restriction bounds in characteristic two. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.SLTwo
open Matrix CategoryTheory
open scoped MatrixGroups
variable {K : Type u} [Field K]

abbrev SL2 (K : Type u) [Field K] := Matrix.SpecialLinearGroup (Fin 2) K

/-- The upper root element. -/
def uni (b : K) : SL2 K := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The diagonal torus element. -/
def tor (a : Kˣ) : SL2 K := ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by
  simp [Matrix.det_fin_two_of]⟩

@[simp] theorem uni_val (b : K) : (uni b).val = !![1, b; 0, 1] := rfl
@[simp] theorem tor_val (a : Kˣ) :
    (tor a).val = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

def uniHom (K : Type u) [Field K] : Multiplicative K →* SL2 K where
  toFun b := uni b.toAdd
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def torHom (K : Type u) [Field K] : Kˣ →* SL2 K where
  toFun := tor
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[simp] theorem uniHom_apply (b : K) : uniHom K (Multiplicative.ofAdd b) = uni b := rfl
@[simp] theorem torHom_apply (a : Kˣ) : torHom K a = tor a := rfl

theorem uniHom_injective : Function.Injective (uniHom K) := by
  intro a b hab
  have := congrFun (congrFun (congrArg Subtype.val hab) 0) 1
  change a.toAdd = b.toAdd at this
  exact congrArg Multiplicative.ofAdd this

theorem torHom_injective : Function.Injective (torHom K) := by
  intro a b hab
  have := congrFun (congrFun (congrArg Subtype.val hab) 0) 0
  simp [torHom] at this
  exact Units.ext this

def Unip (K : Type u) [Field K] : Subgroup (SL2 K) := (uniHom K).range

def Torus (K : Type u) [Field K] : Subgroup (SL2 K) := (torHom K).range

theorem mem_Unip_iff (A : SL2 K) : A ∈ Unip K ↔ ∃ b : K, A = uni b := by
  simp [Unip, MonoidHom.mem_range]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

@[simp] theorem tor_inv (a : Kˣ) : (tor a)⁻¹ = tor a⁻¹ :=
  (map_inv (torHom K) a).symm

/-- Left conjugation by a torus element scales the root parameter by its square. -/
theorem tor_conj_uni (a : Kˣ) (b : K) :
    tor a * uni b * (tor a)⁻¹ = uni ((a : K) ^ 2 * b) := by
  have key : tor a * uni b = uni ((a : K) ^ 2 * b) * tor a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc,
        mul_comm]
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

theorem torus_le_normalizer : Torus K ≤ (Subgroup.normalizer (Unip K : Set (SL2 K))) := by
  refine (Subgroup.le_normalizer_iff (H := Torus K) (K := Unip K)).mpr ?_
  intro A hA B hB
  change ∃ a : Kˣ, tor a = A at hA
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := (mem_Unip_iff B).mp hB
  exact (mem_Unip_iff _).mpr ⟨(a : K) ^ 2 * b, tor_conj_uni a b⟩

/-- The same actual torus, regarded as a subgroup of the root-subgroup normalizer. -/
def torusInNormalizer (K : Type u) [Field K] : Subgroup (Subgroup.normalizer (Unip K : Set (SL2 K))) :=
  (Torus K).subgroupOf (Subgroup.normalizer (Unip K : Set (SL2 K)))

theorem torusInNormalizer_map :
    (torusInNormalizer K).map (Subgroup.normalizer (Unip K : Set (SL2 K))).subtype = Torus K :=
  Subgroup.map_subgroupOf_eq_of_le torus_le_normalizer

theorem card_unip : Nat.card (Unip K) = Nat.card K := by
  calc
    _ = Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective (uniHom_injective (K := K))).toEquiv).symm
    _ = Nat.card K := (Nat.card_congr (Multiplicative.ofAdd : K ≃ Multiplicative K)).symm

private lemma specialLinearGroup_fin_two_card_eq_det_ker
    (K : Type*) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card ((Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker) := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker :=
    Matrix.SpecialLinearGroup.toGL.codRestrict _ (by
      intro A
      exact MonoidHom.mem_ker.mpr
        (Matrix.SpecialLinearGroup.coeToGL_det A))
  have hf_inj : Function.Injective f := by
    intro A B h
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro A
    refine ⟨⟨(A : Matrix.GeneralLinearGroup (Fin 2) K).1, ?_⟩, ?_⟩
    · have hdet := MonoidHom.mem_ker.mp A.property
      change ((A : Matrix.GeneralLinearGroup (Fin 2) K).1).det = 1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using
        congrArg Units.val hdet
    · apply Subtype.ext
      apply Units.ext
      rfl
  exact Nat.card_congr (MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).toEquiv

/-- The order formula `|SL₂(K)| = q(q² - 1)` for a finite field of order
`q = Nat.card K`. -/
theorem sl2_card_formula (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let d : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ :=
    Matrix.GeneralLinearGroup.det
  have hdet_surj : Function.Surjective d :=
    Matrix.GeneralLinearGroup.det_surjective
  have hidx : d.ker.index = Nat.card Kˣ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hdet_surj,
      Subgroup.card_top]
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    rw [Matrix.card_GL_field]
    norm_num [Fintype.card_fin]
  have hker : Nat.card d.ker * d.ker.index =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Subgroup.card_mul_index d.ker
  have hunit : Fintype.card Kˣ = Fintype.card K - 1 :=
    Fintype.card_units K
  have hGL' : Fintype.card (Matrix.GeneralLinearGroup (Fin 2) K) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    simpa only [Nat.card_eq_fintype_card] using hGL
  have hker' : Nat.card d.ker * (Fintype.card K - 1) =
      (Fintype.card K ^ 2 - 1) *
        (Fintype.card K ^ 2 - Fintype.card K) := by
    simpa [hidx, hunit, hGL'] using hker
  have hq : 1 < Fintype.card K :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hqsub : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt hq
  have hfactor : Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib]
    simp
  have hker'' : Nat.card d.ker * (Fintype.card K - 1) =
      (Fintype.card K * (Fintype.card K ^ 2 - 1)) *
        (Fintype.card K - 1) := by
    calc
      Nat.card d.ker * (Fintype.card K - 1) =
          (Fintype.card K ^ 2 - 1) *
            (Fintype.card K ^ 2 - Fintype.card K) := hker'
      _ = (Fintype.card K * (Fintype.card K ^ 2 - 1)) *
          (Fintype.card K - 1) := by rw [hfactor]; ac_rfl
  have hcardker : Nat.card d.ker =
      Fintype.card K * (Fintype.card K ^ 2 - 1) :=
    Nat.eq_of_mul_eq_mul_right hqsub hker''
  rw [specialLinearGroup_fin_two_card_eq_det_ker, hcardker]
  simp only [Nat.card_eq_fintype_card]


theorem index_unip [Finite K] : (Unip K).index = Nat.card K ^ 2 - 1 := by
  have h := (Unip K).card_mul_index
  rw [card_unip, sl2_card_formula] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem odd_index_unip [Finite K] [CharP K 2] : Odd (Unip K).index := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff K 2 (Fintype.card K)).mp (Nat.cast_card_eq_zero K)
  have heven : Even (Nat.card K ^ 2) :=
    (even_iff_two_dvd.mpr hcard).pow_of_ne_zero (by decide)
  have hpos : 1 ≤ Nat.card K ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Nat.card_pos.ne')
  rw [index_unip]
  exact Nat.Even.sub_odd hpos heven (by decide)

/-- The concrete root subgroup and diagonal torus give the normalizer-fixed
upper bound for actual first and second SL2 cohomology. -/
theorem finrank_le_torusFixed_of_charTwo [Finite K] [CharP K 2]
    {k : Type u} [Field k] [CharP k 2]
    (A : Rep k (SL2 K)) (n : ℕ) (hn : n = 1 ∨ n = 2)
    [Module.Finite k (groupCohomology (Rep.res (Unip K).subtype A) n)] :
    Module.finrank k (groupCohomology A n) ≤
      Module.finrank k (GroupCohomology.normalizerFixedSubmodule (Unip K) A
        (torusInNormalizer K) n) :=
  GroupCohomology.finrank_le_normalizerFixed_of_odd_index
    (Unip K) A (torusInNormalizer K) n hn odd_index_unip

end Kourovka2135.SLTwo
