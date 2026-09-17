import Kourovka.Problem2153.BruhatReduction
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms

set_option autoImplicit false

namespace Kourovka.Problem2153

universe u v

/-- Algebraic form of the Iwasawa argument, using the normal core instead of building a
primitive action. Every structural assumption is explicit. -/
theorem isSimpleGroup_of_iwasawa_subgroups {G : Type u} [Group G] [Nontrivial G]
    (P Z : Subgroup G) (hMax : IsCoatom P) (hCore : P.normalCore = ⊥)
    (hNormalize : P ≤ Subgroup.normalizer (Z : Set G))
    (hAbelian : IsMulCommutative Z)
    (hGenerate : Subgroup.normalClosure (Z : Set G) = ⊤)
    (hPerfect : commutator G = ⊤) : IsSimpleGroup G := by
  constructor
  intro N hN
  let : N.Normal := hN
  by_cases hNP : N ≤ P
  · left
    apply le_antisymm _ bot_le
    have hncore : N ≤ P.normalCore := Subgroup.normal_le_normalCore.mpr hNP
    simpa only [hCore] using hncore
  · right
    have hJoin : N ⊔ P = ⊤ := by
      have hStrict : P < N ⊔ P := lt_of_le_of_ne le_sup_right (by
        intro heq
        apply hNP
        rw [heq]
        exact le_sup_left)
      exact hMax.2 _ hStrict
    have hPnormalizes : P ≤ Subgroup.normalizer ((N ⊔ Z : Subgroup G) : Set G) := by
      simpa only [sup_comm] using hNormalize.trans
        (Subgroup.normalizer_le_normalizer_sup_normal (H := Z) (K := N))
    have hNormalJoin : (N ⊔ Z).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_le_iff.mp
      rw [← hJoin]
      exact sup_le (le_sup_left.trans Subgroup.le_normalizer) hPnormalizes
    let : (N ⊔ Z).Normal := hNormalJoin
    have hNZ : N ⊔ Z = ⊤ := by
      apply top_le_iff.mp
      rw [← hGenerate]
      exact Subgroup.normalClosure_le_normal (fun z hz => Subgroup.mem_sup_right hz)
    have hc : commutator G ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNZ hAbelian
    exact top_le_iff.mp (hPerfect ▸ hc)

/-- Normality of a root subgroup inside the maximal subgroup supplies the normalizer premise. -/
theorem isSimpleGroup_of_iwasawa_normal_root {G : Type u} [Group G] [Nontrivial G]
    (P Z : Subgroup G) (hZP : Z ≤ P) [(Z.subgroupOf P).Normal]
    (hMax : IsCoatom P) (hCore : P.normalCore = ⊥)
    (hAbelian : IsMulCommutative Z)
    (hGenerate : Subgroup.normalClosure (Z : Set G) = ⊤)
    (hPerfect : commutator G = ⊤) : IsSimpleGroup G :=
  isSimpleGroup_of_iwasawa_subgroups P Z hMax hCore
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hZP).mp inferInstance)
    hAbelian hGenerate hPerfect

/-- A finite list of conjugacy tests suffices for triviality of the entire normal core.
This accepts, for example, a verified projective frame and one connecting line. -/
theorem normalCore_eq_bot_of_tests {G : Type u} [Group G] {I : Type v}
    (P : Subgroup G) (test : I → G)
    (hTest : ∀ g : G, (∀ i, test i * g * (test i)⁻¹ ∈ P) → g = 1) :
    P.normalCore = ⊥ := by
  apply P.normalCore.eq_bot_iff_forall.mpr
  intro g hg
  exact hTest g (fun i => hg (test i))

/-- Faithfulness on the single orbit of a point proves its stabilizer has trivial core. -/
theorem normalCore_stabilizer_eq_bot_of_orbit_faithful
    {G : Type u} [Group G] {X : Type v} [MulAction G X] (a : X)
    (hFaithful : ∀ g : G, (∀ h : G, g • (h • a) = h • a) → g = 1) :
    (MulAction.stabilizer G a).normalCore = ⊥ := by
  apply normalCore_eq_bot_of_tests (MulAction.stabilizer G a) (fun h : G => h)
  intro g hg
  apply hFaithful g
  intro h
  have hh := hg h⁻¹
  change (h⁻¹ * g * (h⁻¹)⁻¹) • a = a at hh
  simpa only [inv_inv, mul_smul, smul_inv_smul] using congrArg (fun b => h • b) hh

/-- Standard faithful transitive actions are a specialization of orbit faithfulness. -/
theorem normalCore_stabilizer_eq_bot_of_faithful
    {G : Type u} [Group G] {X : Type v} [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G X] (a : X) :
    (MulAction.stabilizer G a).normalCore = ⊥ := by
  apply normalCore_stabilizer_eq_bot_of_orbit_faithful a
  intro g hg
  apply ((faithfulSMul_iff (G := G) (α := X)).mp inferInstance) g
  intro b
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G a b
  exact hg h

/-- Faithfulness of the standard coset action discharges the normal-core condition directly. -/
theorem normalCore_eq_bot_of_faithful_cosets {G : Type u} [Group G] (P : Subgroup G)
    [FaithfulSMul G (G ⧸ P)] : P.normalCore = ⊥ := by
  have h := normalCore_stabilizer_eq_bot_of_faithful (G := G) ((1 : G) : G ⧸ P)
  simpa only [MulAction.stabilizer_quotient] using h

/-- Perfectness can be certified just on a normally generating root subgroup. -/
theorem perfect_of_normal_root {G : Type u} [Group G] (Z : Subgroup G)
    (hGenerate : Subgroup.normalClosure (Z : Set G) = ⊤) (hComm : Z ≤ commutator G) :
    commutator G = ⊤ := by
  apply top_le_iff.mp
  rw [← hGenerate]
  exact Subgroup.normalClosure_le_normal hComm

/-- Membership certificates for a generating set prove normal generation. -/
theorem normalClosure_eq_top_of_generators {G : Type u} [Group G]
    (Z : Subgroup G) (S : Set G) (hGenerate : Subgroup.closure S = ⊤)
    (hWords : S ⊆ Subgroup.normalClosure (Z : Set G)) :
    Subgroup.normalClosure (Z : Set G) = ⊤ := by
  apply top_le_iff.mp
  rw [← hGenerate]
  exact (Subgroup.closure_le _).mpr hWords

/-- BWB coverage reduces maximality to extracting the missing generator from a Weyl element.
The finite Weyl computation is the explicit hypothesis hExtract. -/
theorem isCoatom_of_bruhat_weyl_extraction {G : Type u} [Group G] {K : Type v}
    (B P : Subgroup G) (W : K → G) (r s t w₀ : G)
    (hProper : P ≠ ⊤) (hBP : B ≤ P) (hr : r ∈ P) (ht : t ∈ B)
    (hCover : ∀ g : G, ∃ b₁ ∈ B, ∃ k, ∃ b₂ ∈ B, g = b₁ * W k * b₂)
    (hExtract : ∀ (J : Subgroup G) k, r ∈ J → W k ∈ J → W k ∉ P → w₀ ∈ J)
    (hWord : t * rightConj t w₀ * t = s)
    (hGenerate : Subgroup.closure ((B : Set G) ∪ {r, s}) = ⊤) : IsCoatom P := by
  apply SetLike.isCoatom_iff.mpr
  refine ⟨hProper, ?_⟩
  intro J g hPJ hgP hgJ
  obtain ⟨b₁, hb₁, k, b₂, hb₂, hg⟩ := hCover g
  have hb₁J : b₁ ∈ J := hPJ (hBP hb₁)
  have hb₂J : b₂ ∈ J := hPJ (hBP hb₂)
  have hwJ : W k ∈ J := by
    have hh := J.mul_mem (J.mul_mem (J.inv_mem hb₁J) hgJ) (J.inv_mem hb₂J)
    simpa [hg, mul_assoc] using hh
  have hwP : W k ∉ P := by
    intro hw
    apply hgP
    rw [hg]
    exact P.mul_mem (P.mul_mem (hBP hb₁) hw) (hBP hb₂)
  have hrJ := hPJ hr
  have hw₀J := hExtract J k hrJ hwJ hwP
  have htJ := hPJ (hBP ht)
  have hsJ : s ∈ J := by
    rw [← hWord]
    exact J.mul_mem (J.mul_mem htJ
      (J.mul_mem (J.mul_mem (J.inv_mem hw₀J) htJ) hw₀J)) htJ
  apply top_le_iff.mp
  rw [← hGenerate]
  apply (Subgroup.closure_le _).mpr
  intro a ha
  rcases ha with haB | haRS
  · exact hPJ (hBP haB)
  · rcases haRS with rfl | haS
    · exact hrJ
    · have has : a = s := Set.mem_singleton_iff.mp haS
      subst a
      exact hsJ

/-- The Weyl extraction input can be supplied as finite subgroup-word certificates. -/
theorem isCoatom_of_bruhat_weyl_closure_tests {G : Type u} [Group G] {K : Type v}
    (B P : Subgroup G) (W : K → G) (r s t w₀ : G)
    (hProper : P ≠ ⊤) (hBP : B ≤ P) (hr : r ∈ P) (ht : t ∈ B)
    (hCover : ∀ g : G, ∃ b₁ ∈ B, ∃ k, ∃ b₂ ∈ B, g = b₁ * W k * b₂)
    (hWeyl : ∀ k, W k ∉ P → w₀ ∈ Subgroup.closure ({r, W k} : Set G))
    (hWord : t * rightConj t w₀ * t = s)
    (hGenerate : Subgroup.closure ((B : Set G) ∪ {r, s}) = ⊤) : IsCoatom P := by
  apply isCoatom_of_bruhat_weyl_extraction B P W r s t w₀ hProper hBP hr ht hCover _
    hWord hGenerate
  intro J k hrJ hwJ hwP
  have hle : Subgroup.closure ({r, W k} : Set G) ≤ J := by
    apply (Subgroup.closure_le J).mpr
    intro a ha
    rcases ha with rfl | ha
    · exact hrJ
    · have ha' : a = W k := Set.mem_singleton_iff.mp ha
      subst a
      exact hwJ
  exact hle (hWeyl k hwP)

#print axioms isSimpleGroup_of_iwasawa_subgroups
#print axioms isSimpleGroup_of_iwasawa_normal_root
#print axioms normalCore_eq_bot_of_tests
#print axioms normalCore_stabilizer_eq_bot_of_orbit_faithful
#print axioms normalCore_stabilizer_eq_bot_of_faithful
#print axioms normalCore_eq_bot_of_faithful_cosets
#print axioms perfect_of_normal_root
#print axioms normalClosure_eq_top_of_generators
#print axioms isCoatom_of_bruhat_weyl_extraction
#print axioms isCoatom_of_bruhat_weyl_closure_tests

end Kourovka.Problem2153
