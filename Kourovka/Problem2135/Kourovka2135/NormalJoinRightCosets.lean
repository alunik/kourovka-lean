import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index

/-! Actual right-coset geometry for a normal subgroup and a normalizing join.

Let N be normal in G, A a subgroup of N, and C normalize the actual ambient
image of A. The necessary intersection condition N ∩ C ≤ A makes the cosets
of A C in N C correspond to N/A. No complement or semidirect-product model
is assumed. The equivalence here uses inversion to convert mathlib's existing
left-coset embedding into right cosets: [n] maps to (A C)n⁻¹. Right multiplication
by c consequently corresponds to inverse conjugation on N/A.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.NormalJoinRightCosets

open scoped Pointwise

universe u
variable {G : Type u} [Group G]
variable (N : Subgroup G) (A : Subgroup N) (C : Subgroup G)

abbrev Ambient := ↥(N ⊔ C)
abbrev Joined := A.map N.subtype ⊔ C
abbrev Stabilizer : Subgroup (Ambient N C) := (Joined N A C).subgroupOf (N ⊔ C)
abbrev RightCosets := Quotient (QuotientGroup.rightRel (Stabilizer N A C))

/-- Actual inclusions into the ambient join. -/
def includeN : N →* Ambient N C := Subgroup.inclusion le_sup_left
def includeC : C →* Ambient N C := Subgroup.inclusion le_sup_right

/-- Right multiplication on the actual right cosets. -/
def rightTranslate (c : C) : RightCosets N A C → RightCosets N A C :=
  Quotient.map (fun h => h * includeC N C c) (by
    intro x y h
    change QuotientGroup.rightRel (Stabilizer N A C) x y at h
    change QuotientGroup.rightRel (Stabilizer N A C)
      (x * includeC N C c) (y * includeC N C c)
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h)

@[simp] theorem rightTranslate_mk (c : C) (h : Ambient N C) :
    rightTranslate N A C c (Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C)) h) =
      Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C)) (h * includeC N C c) := rfl

/-- The right-translation function has exactly the out-representative formula
used by the checked coinduced-character formula. -/
theorem rightTranslate_out (c : C) (q : RightCosets N A C) :
    rightTranslate N A C c q =
      Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C))
        (Quotient.out q * includeC N C c) := by
  calc
    rightTranslate N A C c q = rightTranslate N A C c
        (Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C)) (Quotient.out q)) :=
      congrArg (rightTranslate N A C c) (Quotient.out_eq q).symm
    _ = _ := rfl

/-- Membership in the actual ambient image of A is equivalent to membership in A. -/
theorem mem_ambientA_iff (n : N) : (n : G) ∈ A.map N.subtype ↔ n ∈ A := by
  constructor
  · rintro ⟨a, ha, he⟩
    have han : a = n := Subtype.ext he
    exact han ▸ ha
  · intro hn
    exact Subgroup.mem_map_of_mem N.subtype hn

variable (hnorm : C ≤ Subgroup.normalizer (A.map N.subtype))
variable (hinter : N ⊓ C ≤ A.map N.subtype)

include hnorm hinter in
/-- The minimal intersection condition gives the exact subgroup intersection. -/
theorem joined_subgroupOf_eq : (Joined N A C).subgroupOf N = A := by
  ext n
  constructor
  · intro hn
    have hprod : (n : G) ∈ (A.map N.subtype : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (A.map N.subtype) C hnorm]
      exact hn
    obtain ⟨a₀, ha₀, c, hc, he⟩ := hprod
    obtain ⟨a, ha, rfl⟩ := ha₀
    change (a : G) * c = (n : G) at he
    have hcN : c ∈ N := by
      have hec : (a : G)⁻¹ * (n : G) = c := by
        rw [← he]
        simp only [inv_mul_cancel_left]
      rw [← hec]
      exact N.mul_mem (N.inv_mem a.property) n.property
    obtain ⟨b, hb, hbval⟩ := hinter ⟨hcN, hc⟩
    change (b : G) = c at hbval
    have hab : a * b = n := by
      apply Subtype.ext
      change (a : G) * (b : G) = n
      rw [hbval]
      exact he
    exact hab ▸ A.mul_mem ha hb
  · intro hn
    exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem N.subtype hn)

variable [N.Normal]

/-- Product decomposition N C gives surjectivity of mathlib's actual coset inclusion. -/
theorem quotientEmbedding_surjective : Function.Surjective
    (Subgroup.quotientSubgroupOfEmbeddingOfLE (Joined N A C)
      (show N ≤ N ⊔ C from le_sup_left)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro h
  obtain ⟨n, hn, c, hc, he⟩ := Subgroup.mem_sup_of_normal_left.mp h.property
  refine ⟨QuotientGroup.mk (⟨n, hn⟩ : N), ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk]
  apply Quotient.sound
  change QuotientGroup.leftRel (Stabilizer N A C) (includeN N C ⟨n, hn⟩) h
  rw [QuotientGroup.leftRel_apply]
  change n⁻¹ * (h : G) ∈ Joined N A C
  rw [← he, inv_mul_cancel_left]
  exact Subgroup.mem_sup_right hc

/-- The actual left-coset inclusion is a bijection onto the join cosets. -/
def quotientEmbeddingEquiv :
    (N ⧸ (Joined N A C).subgroupOf N) ≃
      ((Ambient N C) ⧸ Stabilizer N A C) :=
  Equiv.ofBijective
    (Subgroup.quotientSubgroupOfEmbeddingOfLE (Joined N A C)
      (show N ≤ N ⊔ C from le_sup_left))
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE (Joined N A C)
      (show N ≤ N ⊔ C from le_sup_left)).injective,
      quotientEmbedding_surjective N A C⟩

/-- The actual coset equivalence, with no assumed complement. -/
def cosetEquiv : (N ⧸ A) ≃ RightCosets N A C :=
  (Subgroup.quotientEquivOfEq (joined_subgroupOf_eq N A C hnorm hinter).symm).trans
    ((quotientEmbeddingEquiv N A C).trans
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Stabilizer N A C)).symm)

@[simp] theorem cosetEquiv_mk (n : N) :
    cosetEquiv N A C hnorm hinter (QuotientGroup.mk n) =
      Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C))
        ((includeN N C n)⁻¹) := rfl

include hnorm hinter in
/-- Exact relative index; no finiteness hypothesis is required for Nat.card. -/
theorem index_eq : (Stabilizer N A C).index = A.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr
    ((QuotientGroup.quotientRightRelEquivQuotientLeftRel (Stabilizer N A C)).symm.trans
      (cosetEquiv N A C hnorm hinter).symm)

include hnorm in
/-- Actual conjugation by C preserves A, in both directions. -/
theorem conj_mem_A_iff (c : C) (n : N) :
    MulAut.conjNormal (c : G) n ∈ A ↔ n ∈ A := by
  rw [← mem_ambientA_iff N A (MulAut.conjNormal (c : G) n), ← mem_ambientA_iff N A n]
  change (c : G) * (n : G) * (c : G)⁻¹ ∈ A.map N.subtype ↔ (n : G) ∈ A.map N.subtype
  exact (Subgroup.mem_normalizer_iff.mp (hnorm c.property) (n : G)).symm

include hnorm in
/-- Equality of the actual A subgroups under actual conjugation. -/
theorem map_A_conj (c : C) : A.map (MulAut.conjNormal (c : G) : MulAut N).toMonoidHom = A := by
  apply le_antisymm
  · rintro x ⟨n, hn, rfl⟩
    exact (conj_mem_A_iff N A C hnorm c n).mpr hn
  · intro x hx
    refine ⟨(MulAut.conjNormal (c : G) : MulAut N).symm x, ?_,
      (MulAut.conjNormal (c : G) : MulAut N).apply_symm_apply x⟩
    apply (conj_mem_A_iff N A C hnorm c _).mp
    simpa only [MulEquiv.apply_symm_apply] using hx

variable [A.Normal]

/-- Forward conjugation on the actual quotient N/A. -/
def conjugationQuotient (c : C) : MulAut (N ⧸ A) :=
  QuotientGroup.congr A A (MulAut.conjNormal (c : G)) (map_A_conj N A C hnorm c)

@[simp] theorem conjugationQuotient_mk (c : C) (n : N) :
    conjugationQuotient N A C hnorm c (QuotientGroup.mk' A n) =
      QuotientGroup.mk' A (MulAut.conjNormal (c : G) n) := rfl

@[simp] theorem conjugationQuotient_symm_mk (c : C) (n : N) :
    (conjugationQuotient N A C hnorm c).symm (QuotientGroup.mk' A n) =
      QuotientGroup.mk' A ((MulAut.conjNormal (c : G) : MulAut N).symm n) := rfl

/-- Right multiplication on right cosets is inverse conjugation on N/A. -/
theorem cosetEquiv_rightTranslate (c : C) (x : N ⧸ A) :
    rightTranslate N A C c (cosetEquiv N A C hnorm hinter x) =
      cosetEquiv N A C hnorm hinter ((conjugationQuotient N A C hnorm c).symm x) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective A x
  rw [conjugationQuotient_symm_mk]
  change rightTranslate N A C c (cosetEquiv N A C hnorm hinter (QuotientGroup.mk n)) =
    cosetEquiv N A C hnorm hinter (QuotientGroup.mk _)
  rw [cosetEquiv_mk, cosetEquiv_mk, rightTranslate_mk]
  apply Quotient.sound
  change QuotientGroup.rightRel (Stabilizer N A C)
    ((includeN N C n)⁻¹ * includeC N C c)
    ((includeN N C ((MulAut.conjNormal (c : G) : MulAut N).symm n))⁻¹)
  rw [QuotientGroup.rightRel_apply]
  change (((MulAut.conjNormal (c : G) : MulAut N).symm n : N) : G)⁻¹ *
    ((n : G)⁻¹ * (c : G))⁻¹ ∈ Joined N A C
  rw [MulAut.conjNormal_symm_apply]
  simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel, mul_one] using
    (show (c : G)⁻¹ ∈ Joined N A C from Subgroup.mem_sup_right (C.inv_mem c.property))

include hinter in
/-- A unique fixed quotient point gives exactly the unique fixed right coset
required by the actual coinduced-character formula. -/
theorem rightCoset_fixed_iff (c : C)
    (hfix : ∀ x : N ⧸ A, conjugationQuotient N A C hnorm c x = x ↔ x = 1)
    (q : RightCosets N A C) :
    Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C))
        (Quotient.out q * includeC N C c) = q ↔
      q = Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C)) 1 := by
  rw [← rightTranslate_out]
  obtain ⟨x, rfl⟩ := (cosetEquiv N A C hnorm hinter).surjective q
  rw [cosetEquiv_rightTranslate]
  have hbase : cosetEquiv N A C hnorm hinter (1 : N ⧸ A) =
      Quotient.mk (QuotientGroup.rightRel (Stabilizer N A C)) 1 := by
    change cosetEquiv N A C hnorm hinter (QuotientGroup.mk (1 : N)) = _
    rw [cosetEquiv_mk, map_one, inv_one]
  constructor
  · intro h
    have hinv := (cosetEquiv N A C hnorm hinter).injective h
    have hforward : conjugationQuotient N A C hnorm c x = x := by
      have he := congrArg (conjugationQuotient N A C hnorm c) hinv
      rw [MulEquiv.apply_symm_apply] at he
      exact he.symm
    rw [(hfix x).mp hforward]
    exact hbase
  · intro h
    have hx : x = 1 := (cosetEquiv N A C hnorm hinter).injective (h.trans hbase.symm)
    rw [hx, map_one]

end Kourovka2135.NormalJoinRightCosets
