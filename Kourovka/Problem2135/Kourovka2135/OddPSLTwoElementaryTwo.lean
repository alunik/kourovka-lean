import Kourovka2135.OddPSLTwoSplitInvolution
import Mathlib.FieldTheory.AlgebraicClosure

/-! Elementary abelian binary subgroups of PSL2 over any odd field.

Entrywise field embeddings induce actual injective homomorphisms on PSL2.
Embedding into the algebraic closure therefore removes the square-root-of-minus-one
premise from the already proved rank-two and self-centralizer calculations.
No subgroup classification or finiteness of the ambient field is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoElementaryTwo

open OddPSLTwoProjectiveChart
open scoped IsMulCommutative

variable {F L : Type*} [Field F] [Field L]

theorem mem_center_iff_entries (A : SLTwo.SL2 F) :
    A ∈ Subgroup.center (SLTwo.SL2 F) ↔
      A.val 0 1 = 0 ∧ A.val 1 0 = 0 ∧ A.val 0 0 = A.val 1 1 := by
  constructor
  · intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hr
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hr
    have h00' : r = A.val 0 0 := by simpa [Matrix.scalar] using h00
    have h11' : r = A.val 1 1 := by simpa [Matrix.scalar] using h11
    refine ⟨?_, ?_, h00'.symm.trans h11'⟩
    · simpa [Matrix.scalar] using h01.symm
    · simpa [Matrix.scalar] using h10.symm
  · rintro ⟨hb, hc, hd⟩
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨A.val 0 0, ?_, ?_⟩
    · simpa only [Fintype.card_fin, pow_two, ← hd, hb, hc, zero_mul, sub_zero,
        Matrix.det_fin_two] using A.det_coe
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hb, hc, hd]

theorem map_mem_center_iff (f : F →+* L) (A : SLTwo.SL2 F) :
    Matrix.SpecialLinearGroup.map f A ∈ Subgroup.center (SLTwo.SL2 L) ↔
      A ∈ Subgroup.center (SLTwo.SL2 F) := by
  rw [mem_center_iff_entries, mem_center_iff_entries]
  change (f (A.val 0 1) = 0 ∧ f (A.val 1 0) = 0 ∧
    f (A.val 0 0) = f (A.val 1 1)) ↔ _
  simp only [map_eq_zero, f.injective.eq_iff]

theorem comap_center (f : F →+* L) :
    (Subgroup.center (SLTwo.SL2 L)).comap (Matrix.SpecialLinearGroup.map f) =
      Subgroup.center (SLTwo.SL2 F) := by
  ext A
  exact map_mem_center_iff f A

/-- The actual entrywise embedding on the projective quotients. -/
def projectiveMap (f : F →+* L) : Q F →* Q L :=
  QuotientGroup.map (Subgroup.center (SLTwo.SL2 F))
    (Subgroup.center (SLTwo.SL2 L)) (Matrix.SpecialLinearGroup.map f)
    (by rw [comap_center])

theorem projectiveMap_injective (f : F →+* L) :
    Function.Injective (projectiveMap f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [projectiveMap, QuotientGroup.ker_map, comap_center,
    QuotientGroup.map_mk'_self]

@[simp] theorem projectiveMap_quotient (f : F →+* L) (A : SLTwo.SL2 F) :
    projectiveMap f (quotient F A) = quotient L (Matrix.SpecialLinearGroup.map f A) := rfl

private theorem exists_closed_sqrt_neg_one (hodd : (-1 : F) ≠ 1) :
    ∃ i : (AlgebraicClosure F)ˣ,
      (i : AlgebraicClosure F) ^ 2 = -1 ∧ (i : AlgebraicClosure F) ^ 2 ≠ 1 := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure F)
    (by decide : 0 < 2)
  have hi0 : i ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hi
    exact neg_ne_zero.mpr one_ne_zero hi.symm
  refine ⟨Units.mk0 i hi0, hi, ?_⟩
  change i ^ 2 ≠ 1
  rw [hi]
  intro h
  apply hodd
  apply (algebraMap F (AlgebraicClosure F)).injective
  simpa only [map_neg, map_one] using h

/-- Every elementary abelian 2-subgroup has at most four elements. -/
theorem card_le_four (hodd : (-1 : F) ≠ 1)
    (E : Subgroup (Q F)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Q F →* Q (AlgebraicClosure F) := projectiveMap (algebraMap F _)
  let E' : Subgroup (Q (AlgebraicClosure F)) := E.map f
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  obtain ⟨i, hi, hine⟩ := exists_closed_sqrt_neg_one hodd
  have h := OddPSLTwoSplitInvolution.card_elementary_two_le_four
    (AlgebraicClosure F) E' i hi hine
  have hc : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (projectiveMap_injective _)
  exact hc ▸ h

/-- A subgroup of order four is self-centralizing in the actual PSL2 group. -/
theorem centralizer_eq_self (hodd : (-1 : F) ≠ 1)
    (E : Subgroup (Q F)) [IsElementaryAbelian 2 E] (hcard : Nat.card E = 4) :
    Subgroup.centralizer (E : Set (Q F)) = E := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Q F →* Q (AlgebraicClosure F) := projectiveMap (algebraMap F _)
  have hf : Function.Injective f := projectiveMap_injective _
  let E' : Subgroup (Q (AlgebraicClosure F)) := E.map f
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map f
  have hc : Nat.card E' = 4 := (Subgroup.card_map_of_injective hf).trans hcard
  obtain ⟨i, hi, hine⟩ := exists_closed_sqrt_neg_one hodd
  have hC := OddPSLTwoSplitInvolution.centralizer_elementary_four_eq_self
    (AlgebraicClosure F) E' hc i hi hine
  apply le_antisymm
  · intro x hx
    have hfx : f x ∈ Subgroup.centralizer (E' : Set (Q (AlgebraicClosure F))) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hx) z hz]
    rw [hC] at hfx
    exact (Subgroup.mem_map_iff_mem hf).mp hfx
  · intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact setLike_mul_comm hy hx

end Kourovka2135.OddPSLTwoElementaryTwo
