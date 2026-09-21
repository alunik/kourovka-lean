import Kourovka2135.OddPSLTwoProjectiveChart
import Mathlib.FieldTheory.Finite.Basic

/-! The actual center of SL2 over a finite field of odd cardinality has
exactly two elements. Only scalar matrices and roots of unity are used. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddSLTwoCenter

open scoped Matrix MatrixGroups

variable (F : Type*) [Field F] [Finite F]

theorem ringChar_ne_two (hodd : Odd (Nat.card F)) : ringChar F ≠ 2 := by
  let : Fintype F := Fintype.ofFinite F
  intro h
  have he := FiniteField.even_card_of_char_two h
  have ho : Odd (Fintype.card F) := by simpa only [Nat.card_eq_fintype_card] using hodd
  have hm := Nat.odd_iff.mp ho
  omega

def minusOne : SLTwo.SL2 F := ⟨!![-1, 0; 0, -1], by simp [Matrix.det_fin_two_of]⟩

omit [Finite F] in
theorem minusOne_mem_center : minusOne F ∈ Subgroup.center (SLTwo.SL2 F) := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusOne]

theorem minusOne_ne_one (hodd : Odd (Nat.card F)) : minusOne F ≠ 1 := by
  intro h
  have he := congrArg (fun g : SLTwo.SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have hn : (-1 : F) = 1 := by simpa [minusOne] using he
  exact Ring.neg_one_ne_one_of_char_ne_two (ringChar_ne_two F hodd) hn

/-- The cardinality is for the actual matrix-group center. -/
theorem card_center (hodd : Odd (Nat.card F)) :
    Nat.card (Subgroup.center (SLTwo.SL2 F)) = 2 := by
  have he := Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 2)).toEquiv
  have hb : Nat.card (Subgroup.center (SLTwo.SL2 F)) ≤ 2 := by
    rw [he]
    exact card_rootsOfUnity F 2
  have hn : Subgroup.center (SLTwo.SL2 F) ≠ ⊥ := by
    intro h
    have hm := minusOne_mem_center F
    rw [h, Subgroup.mem_bot] at hm
    exact minusOne_ne_one F hodd hm
  have hl := (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center (SLTwo.SL2 F))).mpr hn
  omega

theorem card_ker_quotient (hodd : Odd (Nat.card F)) :
    Nat.card (OddPSLTwoProjectiveChart.quotient F).ker = 2 := by
  change Nat.card (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))).ker = 2
  rw [QuotientGroup.ker_mk']
  exact card_center F hodd

end Kourovka2135.OddSLTwoCenter
