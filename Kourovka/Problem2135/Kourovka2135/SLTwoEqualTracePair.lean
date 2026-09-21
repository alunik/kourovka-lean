import Kourovka2135.SLTwoTraceGoodSet

/-! An explicit determinant-one pair with prescribed common nonzero trace
whose product is a chosen diagonal. Nonsquareness of the diagonal parameter
forces the first matrix outside both coordinate Borels and their normalizer.
The structural generation criterion is retained as an explicit hypothesis. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoEqualTracePair
open scoped Matrix
open SLTwoNonscalarWordValues GeneratingPairNielsen
variable {F : Type*} [Field F]

def left (s : Fˣ) (t : F) : SLTwo.SL2 F :=
  let a := t * (s : F) / ((s : F) + 1)
  let d := t / ((s : F) + 1)
  ⟨!![a, 1; a * d - 1, d], by simp [Matrix.det_fin_two_of]⟩

def right (s : Fˣ) (t : F) : SLTwo.SL2 F := (left s t)⁻¹ * SLTwo.tor s

theorem left_mul_right (s : Fˣ) (t : F) : left s t * right s t = SLTwo.tor s := by
  exact mul_inv_cancel_left _ _

theorem trace_left (s : Fˣ) (hs : (s : F) + 1 ≠ 0) (t : F) :
    (left s t).val.trace = t := by
  simp only [left, Matrix.trace_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

theorem trace_right (s : Fˣ) (hs : (s : F) + 1 ≠ 0) (t : F) :
    (right s t).val.trace = t := by
  change ((↑((left s t)⁻¹) : Matrix (Fin 2) (Fin 2) F) * (SLTwo.tor s).val).trace = _
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [left, SLTwo.tor, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  field_simp

theorem left_nonscalar (s : Fˣ) (t : F) : Nonscalar (left s t) := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  simp [left] at h

theorem right_nonscalar (s : Fˣ) (t : F) : Nonscalar (right s t) := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  have hz : -(s : F)⁻¹ = 0 := by
    change ((↑((left s t)⁻¹) : Matrix (Fin 2) (Fin 2) F) * (SLTwo.tor s).val) 0 1 = _ at h
    rw [Matrix.SpecialLinearGroup.coe_inv] at h
    simp [left, SLTwo.tor, Matrix.adjugate_fin_two] at h
  exact (neg_ne_zero.mpr (inv_ne_zero s.ne_zero)) hz

theorem left_upper_right (s : Fˣ) (t : F) : (left s t).val 0 1 = 1 := rfl

theorem left_diagonal_ne_zero (s : Fˣ) (hs : (s : F) + 1 ≠ 0)
    (t : F) (ht : t ≠ 0) : (left s t).val 0 0 ≠ 0 ∧ (left s t).val 1 1 ≠ 0 :=
  ⟨div_ne_zero (mul_ne_zero ht s.ne_zero) hs, div_ne_zero ht hs⟩

theorem left_lower_left_ne_zero (s : Fˣ) (hs : (s : F) + 1 ≠ 0)
    (hns : ¬ IsSquare (s : F)) (t : F) (ht : t ≠ 0) : (left s t).val 1 0 ≠ 0 := by
  intro hz
  apply hns
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨((s : F) + 1) / t, ?_⟩
  change t * (s : F) / ((s : F) + 1) * (t / ((s : F) + 1)) - 1 = 0 at hz
  field_simp at hz ⊢
  linear_combination hz

theorem closure_pair (s : Fˣ) (t : F) :
    Subgroup.closure ({left s t, right s t} : Set (SLTwo.SL2 F)) =
      Subgroup.closure ({SLTwo.tor s, left s t} : Set (SLTwo.SL2 F)) := by
  rw [right, closure_pair_inv_mul_left, Set.pair_comm]

theorem generates_of_matrix_criterion (s : Fˣ) (hs : (s : F) + 1 ≠ 0)
    (hns : ¬ IsSquare (s : F))
    (hgen : ∀ g : SLTwo.SL2 F, g.val 0 1 ≠ 0 → g.val 1 0 ≠ 0 →
      g.val 0 0 ≠ 0 ∨ g.val 1 1 ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, g} : Set (SLTwo.SL2 F)) = ⊤)
    (t : F) (ht : t ≠ 0) :
    Subgroup.closure ({left s t, right s t} : Set (SLTwo.SL2 F)) = ⊤ := by
  rw [closure_pair]
  exact hgen _ (by rw [left_upper_right]; exact one_ne_zero)
    (left_lower_left_ne_zero s hs hns t ht) (Or.inl (left_diagonal_ne_zero s hs t ht).1)

end Kourovka2135.SLTwoEqualTracePair
