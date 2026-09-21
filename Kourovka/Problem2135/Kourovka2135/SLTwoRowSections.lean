import Kourovka2135.SLTwoHomogeneousFunctions

/-! Explicit sections for the second-row map SL2 → nonzero vectors.

The fibers are left upper-unipotent cosets. These concrete facts implement
the homogeneous-function embedding without assuming Frobenius reciprocity.
-/

set_option autoImplicit false
noncomputable section
universe v

namespace Kourovka2135.SLTwoRowSections

open SLTwoHomogeneousFunctions

variable {F : Type v} [Field F]

/-- A determinant-one matrix with the prescribed nonzero second row. -/
def rowSection (z : Point F) : SLTwo.SL2 F := by
  classical
  exact if hz : z.val 0 = 0 then
    SLTwo.tor ((Units.mk0 (z.val 1) (second_ne_zero_of_first_eq_zero z hz))⁻¹)
  else
    ⟨!![0, -(z.val 0)⁻¹; z.val 0, z.val 1], by simp [Matrix.det_fin_two_of, hz]⟩

/-- The explicit matrix really has the requested second row. -/
theorem rowSection_point (z : Point F) :
    pointAction (rowSection z) (infinity F) = z := by
  classical
  apply Subtype.ext
  funext i
  by_cases hz : z.val 0 = 0 <;> fin_cases i <;>
    simp [rowSection, hz, pointAction, infinity, SLTwo.tor_val]

/-- A determinant-one matrix fixing the second standard row is upper unipotent. -/
theorem eq_uni_of_point_infinity (g : SLTwo.SL2 F)
    (hg : pointAction g (infinity F) = infinity F) :
    g = SLTwo.uni (g.val 0 1) := by
  have h0 := congrArg (fun z : Point F => z.val 0) hg
  have h1 := congrArg (fun z : Point F => z.val 1) hg
  have h10 : g.val 1 0 = 0 := by
    simpa [pointAction, infinity, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  have h11 : g.val 1 1 = 1 := by
    simpa [pointAction, infinity, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h1
  have h00 : g.val 0 0 = 1 := by
    have hd := g.property
    change g.val.det = 1 at hd
    rw [Matrix.det_fin_two, h10, h11, mul_one, mul_zero, sub_zero] at hd
    exact hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SLTwo.uni_val, h00, h10, h11]

/-- Equal nonzero second rows differ by left multiplication by a genuine unipotent. -/
theorem exists_uni_mul_of_point_eq (g h : SLTwo.SL2 F)
    (hgh : pointAction g (infinity F) = pointAction h (infinity F)) :
    ∃ t : F, g = SLTwo.uni t * h := by
  have hinf : pointAction (g * h⁻¹) (infinity F) = infinity F := by
    rw [pointAction_mul, hgh, ← pointAction_mul, mul_inv_cancel, pointAction_one]
  refine ⟨(g * h⁻¹).val 0 1, ?_⟩
  have hmul := congrArg (fun x : SLTwo.SL2 F => x * h)
    (eq_uni_of_point_infinity (g * h⁻¹) hinf)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

/-- Any matrix differs from the canonical matrix for its row by a left unipotent. -/
theorem exists_uni_mul_rowSection (g : SLTwo.SL2 F) :
    ∃ t : F, g = SLTwo.uni t * rowSection (pointAction g (infinity F)) :=
  exists_uni_mul_of_point_eq g _ (rowSection_point _).symm

/-- Left multiplication by the inverse torus parameter scales the second row forward. -/
theorem point_torus_mul (a : Fˣ) (g : SLTwo.SL2 F) :
    pointAction (SLTwo.tor a⁻¹ * g) (infinity F) =
      scalePoint a (pointAction g (infinity F)) := by
  rw [pointAction_mul, pointAction_tor_infinity, inv_inv, pointAction_scale]

end Kourovka2135.SLTwoRowSections
