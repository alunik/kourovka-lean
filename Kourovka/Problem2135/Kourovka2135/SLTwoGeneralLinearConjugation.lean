import Kourovka2135.SLTwoUnipotent
import Kourovka2135.MatrixTwoSameTraceConjugacy

/-! Actual GL2 conjugation automorphisms of SL2, including the same-trace
nonscalar conjugacy consequence. The determinant of the conjugator is free. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoGeneralLinearConjugation
open Matrix
variable {F : Type*} [Field F]

def conjugate (C : Matrix.GeneralLinearGroup (Fin 2) F) (g : SLTwo.SL2 F) :
    SLTwo.SL2 F :=
  ⟨(C : Matrix (Fin 2) (Fin 2) F) * g.val *
    ((C⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
      rw [Matrix.det_mul, Matrix.det_mul, g.prop, mul_one, ← Matrix.det_mul,
        Units.mul_inv, Matrix.det_one]⟩

def automorphism (C : Matrix.GeneralLinearGroup (Fin 2) F) : MulAut (SLTwo.SL2 F) where
  toFun := conjugate C
  invFun := conjugate C⁻¹
  left_inv g := by
    apply Subtype.ext
    simp [conjugate, Matrix.mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [conjugate, Matrix.mul_assoc]
  map_mul' g h := by
    apply Subtype.ext
    change (↑C : Matrix (Fin 2) (Fin 2) F) * (g.val * h.val) *
        (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F) =
      ((↑C : Matrix (Fin 2) (Fin 2) F) * g.val * (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F)) *
      ((↑C : Matrix (Fin 2) (Fin 2) F) * h.val * (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F))
    simp [Matrix.mul_assoc]

theorem automorphism_val (C : Matrix.GeneralLinearGroup (Fin 2) F) (g : SLTwo.SL2 F) :
    (automorphism C g).val = (C : Matrix (Fin 2) (Fin 2) F) * g.val *
      ((C⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem trace_automorphism (C : Matrix.GeneralLinearGroup (Fin 2) F) (g : SLTwo.SL2 F) :
    (automorphism C g).val.trace = g.val.trace :=
  Matrix.trace_units_conj C g.val

theorem exists_automorphism_of_trace (g h : SLTwo.SL2 F)
    (hg : ¬ ∃ r : F, g.val = Matrix.scalar (Fin 2) r)
    (hh : ¬ ∃ r : F, h.val = Matrix.scalar (Fin 2) r)
    (htrace : g.val.trace = h.val.trace) :
    ∃ C : Matrix.GeneralLinearGroup (Fin 2) F, automorphism C g = h := by
  obtain ⟨C, hC⟩ := MatrixTwoSameTraceConjugacy.exists_conjugator g.val h.val hg hh
    htrace (g.prop.trans h.prop.symm)
  exact ⟨C, Subtype.ext hC⟩

end Kourovka2135.SLTwoGeneralLinearConjugation
