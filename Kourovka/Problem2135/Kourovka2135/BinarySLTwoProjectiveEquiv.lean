import Kourovka2135.SLTwoUnipotent
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Algebra.CharP.Lemmas

/-! The actual characteristic-two SL2 group is its projective quotient.
The center is computed from Mathlib's scalar description and the equation
r squared equals one in a characteristic-two field.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinarySLTwoProjectiveEquiv

variable (F : Type*) [Field F] [CharP F 2]

theorem center_eq_bot : Subgroup.center (SLTwo.SL2 F) = ⊥ := by
  apply bot_unique
  intro A hA
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa only [Fintype.card_fin] using hr
  have hr1 : r = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hr2
  change A = 1
  apply Subtype.ext
  rw [← hscalar, hr1]
  simp

/-- The equivalence is the canonical projection, proved bijective. -/
def equiv : SLTwo.SL2 F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', center_eq_bot]),
      QuotientGroup.mk'_surjective _⟩

@[simp] theorem equiv_apply (g : SLTwo.SL2 F) :
    equiv F g = QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F)) g := rfl

end Kourovka2135.BinarySLTwoProjectiveEquiv
