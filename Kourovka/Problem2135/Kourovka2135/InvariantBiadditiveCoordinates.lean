import Kourovka2135.ScalarInvariantBiadditive

/-! Transport the scalar-invariance obstruction through actual additive
coordinate equivalences. The actions and their coordinate formulas remain
explicit inputs, so this lemma makes no group-model identification. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.InvariantBiadditiveCoordinates

variable {F D E A : Type*} [Field F] [AddCommGroup D] [AddCommGroup E] [AddCommGroup A]

/-- Precompose both inputs of an actual biadditive map. -/
def reindex (d : D ≃+ F) (e : E ≃+ F) (B : D →+ (E →+ A)) : F →+ (F →+ A) where
  toFun x := (B (d.symm x)).comp e.symm.toAddMonoidHom
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

@[simp] theorem reindex_apply (d : D ≃+ F) (e : E ≃+ F) (B : D →+ (E →+ A))
    (x y : F) : reindex d e B x y = B (d.symm x) (e.symm y) := rfl

/-- Scalar coordinate formulas and a concrete nonadditivity obstruction
annihilate the original form, with no dimension or semisimplicity hypothesis. -/
theorem eq_zero (n : ℕ) (hn : 0 < n)
    (hbad : ¬ ∀ x y : F, ((x + y) ^ n)⁻¹ = (x ^ n)⁻¹ + (y ^ n)⁻¹)
    (d : D ≃+ F) (e : E ≃+ F) (alpha : Fˣ → D → D) (beta : Fˣ → E → E)
    (hd : ∀ u x, d (alpha u x) = (u : F) ^ n * d x)
    (he : ∀ u y, e (beta u y) = (u : F) * e y)
    (B : D →+ (E →+ A)) (hB : ∀ u x y, B (alpha u x) (beta u y) = B x y) : B = 0 := by
  have hC : reindex d e B = 0 := by
    apply ScalarInvariantBiadditive.eq_zero_of_not_additive n hn hbad
    intro u x y
    have hdx : d.symm ((u : F) ^ n * x) = alpha u (d.symm x) := by
      apply d.injective
      rw [d.apply_symm_apply, hd, d.apply_symm_apply]
    have hey : e.symm ((u : F) * y) = beta u (e.symm y) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    simp only [reindex_apply, hdx, hey]
    exact hB u (d.symm x) (e.symm y)
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  have h := congrArg (fun C : F →+ (F →+ A) => C (d x) (e y)) hC
  simpa only [reindex_apply, d.symm_apply_apply, e.symm_apply_apply,
    AddMonoidHom.zero_apply] using h

end Kourovka2135.InvariantBiadditiveCoordinates
