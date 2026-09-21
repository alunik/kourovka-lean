import Kourovka2135.AbelianExtensionCocycle
import Mathlib.Algebra.Module.ZMod

/-! Construct the actual quotient action on an abelian extension kernel,
then its prime-field representation. The compatibility equation used by the
factor-set and Frattini theorems is proved from the extension itself.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.AbelianExtensionRepresentation

variable {J Q W : Type} [Group J] [Group Q] [AddCommGroup W]
variable (S : GroupExtension (Multiplicative W) J Q)

/-- Kernel elements act trivially on an abelian kernel by conjugation. -/
theorem kernel_le_conjAct_ker : S.rightHom.ker ≤ S.conjAct.ker := by
  intro j hj
  rw [← S.range_inl_eq_ker_rightHom] at hj
  obtain ⟨w, rfl⟩ := hj
  change S.conjAct (S.inl w) = 1
  apply MulEquiv.ext
  intro x
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  change S.inl w * S.inl x * (S.inl w)⁻¹ = S.inl x
  calc
    S.inl w * S.inl x * (S.inl w)⁻¹ = S.inl (w * x * w⁻¹) := by
      simp only [map_mul, map_inv]
    _ = S.inl x := by simp

/-- The actual conjugation action descends along the extension projection. -/
def quotientConjugation : Q →* MulAut (Multiplicative W) :=
  S.rightHom.liftOfRightInverse S.surjInvRightHom
    S.surjInvRightHom.rightInverse_rightHom
    ⟨S.conjAct, kernel_le_conjAct_ker S⟩

@[simp] theorem quotientConjugation_rightHom (j : J) :
    quotientConjugation S (S.rightHom j) = S.conjAct j :=
  S.rightHom.liftOfRightInverse_comp_apply S.surjInvRightHom
    S.surjInvRightHom.rightInverse_rightHom
    ⟨S.conjAct, kernel_le_conjAct_ker S⟩ j

/-- The actual automorphism written as an additive homomorphism on W. -/
def actionAddHom (q : Q) : W →+ W where
  toFun w := (quotientConjugation S q (Multiplicative.ofAdd w)).toAdd
  map_zero' := (quotientConjugation S q).map_one
  map_add' _ _ := (quotientConjugation S q).map_mul _ _

variable (p : ℕ) [Module (ZMod p) W]

/-- Every automorphism of a prime-field module's additive group is linear. -/
def representation : Representation (ZMod p) Q W where
  toFun q := (actionAddHom S q).toZModLinearMap p
  map_one' := by
    ext w
    change (quotientConjugation S 1 (Multiplicative.ofAdd w)).toAdd = w
    rw [map_one]
    rfl
  map_mul' a b := by
    ext w
    change (quotientConjugation S (a * b) (Multiplicative.ofAdd w)).toAdd =
      (quotientConjugation S a
        (quotientConjugation S b (Multiplicative.ofAdd w))).toAdd
    rw [map_mul]
    rfl

@[simp] theorem representation_rightHom (j : J) (w : W) :
    representation S p (S.rightHom j) w =
      (S.conjAct j (Multiplicative.ofAdd w)).toAdd := by
  change (quotientConjugation S (S.rightHom j) (Multiplicative.ofAdd w)).toAdd = _
  rw [quotientConjugation_rightHom]

/-- The factor-set theorem's compatibility input holds for the constructed
representation, with no action-identification assumption. -/
theorem compatibleAction :
    AbelianExtensionCocycle.CompatibleAction S (representation S p) := by
  intro j w
  change S.inl (Multiplicative.ofAdd (representation S p (S.rightHom j) w)) =
    j * S.inl (Multiplicative.ofAdd w) * j⁻¹
  rw [representation_rightHom]
  exact S.inl_conjAct_comm

end Kourovka2135.AbelianExtensionRepresentation
