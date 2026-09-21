import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two

/-! A nondegenerate alternating binary vector space cannot have dimension three.
The determinant formula makes every symmetric zero-diagonal 3×3 binary
matrix singular. The passage from an arbitrary finite-dimensional space to
that identity uses its actual basis and nondegeneracy/determinant theorem.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryAlternatingThree

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem matrix_singular : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (∀ i, A i i = 0) → (∀ i j, A i j = A j i) → A.det = 0 := by
  intro A hd hs
  rw [Matrix.det_fin_three]
  simp only [hd, zero_mul, mul_zero, sub_zero, zero_add]
  rw [hs 2 0, hs 1 0, hs 2 1]
  convert CharTwo.add_self_eq_zero (A 0 1 * A 1 2 * A 0 2) using 1
  ring

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [FiniteDimensional (ZMod 2) V]

theorem finrank_ne_three (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hnd : ∀ x, (∀ y, β x y = 0) → x = 0) :
    Module.finrank (ZMod 2) V ≠ 3 := by
  classical
  intro hdim
  let b : Module.Basis (Fin 3) (ZMod 2) V :=
    (Module.finBasis (ZMod 2) V).reindex (finCongr hdim)
  have hs (x y : V) : β x y = β y x := by
    apply CharTwo.add_eq_zero.mp
    have h := hAlt (x + y)
    simpa only [map_add, LinearMap.add_apply, hAlt, zero_add, add_zero, add_comm] using h
  have hnondeg : LinearMap.BilinForm.Nondegenerate β :=
    ⟨hnd, fun x hx => hnd x (fun y => (hs x y).trans (hx y))⟩
  have hdet : (LinearMap.BilinForm.toMatrix b β).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnondeg
  apply hdet
  apply matrix_singular
  · intro i
    simpa only [LinearMap.BilinForm.toMatrix_apply] using hAlt (b i)
  · intro i j
    simpa only [LinearMap.BilinForm.toMatrix_apply] using hs (b i) (b j)

end Kourovka2135.BinaryAlternatingThree
