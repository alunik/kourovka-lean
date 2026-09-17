import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Kourovka.Problem2153.Field8

/-- The coefficients of `1, ω, ω²`, encoded by the constructor index in binary. -/
inductive F8 where
  | e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
  deriving DecidableEq

open F8

instance : Fintype F8 where
  elems := {e0, e1, e2, e3, e4, e5, e6, e7}
  complete x := by cases x <;> decide

def add : F8 → F8 → F8
  | e0, e0 => e0
  | e0, e1 => e1
  | e0, e2 => e2
  | e0, e3 => e3
  | e0, e4 => e4
  | e0, e5 => e5
  | e0, e6 => e6
  | e0, e7 => e7
  | e1, e0 => e1
  | e1, e1 => e0
  | e1, e2 => e3
  | e1, e3 => e2
  | e1, e4 => e5
  | e1, e5 => e4
  | e1, e6 => e7
  | e1, e7 => e6
  | e2, e0 => e2
  | e2, e1 => e3
  | e2, e2 => e0
  | e2, e3 => e1
  | e2, e4 => e6
  | e2, e5 => e7
  | e2, e6 => e4
  | e2, e7 => e5
  | e3, e0 => e3
  | e3, e1 => e2
  | e3, e2 => e1
  | e3, e3 => e0
  | e3, e4 => e7
  | e3, e5 => e6
  | e3, e6 => e5
  | e3, e7 => e4
  | e4, e0 => e4
  | e4, e1 => e5
  | e4, e2 => e6
  | e4, e3 => e7
  | e4, e4 => e0
  | e4, e5 => e1
  | e4, e6 => e2
  | e4, e7 => e3
  | e5, e0 => e5
  | e5, e1 => e4
  | e5, e2 => e7
  | e5, e3 => e6
  | e5, e4 => e1
  | e5, e5 => e0
  | e5, e6 => e3
  | e5, e7 => e2
  | e6, e0 => e6
  | e6, e1 => e7
  | e6, e2 => e4
  | e6, e3 => e5
  | e6, e4 => e2
  | e6, e5 => e3
  | e6, e6 => e0
  | e6, e7 => e1
  | e7, e0 => e7
  | e7, e1 => e6
  | e7, e2 => e5
  | e7, e3 => e4
  | e7, e4 => e3
  | e7, e5 => e2
  | e7, e6 => e1
  | e7, e7 => e0

def mul : F8 → F8 → F8
  | e0, e0 => e0
  | e0, e1 => e0
  | e0, e2 => e0
  | e0, e3 => e0
  | e0, e4 => e0
  | e0, e5 => e0
  | e0, e6 => e0
  | e0, e7 => e0
  | e1, e0 => e0
  | e1, e1 => e1
  | e1, e2 => e2
  | e1, e3 => e3
  | e1, e4 => e4
  | e1, e5 => e5
  | e1, e6 => e6
  | e1, e7 => e7
  | e2, e0 => e0
  | e2, e1 => e2
  | e2, e2 => e4
  | e2, e3 => e6
  | e2, e4 => e3
  | e2, e5 => e1
  | e2, e6 => e7
  | e2, e7 => e5
  | e3, e0 => e0
  | e3, e1 => e3
  | e3, e2 => e6
  | e3, e3 => e5
  | e3, e4 => e7
  | e3, e5 => e4
  | e3, e6 => e1
  | e3, e7 => e2
  | e4, e0 => e0
  | e4, e1 => e4
  | e4, e2 => e3
  | e4, e3 => e7
  | e4, e4 => e6
  | e4, e5 => e2
  | e4, e6 => e5
  | e4, e7 => e1
  | e5, e0 => e0
  | e5, e1 => e5
  | e5, e2 => e1
  | e5, e3 => e4
  | e5, e4 => e2
  | e5, e5 => e7
  | e5, e6 => e3
  | e5, e7 => e6
  | e6, e0 => e0
  | e6, e1 => e6
  | e6, e2 => e7
  | e6, e3 => e1
  | e6, e4 => e5
  | e6, e5 => e3
  | e6, e6 => e2
  | e6, e7 => e4
  | e7, e0 => e0
  | e7, e1 => e7
  | e7, e2 => e5
  | e7, e3 => e2
  | e7, e4 => e1
  | e7, e5 => e6
  | e7, e6 => e4
  | e7, e7 => e3

instance : Zero F8 := ⟨e0⟩
instance : One F8 := ⟨e1⟩
instance : Add F8 := ⟨add⟩
instance : Mul F8 := ⟨mul⟩
instance : Neg F8 := ⟨id⟩

instance : CommRing F8 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  neg_add_cancel := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Nontrivial F8 := ⟨⟨0, 1, by decide⟩⟩

def inv : F8 → F8
  | e0 => e0
  | e1 => e1
  | e2 => e5
  | e3 => e6
  | e4 => e7
  | e5 => e2
  | e6 => e3
  | e7 => e4

instance : Field F8 where
  inv := inv
  mul_inv_cancel := by decide
  inv_zero := rfl
  nnqsmul := _
  qsmul := _

instance : CharP F8 2 := (CharP.charP_iff_prime_eq_zero (by decide)).2 (by decide)

@[simp] theorem card : Fintype.card F8 = 8 := by decide

/-- Coefficient encoding: bit 0 is the constant term, bit 1 is ω, bit 2 is ω². -/
def code : F8 → Fin 8
  | e0 => 0 | e1 => 1 | e2 => 2 | e3 => 3
  | e4 => 4 | e5 => 5 | e6 => 6 | e7 => 7

def ofCode (i : Fin 8) : F8 := ![e0, e1, e2, e3, e4, e5, e6, e7] i

@[simp] theorem ofCode_code : ∀ a : F8, ofCode (code a) = a := by decide
@[simp] theorem code_ofCode : ∀ i : Fin 8, code (ofCode i) = i := by decide

def codeEquiv : F8 ≃ Fin 8 where
  toFun := code
  invFun := ofCode
  left_inv := ofCode_code
  right_inv := code_ofCode

def ω : F8 := e2

theorem omega_cubic : ω ^ 3 = ω + 1 := by decide
theorem omega_fourth : ω ^ 4 = ω ^ 2 + ω := by decide

/-- Four-dimensional matrix algebra over the certified eight-element field. -/
abbrev Mat := Matrix (Fin 4) (Fin 4) F8
abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) F8

/-- Standard central root elements in the Suzuki matrix model. -/
def z (t : F8) : Mat :=
  !![1, 0, 0, 0; 0, 1, 0, 0; t, 0, 1, 0; t ^ 4, t, 0, 1]

def T : Mat :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

def A : Mat := T * z 1 * T

theorem z_add : ∀ s t : F8, z (s + t) = z s * z t := by decide
theorem z_zero : z 0 = 1 := by decide
theorem z_injective : Function.Injective z := by decide
theorem z_square : ∀ t : F8, z t * z t = 1 := by decide
theorem T_square : T * T = 1 := by decide

def zUnit (t : F8) : GL4 := ⟨z t, z t, z_square t, z_square t⟩
def TUnit : GL4 := ⟨T, T, T_square, T_square⟩
def AUnit : GL4 := TUnit * zUnit 1 * TUnit

theorem zUnit_add (s t : F8) : zUnit (s + t) = zUnit s * zUnit t :=
  Units.ext (z_add s t)
theorem zUnit_zero : zUnit 0 = 1 := Units.ext z_zero
theorem zUnit_injective : Function.Injective zUnit := by
  intro s t h
  exact z_injective (congrArg Units.val h)

theorem A_square : A ^ 2 = 1 := by decide
theorem A_ne_one : A ≠ 1 := by decide
theorem z1_ne_one : z 1 ≠ 1 := by decide
theorem zw_ne_one : z ω ≠ 1 := by decide
theorem Az1_fifth : (A * z 1) ^ 5 = 1 := by decide
theorem Az1_ne_one : A * z 1 ≠ 1 := by decide
theorem Azw_seventh : (A * z ω) ^ 7 = 1 := by decide
theorem Azw_ne_one : A * z ω ≠ 1 := by decide

private theorem order_prime {M : Type*} [Monoid M] (g : M) (p : ℕ)
    (hp : p.Prime) (hpow : g ^ p = 1) (hne : g ≠ 1) : orderOf g = p := by
  let : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hpow hne

theorem order_A : orderOf A = 2 := order_prime A 2 (by decide) A_square A_ne_one
theorem order_z1 : orderOf (z 1) = 2 :=
  order_prime (z 1) 2 (by decide) (by decide) z1_ne_one
theorem order_zw : orderOf (z ω) = 2 :=
  order_prime (z ω) 2 (by decide) (by decide) zw_ne_one
theorem order_Az1 : orderOf (A * z 1) = 5 :=
  order_prime (A * z 1) 5 (by decide) Az1_fifth Az1_ne_one
theorem order_Azw : orderOf (A * z ω) = 7 :=
  order_prime (A * z ω) 7 (by decide) Azw_seventh Azw_ne_one

theorem order_AUnit : orderOf AUnit = 2 := by
  rw [← orderOf_units]
  exact order_A
theorem order_z1Unit : orderOf (zUnit 1) = 2 := by
  rw [← orderOf_units]
  exact order_z1
theorem order_zwUnit : orderOf (zUnit ω) = 2 := by
  rw [← orderOf_units]
  exact order_zw
theorem order_Az1Unit : orderOf (AUnit * zUnit 1) = 5 := by
  rw [← orderOf_units]
  exact order_Az1
theorem order_AzwUnit : orderOf (AUnit * zUnit ω) = 7 := by
  rw [← orderOf_units]
  exact order_Azw

theorem z1_ne_zw : zUnit 1 ≠ zUnit ω := by
  intro h
  have := zUnit_injective h
  exact (by decide : (1 : F8) ≠ ω) this

theorem TUnit_inv : TUnit⁻¹ = TUnit := Units.ext rfl

theorem AUnit_conjugate : AUnit = TUnit * zUnit 1 * TUnit⁻¹ := by
  rw [TUnit_inv]
  rfl

/-- Exact orders survive every faithful placement of these actual matrix units. -/
theorem faithful_orders {G : Type*} [Group G] (f : GL4 →* G)
    (hf : Function.Injective f) :
    orderOf (f AUnit) = 2 ∧ orderOf (f (zUnit 1)) = 2 ∧
    orderOf (f (zUnit ω)) = 2 ∧
    orderOf (f AUnit * f (zUnit 1)) = 5 ∧
    orderOf (f AUnit * f (zUnit ω)) = 7 := by
  simp only [← map_mul, orderOf_injective f hf]
  exact ⟨order_AUnit, order_z1Unit, order_zwUnit, order_Az1Unit, order_AzwUnit⟩

end Kourovka.Problem2153.Field8
