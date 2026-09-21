import Kourovka2135.SuzukiEightMoore
import Kourovka2135.SuzukiRootCoordinates
import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

/-! A computable field with eight elements, using polynomial-bit codes for
F2[X]/(X^3+X+1). The element type is a new structure, so field arithmetic
cannot be confused with arithmetic modulo eight on Fin 8. All finite ring
and domain axioms are kernel-checked by literal cases and ordinary `decide +kernel`. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace Kourovka2135.SuzukiEightCodeField

/-- Three binary polynomial coefficients, carried by a distinct field type. -/
@[ext] structure Element where
  code : Fin 8
  deriving DecidableEq, Fintype, Repr

/-- Interpret a polynomial-bit code, not a natural-number field cast. -/
def ofCode (code : Fin 8) : Element := ⟨code⟩

def codeEquiv : Element ≃ Fin 8 where
  toFun := Element.code
  invFun := ofCode
  left_inv _ := rfl
  right_inv _ := rfl

theorem xor_lt_eight (a b : Fin 8) : Nat.xor a.val b.val < 8 := by
  exact Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt

/-- Addition is bitwise xor on the three polynomial coefficients. -/
def xorCode (a b : Fin 8) : Fin 8 :=
  ⟨Nat.xor a.val b.val, xor_lt_eight a b⟩

/-- The 64 multiplication entries, packed with three bits per entry. -/
def packedMultiplicationTable : ℕ := 2821848294356612419217921029917578219971947684264937521152

/-- Multiplication reduced modulo the binary polynomial with bits 1011. -/
def multiplicationTable (a b : Fin 8) : Fin 8 :=
  ⟨(Nat.shiftRight packedMultiplicationTable (3 * (8 * a.val + b.val))) % 8,
    Nat.mod_lt _ (by decide +kernel)⟩

instance : Zero Element := ⟨ofCode 0⟩
instance : One Element := ⟨ofCode 1⟩
instance : Add Element := ⟨fun a b => ofCode (xorCode a.code b.code)⟩
instance : Neg Element := ⟨id⟩
instance : Sub Element := ⟨fun a b => ofCode (xorCode a.code b.code)⟩
instance : Mul Element := ⟨fun a b => ofCode (multiplicationTable a.code b.code)⟩

private theorem add_assoc_cert (a b c : Element) : a + b + c = a + (b + c) := by
  apply Element.ext
  apply Fin.ext
  exact Nat.xor_assoc _ _ _

private theorem mul_comm_cert : ∀ a b : Element, a * b = b * a := by decide +kernel

private theorem mul_assoc_0_0 : ∀ c : Element, (ofCode 0) * (ofCode 0) * c = (ofCode 0) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_1 : ∀ c : Element, (ofCode 0) * (ofCode 1) * c = (ofCode 0) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_2 : ∀ c : Element, (ofCode 0) * (ofCode 2) * c = (ofCode 0) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_3 : ∀ c : Element, (ofCode 0) * (ofCode 3) * c = (ofCode 0) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_4 : ∀ c : Element, (ofCode 0) * (ofCode 4) * c = (ofCode 0) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_5 : ∀ c : Element, (ofCode 0) * (ofCode 5) * c = (ofCode 0) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_6 : ∀ c : Element, (ofCode 0) * (ofCode 6) * c = (ofCode 0) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_7 : ∀ c : Element, (ofCode 0) * (ofCode 7) * c = (ofCode 0) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code0 : ∀ b c : Element, (ofCode 0) * b * c = (ofCode 0) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_0_0
  · exact mul_assoc_0_1
  · exact mul_assoc_0_2
  · exact mul_assoc_0_3
  · exact mul_assoc_0_4
  · exact mul_assoc_0_5
  · exact mul_assoc_0_6
  · exact mul_assoc_0_7
private theorem mul_assoc_1_0 : ∀ c : Element, (ofCode 1) * (ofCode 0) * c = (ofCode 1) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_1 : ∀ c : Element, (ofCode 1) * (ofCode 1) * c = (ofCode 1) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_2 : ∀ c : Element, (ofCode 1) * (ofCode 2) * c = (ofCode 1) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_3 : ∀ c : Element, (ofCode 1) * (ofCode 3) * c = (ofCode 1) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_4 : ∀ c : Element, (ofCode 1) * (ofCode 4) * c = (ofCode 1) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_5 : ∀ c : Element, (ofCode 1) * (ofCode 5) * c = (ofCode 1) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_6 : ∀ c : Element, (ofCode 1) * (ofCode 6) * c = (ofCode 1) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_7 : ∀ c : Element, (ofCode 1) * (ofCode 7) * c = (ofCode 1) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code1 : ∀ b c : Element, (ofCode 1) * b * c = (ofCode 1) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_1_0
  · exact mul_assoc_1_1
  · exact mul_assoc_1_2
  · exact mul_assoc_1_3
  · exact mul_assoc_1_4
  · exact mul_assoc_1_5
  · exact mul_assoc_1_6
  · exact mul_assoc_1_7
private theorem mul_assoc_2_0 : ∀ c : Element, (ofCode 2) * (ofCode 0) * c = (ofCode 2) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_1 : ∀ c : Element, (ofCode 2) * (ofCode 1) * c = (ofCode 2) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_2 : ∀ c : Element, (ofCode 2) * (ofCode 2) * c = (ofCode 2) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_3 : ∀ c : Element, (ofCode 2) * (ofCode 3) * c = (ofCode 2) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_4 : ∀ c : Element, (ofCode 2) * (ofCode 4) * c = (ofCode 2) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_5 : ∀ c : Element, (ofCode 2) * (ofCode 5) * c = (ofCode 2) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_6 : ∀ c : Element, (ofCode 2) * (ofCode 6) * c = (ofCode 2) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_7 : ∀ c : Element, (ofCode 2) * (ofCode 7) * c = (ofCode 2) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code2 : ∀ b c : Element, (ofCode 2) * b * c = (ofCode 2) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_2_0
  · exact mul_assoc_2_1
  · exact mul_assoc_2_2
  · exact mul_assoc_2_3
  · exact mul_assoc_2_4
  · exact mul_assoc_2_5
  · exact mul_assoc_2_6
  · exact mul_assoc_2_7
private theorem mul_assoc_3_0 : ∀ c : Element, (ofCode 3) * (ofCode 0) * c = (ofCode 3) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_1 : ∀ c : Element, (ofCode 3) * (ofCode 1) * c = (ofCode 3) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_2 : ∀ c : Element, (ofCode 3) * (ofCode 2) * c = (ofCode 3) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_3 : ∀ c : Element, (ofCode 3) * (ofCode 3) * c = (ofCode 3) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_4 : ∀ c : Element, (ofCode 3) * (ofCode 4) * c = (ofCode 3) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_5 : ∀ c : Element, (ofCode 3) * (ofCode 5) * c = (ofCode 3) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_6 : ∀ c : Element, (ofCode 3) * (ofCode 6) * c = (ofCode 3) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_7 : ∀ c : Element, (ofCode 3) * (ofCode 7) * c = (ofCode 3) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code3 : ∀ b c : Element, (ofCode 3) * b * c = (ofCode 3) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_3_0
  · exact mul_assoc_3_1
  · exact mul_assoc_3_2
  · exact mul_assoc_3_3
  · exact mul_assoc_3_4
  · exact mul_assoc_3_5
  · exact mul_assoc_3_6
  · exact mul_assoc_3_7
private theorem mul_assoc_4_0 : ∀ c : Element, (ofCode 4) * (ofCode 0) * c = (ofCode 4) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_1 : ∀ c : Element, (ofCode 4) * (ofCode 1) * c = (ofCode 4) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_2 : ∀ c : Element, (ofCode 4) * (ofCode 2) * c = (ofCode 4) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_3 : ∀ c : Element, (ofCode 4) * (ofCode 3) * c = (ofCode 4) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_4 : ∀ c : Element, (ofCode 4) * (ofCode 4) * c = (ofCode 4) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_5 : ∀ c : Element, (ofCode 4) * (ofCode 5) * c = (ofCode 4) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_6 : ∀ c : Element, (ofCode 4) * (ofCode 6) * c = (ofCode 4) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_7 : ∀ c : Element, (ofCode 4) * (ofCode 7) * c = (ofCode 4) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code4 : ∀ b c : Element, (ofCode 4) * b * c = (ofCode 4) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_4_0
  · exact mul_assoc_4_1
  · exact mul_assoc_4_2
  · exact mul_assoc_4_3
  · exact mul_assoc_4_4
  · exact mul_assoc_4_5
  · exact mul_assoc_4_6
  · exact mul_assoc_4_7
private theorem mul_assoc_5_0 : ∀ c : Element, (ofCode 5) * (ofCode 0) * c = (ofCode 5) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_1 : ∀ c : Element, (ofCode 5) * (ofCode 1) * c = (ofCode 5) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_2 : ∀ c : Element, (ofCode 5) * (ofCode 2) * c = (ofCode 5) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_3 : ∀ c : Element, (ofCode 5) * (ofCode 3) * c = (ofCode 5) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_4 : ∀ c : Element, (ofCode 5) * (ofCode 4) * c = (ofCode 5) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_5 : ∀ c : Element, (ofCode 5) * (ofCode 5) * c = (ofCode 5) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_6 : ∀ c : Element, (ofCode 5) * (ofCode 6) * c = (ofCode 5) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_7 : ∀ c : Element, (ofCode 5) * (ofCode 7) * c = (ofCode 5) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code5 : ∀ b c : Element, (ofCode 5) * b * c = (ofCode 5) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_5_0
  · exact mul_assoc_5_1
  · exact mul_assoc_5_2
  · exact mul_assoc_5_3
  · exact mul_assoc_5_4
  · exact mul_assoc_5_5
  · exact mul_assoc_5_6
  · exact mul_assoc_5_7
private theorem mul_assoc_6_0 : ∀ c : Element, (ofCode 6) * (ofCode 0) * c = (ofCode 6) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_1 : ∀ c : Element, (ofCode 6) * (ofCode 1) * c = (ofCode 6) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_2 : ∀ c : Element, (ofCode 6) * (ofCode 2) * c = (ofCode 6) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_3 : ∀ c : Element, (ofCode 6) * (ofCode 3) * c = (ofCode 6) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_4 : ∀ c : Element, (ofCode 6) * (ofCode 4) * c = (ofCode 6) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_5 : ∀ c : Element, (ofCode 6) * (ofCode 5) * c = (ofCode 6) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_6 : ∀ c : Element, (ofCode 6) * (ofCode 6) * c = (ofCode 6) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_7 : ∀ c : Element, (ofCode 6) * (ofCode 7) * c = (ofCode 6) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code6 : ∀ b c : Element, (ofCode 6) * b * c = (ofCode 6) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_6_0
  · exact mul_assoc_6_1
  · exact mul_assoc_6_2
  · exact mul_assoc_6_3
  · exact mul_assoc_6_4
  · exact mul_assoc_6_5
  · exact mul_assoc_6_6
  · exact mul_assoc_6_7
private theorem mul_assoc_7_0 : ∀ c : Element, (ofCode 7) * (ofCode 0) * c = (ofCode 7) * ((ofCode 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_1 : ∀ c : Element, (ofCode 7) * (ofCode 1) * c = (ofCode 7) * ((ofCode 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_2 : ∀ c : Element, (ofCode 7) * (ofCode 2) * c = (ofCode 7) * ((ofCode 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_3 : ∀ c : Element, (ofCode 7) * (ofCode 3) * c = (ofCode 7) * ((ofCode 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_4 : ∀ c : Element, (ofCode 7) * (ofCode 4) * c = (ofCode 7) * ((ofCode 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_5 : ∀ c : Element, (ofCode 7) * (ofCode 5) * c = (ofCode 7) * ((ofCode 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_6 : ∀ c : Element, (ofCode 7) * (ofCode 6) * c = (ofCode 7) * ((ofCode 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_7 : ∀ c : Element, (ofCode 7) * (ofCode 7) * c = (ofCode 7) * ((ofCode 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_code7 : ∀ b c : Element, (ofCode 7) * b * c = (ofCode 7) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_7_0
  · exact mul_assoc_7_1
  · exact mul_assoc_7_2
  · exact mul_assoc_7_3
  · exact mul_assoc_7_4
  · exact mul_assoc_7_5
  · exact mul_assoc_7_6
  · exact mul_assoc_7_7

private theorem mul_assoc_cert : ∀ a b c : Element, a * b * c = a * (b * c) := by
  rintro ⟨a⟩
  fin_cases a
  · exact mul_assoc_code0
  · exact mul_assoc_code1
  · exact mul_assoc_code2
  · exact mul_assoc_code3
  · exact mul_assoc_code4
  · exact mul_assoc_code5
  · exact mul_assoc_code6
  · exact mul_assoc_code7


private theorem left_distrib_0_0 : ∀ c : Element, (ofCode 0) * ((ofCode 0) + c) = (ofCode 0) * (ofCode 0) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_1 : ∀ c : Element, (ofCode 0) * ((ofCode 1) + c) = (ofCode 0) * (ofCode 1) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_2 : ∀ c : Element, (ofCode 0) * ((ofCode 2) + c) = (ofCode 0) * (ofCode 2) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_3 : ∀ c : Element, (ofCode 0) * ((ofCode 3) + c) = (ofCode 0) * (ofCode 3) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_4 : ∀ c : Element, (ofCode 0) * ((ofCode 4) + c) = (ofCode 0) * (ofCode 4) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_5 : ∀ c : Element, (ofCode 0) * ((ofCode 5) + c) = (ofCode 0) * (ofCode 5) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_6 : ∀ c : Element, (ofCode 0) * ((ofCode 6) + c) = (ofCode 0) * (ofCode 6) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_0_7 : ∀ c : Element, (ofCode 0) * ((ofCode 7) + c) = (ofCode 0) * (ofCode 7) + (ofCode 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code0 : ∀ b c : Element, (ofCode 0) * (b + c) = (ofCode 0) * b + (ofCode 0) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_0_0
  · exact left_distrib_0_1
  · exact left_distrib_0_2
  · exact left_distrib_0_3
  · exact left_distrib_0_4
  · exact left_distrib_0_5
  · exact left_distrib_0_6
  · exact left_distrib_0_7
private theorem left_distrib_1_0 : ∀ c : Element, (ofCode 1) * ((ofCode 0) + c) = (ofCode 1) * (ofCode 0) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_1 : ∀ c : Element, (ofCode 1) * ((ofCode 1) + c) = (ofCode 1) * (ofCode 1) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_2 : ∀ c : Element, (ofCode 1) * ((ofCode 2) + c) = (ofCode 1) * (ofCode 2) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_3 : ∀ c : Element, (ofCode 1) * ((ofCode 3) + c) = (ofCode 1) * (ofCode 3) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_4 : ∀ c : Element, (ofCode 1) * ((ofCode 4) + c) = (ofCode 1) * (ofCode 4) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_5 : ∀ c : Element, (ofCode 1) * ((ofCode 5) + c) = (ofCode 1) * (ofCode 5) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_6 : ∀ c : Element, (ofCode 1) * ((ofCode 6) + c) = (ofCode 1) * (ofCode 6) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_1_7 : ∀ c : Element, (ofCode 1) * ((ofCode 7) + c) = (ofCode 1) * (ofCode 7) + (ofCode 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code1 : ∀ b c : Element, (ofCode 1) * (b + c) = (ofCode 1) * b + (ofCode 1) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_1_0
  · exact left_distrib_1_1
  · exact left_distrib_1_2
  · exact left_distrib_1_3
  · exact left_distrib_1_4
  · exact left_distrib_1_5
  · exact left_distrib_1_6
  · exact left_distrib_1_7
private theorem left_distrib_2_0 : ∀ c : Element, (ofCode 2) * ((ofCode 0) + c) = (ofCode 2) * (ofCode 0) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_1 : ∀ c : Element, (ofCode 2) * ((ofCode 1) + c) = (ofCode 2) * (ofCode 1) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_2 : ∀ c : Element, (ofCode 2) * ((ofCode 2) + c) = (ofCode 2) * (ofCode 2) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_3 : ∀ c : Element, (ofCode 2) * ((ofCode 3) + c) = (ofCode 2) * (ofCode 3) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_4 : ∀ c : Element, (ofCode 2) * ((ofCode 4) + c) = (ofCode 2) * (ofCode 4) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_5 : ∀ c : Element, (ofCode 2) * ((ofCode 5) + c) = (ofCode 2) * (ofCode 5) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_6 : ∀ c : Element, (ofCode 2) * ((ofCode 6) + c) = (ofCode 2) * (ofCode 6) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_2_7 : ∀ c : Element, (ofCode 2) * ((ofCode 7) + c) = (ofCode 2) * (ofCode 7) + (ofCode 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code2 : ∀ b c : Element, (ofCode 2) * (b + c) = (ofCode 2) * b + (ofCode 2) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_2_0
  · exact left_distrib_2_1
  · exact left_distrib_2_2
  · exact left_distrib_2_3
  · exact left_distrib_2_4
  · exact left_distrib_2_5
  · exact left_distrib_2_6
  · exact left_distrib_2_7
private theorem left_distrib_3_0 : ∀ c : Element, (ofCode 3) * ((ofCode 0) + c) = (ofCode 3) * (ofCode 0) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_1 : ∀ c : Element, (ofCode 3) * ((ofCode 1) + c) = (ofCode 3) * (ofCode 1) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_2 : ∀ c : Element, (ofCode 3) * ((ofCode 2) + c) = (ofCode 3) * (ofCode 2) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_3 : ∀ c : Element, (ofCode 3) * ((ofCode 3) + c) = (ofCode 3) * (ofCode 3) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_4 : ∀ c : Element, (ofCode 3) * ((ofCode 4) + c) = (ofCode 3) * (ofCode 4) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_5 : ∀ c : Element, (ofCode 3) * ((ofCode 5) + c) = (ofCode 3) * (ofCode 5) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_6 : ∀ c : Element, (ofCode 3) * ((ofCode 6) + c) = (ofCode 3) * (ofCode 6) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_3_7 : ∀ c : Element, (ofCode 3) * ((ofCode 7) + c) = (ofCode 3) * (ofCode 7) + (ofCode 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code3 : ∀ b c : Element, (ofCode 3) * (b + c) = (ofCode 3) * b + (ofCode 3) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_3_0
  · exact left_distrib_3_1
  · exact left_distrib_3_2
  · exact left_distrib_3_3
  · exact left_distrib_3_4
  · exact left_distrib_3_5
  · exact left_distrib_3_6
  · exact left_distrib_3_7
private theorem left_distrib_4_0 : ∀ c : Element, (ofCode 4) * ((ofCode 0) + c) = (ofCode 4) * (ofCode 0) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_1 : ∀ c : Element, (ofCode 4) * ((ofCode 1) + c) = (ofCode 4) * (ofCode 1) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_2 : ∀ c : Element, (ofCode 4) * ((ofCode 2) + c) = (ofCode 4) * (ofCode 2) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_3 : ∀ c : Element, (ofCode 4) * ((ofCode 3) + c) = (ofCode 4) * (ofCode 3) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_4 : ∀ c : Element, (ofCode 4) * ((ofCode 4) + c) = (ofCode 4) * (ofCode 4) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_5 : ∀ c : Element, (ofCode 4) * ((ofCode 5) + c) = (ofCode 4) * (ofCode 5) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_6 : ∀ c : Element, (ofCode 4) * ((ofCode 6) + c) = (ofCode 4) * (ofCode 6) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_4_7 : ∀ c : Element, (ofCode 4) * ((ofCode 7) + c) = (ofCode 4) * (ofCode 7) + (ofCode 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code4 : ∀ b c : Element, (ofCode 4) * (b + c) = (ofCode 4) * b + (ofCode 4) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_4_0
  · exact left_distrib_4_1
  · exact left_distrib_4_2
  · exact left_distrib_4_3
  · exact left_distrib_4_4
  · exact left_distrib_4_5
  · exact left_distrib_4_6
  · exact left_distrib_4_7
private theorem left_distrib_5_0 : ∀ c : Element, (ofCode 5) * ((ofCode 0) + c) = (ofCode 5) * (ofCode 0) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_1 : ∀ c : Element, (ofCode 5) * ((ofCode 1) + c) = (ofCode 5) * (ofCode 1) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_2 : ∀ c : Element, (ofCode 5) * ((ofCode 2) + c) = (ofCode 5) * (ofCode 2) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_3 : ∀ c : Element, (ofCode 5) * ((ofCode 3) + c) = (ofCode 5) * (ofCode 3) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_4 : ∀ c : Element, (ofCode 5) * ((ofCode 4) + c) = (ofCode 5) * (ofCode 4) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_5 : ∀ c : Element, (ofCode 5) * ((ofCode 5) + c) = (ofCode 5) * (ofCode 5) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_6 : ∀ c : Element, (ofCode 5) * ((ofCode 6) + c) = (ofCode 5) * (ofCode 6) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_5_7 : ∀ c : Element, (ofCode 5) * ((ofCode 7) + c) = (ofCode 5) * (ofCode 7) + (ofCode 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code5 : ∀ b c : Element, (ofCode 5) * (b + c) = (ofCode 5) * b + (ofCode 5) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_5_0
  · exact left_distrib_5_1
  · exact left_distrib_5_2
  · exact left_distrib_5_3
  · exact left_distrib_5_4
  · exact left_distrib_5_5
  · exact left_distrib_5_6
  · exact left_distrib_5_7
private theorem left_distrib_6_0 : ∀ c : Element, (ofCode 6) * ((ofCode 0) + c) = (ofCode 6) * (ofCode 0) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_1 : ∀ c : Element, (ofCode 6) * ((ofCode 1) + c) = (ofCode 6) * (ofCode 1) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_2 : ∀ c : Element, (ofCode 6) * ((ofCode 2) + c) = (ofCode 6) * (ofCode 2) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_3 : ∀ c : Element, (ofCode 6) * ((ofCode 3) + c) = (ofCode 6) * (ofCode 3) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_4 : ∀ c : Element, (ofCode 6) * ((ofCode 4) + c) = (ofCode 6) * (ofCode 4) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_5 : ∀ c : Element, (ofCode 6) * ((ofCode 5) + c) = (ofCode 6) * (ofCode 5) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_6 : ∀ c : Element, (ofCode 6) * ((ofCode 6) + c) = (ofCode 6) * (ofCode 6) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_6_7 : ∀ c : Element, (ofCode 6) * ((ofCode 7) + c) = (ofCode 6) * (ofCode 7) + (ofCode 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code6 : ∀ b c : Element, (ofCode 6) * (b + c) = (ofCode 6) * b + (ofCode 6) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_6_0
  · exact left_distrib_6_1
  · exact left_distrib_6_2
  · exact left_distrib_6_3
  · exact left_distrib_6_4
  · exact left_distrib_6_5
  · exact left_distrib_6_6
  · exact left_distrib_6_7
private theorem left_distrib_7_0 : ∀ c : Element, (ofCode 7) * ((ofCode 0) + c) = (ofCode 7) * (ofCode 0) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_1 : ∀ c : Element, (ofCode 7) * ((ofCode 1) + c) = (ofCode 7) * (ofCode 1) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_2 : ∀ c : Element, (ofCode 7) * ((ofCode 2) + c) = (ofCode 7) * (ofCode 2) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_3 : ∀ c : Element, (ofCode 7) * ((ofCode 3) + c) = (ofCode 7) * (ofCode 3) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_4 : ∀ c : Element, (ofCode 7) * ((ofCode 4) + c) = (ofCode 7) * (ofCode 4) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_5 : ∀ c : Element, (ofCode 7) * ((ofCode 5) + c) = (ofCode 7) * (ofCode 5) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_6 : ∀ c : Element, (ofCode 7) * ((ofCode 6) + c) = (ofCode 7) * (ofCode 6) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_7_7 : ∀ c : Element, (ofCode 7) * ((ofCode 7) + c) = (ofCode 7) * (ofCode 7) + (ofCode 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem left_distrib_code7 : ∀ b c : Element, (ofCode 7) * (b + c) = (ofCode 7) * b + (ofCode 7) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact left_distrib_7_0
  · exact left_distrib_7_1
  · exact left_distrib_7_2
  · exact left_distrib_7_3
  · exact left_distrib_7_4
  · exact left_distrib_7_5
  · exact left_distrib_7_6
  · exact left_distrib_7_7

private theorem left_distrib_cert : ∀ a b c : Element, a * (b + c) = a * b + a * c := by
  rintro ⟨a⟩
  fin_cases a
  · exact left_distrib_code0
  · exact left_distrib_code1
  · exact left_distrib_code2
  · exact left_distrib_code3
  · exact left_distrib_code4
  · exact left_distrib_code5
  · exact left_distrib_code6
  · exact left_distrib_code7


instance : CommRing Element where
  add_assoc := add_assoc_cert
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  add_comm := by decide +kernel
  neg_add_cancel := by decide +kernel
  mul_assoc := mul_assoc_cert
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  mul_comm := mul_comm_cert
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
  left_distrib := left_distrib_cert
  right_distrib := by
    intro a b c
    rw [mul_comm_cert (a + b) c, left_distrib_cert, mul_comm_cert c a, mul_comm_cert c b]
  nsmul := nsmulRec
  zsmul := zsmulRec


instance : Nontrivial Element := ⟨⟨0, 1, by decide +kernel⟩⟩

instance : NoZeroDivisors Element where
  eq_zero_or_eq_zero_of_mul_eq_zero := by decide +kernel

instance : IsDomain Element := NoZeroDivisors.to_isDomain Element

/-- The finite-domain construction supplies computable field division. -/
instance : Field Element := Fintype.fieldOfDomain Element


instance : CharP Element 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (by decide +kernel) (by decide +kernel)

@[simp] theorem code_ofCode (a : Fin 8) : (ofCode a).code = a := rfl
@[simp] theorem ofCode_code (a : Element) : ofCode a.code = a := rfl
@[simp] theorem code_zero : (0 : Element).code = 0 := rfl
@[simp] theorem code_one : (1 : Element).code = 1 := rfl
@[simp] theorem ofCode_zero : ofCode 0 = 0 := rfl
@[simp] theorem ofCode_one : ofCode 1 = 1 := rfl

theorem code_add (a b : Element) : (a + b).code = xorCode a.code b.code := rfl

theorem code_mul (a b : Element) : (a * b).code = multiplicationTable a.code b.code := rfl

theorem card_element : Fintype.card Element = 8 := by
  rw [Fintype.card_congr codeEquiv]
  exact Fintype.card_fin 8

theorem natCard_element : Nat.card Element = 8 := by
  rw [Nat.card_eq_fintype_card, card_element]

/-- The polynomial generator has code two. -/
def z : Element := ofCode 2

/-- The canonical matrix parameter has polynomial-bit code three. -/
def alpha : Element := ofCode 3

@[simp] theorem code_z : z.code = 2 := rfl
@[simp] theorem code_alpha : alpha.code = 3 := rfl

theorem z_cubic : z ^ 3 + z + 1 = 0 := by decide +kernel

theorem alpha_eq_z_cubed : alpha = z ^ 3 := by decide +kernel

theorem alpha_cubic : alpha ^ 3 + alpha ^ 2 + 1 = 0 := by decide +kernel

theorem alpha_ne_zero : alpha ≠ 0 := by decide +kernel

theorem alpha_ne_one : alpha ≠ 1 := by decide +kernel

/-- The code field is isomorphic to the actual Suzuki field at parameter one.
Only this transport is noncomputable; the code arithmetic remains computable. -/
noncomputable def actualEquiv : Element ≃+* SuzukiGeometry.K 1 := by
  let : Fintype (SuzukiGeometry.K 1) := Fintype.ofFinite (SuzukiGeometry.K 1)
  apply FiniteField.ringEquivOfCardEq
  rw [card_element, ← Nat.card_eq_fintype_card, SuzukiEightMoore.card_actual]

noncomputable def actualAlpha : SuzukiGeometry.K 1 := actualEquiv alpha

theorem actualAlpha_cubic : actualAlpha ^ 3 + actualAlpha ^ 2 + 1 = 0 := by
  have h := congrArg actualEquiv alpha_cubic
  simpa only [map_add, map_pow, map_one, map_zero, actualAlpha] using h

end Kourovka2135.SuzukiEightCodeField
