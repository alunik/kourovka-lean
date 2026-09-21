import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-! A concrete field with sixteen elements. Polynomial-basis bits use the
modulus X^4+X+1. Every field axiom is checked by literal-case kernel reduction;
the finite table is data, not an assumed algebraic or classification theorem.
The `ofBits` constructor is distinct from natural-number casting. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Kourovka2135.BinaryFieldSixteen

/-- Four polynomial-basis bits. The wrapper prevents accidental arithmetic modulo sixteen. -/
structure K where
  bits : Fin 16
  deriving DecidableEq, Fintype

/-- Decode polynomial-basis bits; this is not a natural-number field cast. -/
def ofBits (n : ℕ) : K := ⟨⟨n % 16, Nat.mod_lt _ (by decide +kernel)⟩⟩

private def packedMulTable : ℕ := 116196760129267793630862849262464326346044543732748708940920453221664288556434379745879494961270582141731748813355742142288220638766218855867759359510984593843506004200114943278699875244065120512813025380665946106619127097398772031257643617143689515450995722003729973585221105779229319991106539050771048038400
private def packedInvTable : ℕ := 9460475325918865680

private def mulTable (a b : Fin 16) : Fin 16 :=
  ⟨(Nat.shiftRight packedMulTable (4 * (16 * a.val + b.val))) % 16,
    Nat.mod_lt _ (by decide +kernel)⟩
private def invTable (a : Fin 16) : Fin 16 :=
  ⟨(Nat.shiftRight packedInvTable (4 * a.val)) % 16,
    Nat.mod_lt _ (by decide +kernel)⟩

instance : Zero K := ⟨ofBits 0⟩
instance : One K := ⟨ofBits 1⟩
instance : Add K := ⟨fun a b => ofBits (Nat.xor a.bits.val b.bits.val)⟩
instance : Neg K := ⟨id⟩
instance : Mul K := ⟨fun a b => ⟨mulTable a.bits b.bits⟩⟩
instance : Inv K := ⟨fun a => ⟨invTable a.bits⟩⟩

private theorem bits_injective : Function.Injective (fun a : K => a.bits.val) := by
  rintro ⟨a⟩ ⟨b⟩ h
  congr 1
  exact Fin.ext h

private theorem bits_add (a b : K) :
    (a + b).bits.val = Nat.xor a.bits.val b.bits.val := by
  change (Nat.xor a.bits.val b.bits.val) % 16 = _
  apply Nat.mod_eq_of_lt
  exact Nat.xor_lt_two_pow (n := 4) a.bits.isLt b.bits.isLt

private theorem add_assoc_cert (a b c : K) : a + b + c = a + (b + c) := by
  apply bits_injective
  simp only [bits_add]
  exact Nat.xor_assoc _ _ _

private theorem zero_add_cert : ∀ a : K, 0 + a = a := by decide +kernel
private theorem neg_add_cert : ∀ a : K, -a + a = 0 := by decide +kernel
private theorem mul_assoc_0_0 : ∀ c : K, (ofBits 0) * (ofBits 0) * c = (ofBits 0) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_1 : ∀ c : K, (ofBits 0) * (ofBits 1) * c = (ofBits 0) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_2 : ∀ c : K, (ofBits 0) * (ofBits 2) * c = (ofBits 0) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_3 : ∀ c : K, (ofBits 0) * (ofBits 3) * c = (ofBits 0) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_4 : ∀ c : K, (ofBits 0) * (ofBits 4) * c = (ofBits 0) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_5 : ∀ c : K, (ofBits 0) * (ofBits 5) * c = (ofBits 0) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_6 : ∀ c : K, (ofBits 0) * (ofBits 6) * c = (ofBits 0) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_7 : ∀ c : K, (ofBits 0) * (ofBits 7) * c = (ofBits 0) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_8 : ∀ c : K, (ofBits 0) * (ofBits 8) * c = (ofBits 0) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_9 : ∀ c : K, (ofBits 0) * (ofBits 9) * c = (ofBits 0) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_10 : ∀ c : K, (ofBits 0) * (ofBits 10) * c = (ofBits 0) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_11 : ∀ c : K, (ofBits 0) * (ofBits 11) * c = (ofBits 0) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_12 : ∀ c : K, (ofBits 0) * (ofBits 12) * c = (ofBits 0) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_13 : ∀ c : K, (ofBits 0) * (ofBits 13) * c = (ofBits 0) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_14 : ∀ c : K, (ofBits 0) * (ofBits 14) * c = (ofBits 0) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_0_15 : ∀ c : K, (ofBits 0) * (ofBits 15) * c = (ofBits 0) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits0 : ∀ b c : K, (ofBits 0) * b * c = (ofBits 0) * (b * c) := by
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
  · exact mul_assoc_0_8
  · exact mul_assoc_0_9
  · exact mul_assoc_0_10
  · exact mul_assoc_0_11
  · exact mul_assoc_0_12
  · exact mul_assoc_0_13
  · exact mul_assoc_0_14
  · exact mul_assoc_0_15

private theorem mul_assoc_1_0 : ∀ c : K, (ofBits 1) * (ofBits 0) * c = (ofBits 1) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_1 : ∀ c : K, (ofBits 1) * (ofBits 1) * c = (ofBits 1) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_2 : ∀ c : K, (ofBits 1) * (ofBits 2) * c = (ofBits 1) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_3 : ∀ c : K, (ofBits 1) * (ofBits 3) * c = (ofBits 1) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_4 : ∀ c : K, (ofBits 1) * (ofBits 4) * c = (ofBits 1) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_5 : ∀ c : K, (ofBits 1) * (ofBits 5) * c = (ofBits 1) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_6 : ∀ c : K, (ofBits 1) * (ofBits 6) * c = (ofBits 1) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_7 : ∀ c : K, (ofBits 1) * (ofBits 7) * c = (ofBits 1) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_8 : ∀ c : K, (ofBits 1) * (ofBits 8) * c = (ofBits 1) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_9 : ∀ c : K, (ofBits 1) * (ofBits 9) * c = (ofBits 1) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_10 : ∀ c : K, (ofBits 1) * (ofBits 10) * c = (ofBits 1) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_11 : ∀ c : K, (ofBits 1) * (ofBits 11) * c = (ofBits 1) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_12 : ∀ c : K, (ofBits 1) * (ofBits 12) * c = (ofBits 1) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_13 : ∀ c : K, (ofBits 1) * (ofBits 13) * c = (ofBits 1) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_14 : ∀ c : K, (ofBits 1) * (ofBits 14) * c = (ofBits 1) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_1_15 : ∀ c : K, (ofBits 1) * (ofBits 15) * c = (ofBits 1) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits1 : ∀ b c : K, (ofBits 1) * b * c = (ofBits 1) * (b * c) := by
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
  · exact mul_assoc_1_8
  · exact mul_assoc_1_9
  · exact mul_assoc_1_10
  · exact mul_assoc_1_11
  · exact mul_assoc_1_12
  · exact mul_assoc_1_13
  · exact mul_assoc_1_14
  · exact mul_assoc_1_15

private theorem mul_assoc_2_0 : ∀ c : K, (ofBits 2) * (ofBits 0) * c = (ofBits 2) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_1 : ∀ c : K, (ofBits 2) * (ofBits 1) * c = (ofBits 2) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_2 : ∀ c : K, (ofBits 2) * (ofBits 2) * c = (ofBits 2) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_3 : ∀ c : K, (ofBits 2) * (ofBits 3) * c = (ofBits 2) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_4 : ∀ c : K, (ofBits 2) * (ofBits 4) * c = (ofBits 2) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_5 : ∀ c : K, (ofBits 2) * (ofBits 5) * c = (ofBits 2) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_6 : ∀ c : K, (ofBits 2) * (ofBits 6) * c = (ofBits 2) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_7 : ∀ c : K, (ofBits 2) * (ofBits 7) * c = (ofBits 2) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_8 : ∀ c : K, (ofBits 2) * (ofBits 8) * c = (ofBits 2) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_9 : ∀ c : K, (ofBits 2) * (ofBits 9) * c = (ofBits 2) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_10 : ∀ c : K, (ofBits 2) * (ofBits 10) * c = (ofBits 2) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_11 : ∀ c : K, (ofBits 2) * (ofBits 11) * c = (ofBits 2) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_12 : ∀ c : K, (ofBits 2) * (ofBits 12) * c = (ofBits 2) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_13 : ∀ c : K, (ofBits 2) * (ofBits 13) * c = (ofBits 2) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_14 : ∀ c : K, (ofBits 2) * (ofBits 14) * c = (ofBits 2) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_2_15 : ∀ c : K, (ofBits 2) * (ofBits 15) * c = (ofBits 2) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits2 : ∀ b c : K, (ofBits 2) * b * c = (ofBits 2) * (b * c) := by
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
  · exact mul_assoc_2_8
  · exact mul_assoc_2_9
  · exact mul_assoc_2_10
  · exact mul_assoc_2_11
  · exact mul_assoc_2_12
  · exact mul_assoc_2_13
  · exact mul_assoc_2_14
  · exact mul_assoc_2_15

private theorem mul_assoc_3_0 : ∀ c : K, (ofBits 3) * (ofBits 0) * c = (ofBits 3) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_1 : ∀ c : K, (ofBits 3) * (ofBits 1) * c = (ofBits 3) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_2 : ∀ c : K, (ofBits 3) * (ofBits 2) * c = (ofBits 3) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_3 : ∀ c : K, (ofBits 3) * (ofBits 3) * c = (ofBits 3) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_4 : ∀ c : K, (ofBits 3) * (ofBits 4) * c = (ofBits 3) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_5 : ∀ c : K, (ofBits 3) * (ofBits 5) * c = (ofBits 3) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_6 : ∀ c : K, (ofBits 3) * (ofBits 6) * c = (ofBits 3) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_7 : ∀ c : K, (ofBits 3) * (ofBits 7) * c = (ofBits 3) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_8 : ∀ c : K, (ofBits 3) * (ofBits 8) * c = (ofBits 3) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_9 : ∀ c : K, (ofBits 3) * (ofBits 9) * c = (ofBits 3) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_10 : ∀ c : K, (ofBits 3) * (ofBits 10) * c = (ofBits 3) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_11 : ∀ c : K, (ofBits 3) * (ofBits 11) * c = (ofBits 3) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_12 : ∀ c : K, (ofBits 3) * (ofBits 12) * c = (ofBits 3) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_13 : ∀ c : K, (ofBits 3) * (ofBits 13) * c = (ofBits 3) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_14 : ∀ c : K, (ofBits 3) * (ofBits 14) * c = (ofBits 3) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_3_15 : ∀ c : K, (ofBits 3) * (ofBits 15) * c = (ofBits 3) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits3 : ∀ b c : K, (ofBits 3) * b * c = (ofBits 3) * (b * c) := by
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
  · exact mul_assoc_3_8
  · exact mul_assoc_3_9
  · exact mul_assoc_3_10
  · exact mul_assoc_3_11
  · exact mul_assoc_3_12
  · exact mul_assoc_3_13
  · exact mul_assoc_3_14
  · exact mul_assoc_3_15

private theorem mul_assoc_4_0 : ∀ c : K, (ofBits 4) * (ofBits 0) * c = (ofBits 4) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_1 : ∀ c : K, (ofBits 4) * (ofBits 1) * c = (ofBits 4) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_2 : ∀ c : K, (ofBits 4) * (ofBits 2) * c = (ofBits 4) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_3 : ∀ c : K, (ofBits 4) * (ofBits 3) * c = (ofBits 4) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_4 : ∀ c : K, (ofBits 4) * (ofBits 4) * c = (ofBits 4) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_5 : ∀ c : K, (ofBits 4) * (ofBits 5) * c = (ofBits 4) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_6 : ∀ c : K, (ofBits 4) * (ofBits 6) * c = (ofBits 4) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_7 : ∀ c : K, (ofBits 4) * (ofBits 7) * c = (ofBits 4) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_8 : ∀ c : K, (ofBits 4) * (ofBits 8) * c = (ofBits 4) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_9 : ∀ c : K, (ofBits 4) * (ofBits 9) * c = (ofBits 4) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_10 : ∀ c : K, (ofBits 4) * (ofBits 10) * c = (ofBits 4) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_11 : ∀ c : K, (ofBits 4) * (ofBits 11) * c = (ofBits 4) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_12 : ∀ c : K, (ofBits 4) * (ofBits 12) * c = (ofBits 4) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_13 : ∀ c : K, (ofBits 4) * (ofBits 13) * c = (ofBits 4) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_14 : ∀ c : K, (ofBits 4) * (ofBits 14) * c = (ofBits 4) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_4_15 : ∀ c : K, (ofBits 4) * (ofBits 15) * c = (ofBits 4) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits4 : ∀ b c : K, (ofBits 4) * b * c = (ofBits 4) * (b * c) := by
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
  · exact mul_assoc_4_8
  · exact mul_assoc_4_9
  · exact mul_assoc_4_10
  · exact mul_assoc_4_11
  · exact mul_assoc_4_12
  · exact mul_assoc_4_13
  · exact mul_assoc_4_14
  · exact mul_assoc_4_15

private theorem mul_assoc_5_0 : ∀ c : K, (ofBits 5) * (ofBits 0) * c = (ofBits 5) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_1 : ∀ c : K, (ofBits 5) * (ofBits 1) * c = (ofBits 5) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_2 : ∀ c : K, (ofBits 5) * (ofBits 2) * c = (ofBits 5) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_3 : ∀ c : K, (ofBits 5) * (ofBits 3) * c = (ofBits 5) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_4 : ∀ c : K, (ofBits 5) * (ofBits 4) * c = (ofBits 5) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_5 : ∀ c : K, (ofBits 5) * (ofBits 5) * c = (ofBits 5) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_6 : ∀ c : K, (ofBits 5) * (ofBits 6) * c = (ofBits 5) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_7 : ∀ c : K, (ofBits 5) * (ofBits 7) * c = (ofBits 5) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_8 : ∀ c : K, (ofBits 5) * (ofBits 8) * c = (ofBits 5) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_9 : ∀ c : K, (ofBits 5) * (ofBits 9) * c = (ofBits 5) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_10 : ∀ c : K, (ofBits 5) * (ofBits 10) * c = (ofBits 5) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_11 : ∀ c : K, (ofBits 5) * (ofBits 11) * c = (ofBits 5) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_12 : ∀ c : K, (ofBits 5) * (ofBits 12) * c = (ofBits 5) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_13 : ∀ c : K, (ofBits 5) * (ofBits 13) * c = (ofBits 5) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_14 : ∀ c : K, (ofBits 5) * (ofBits 14) * c = (ofBits 5) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_5_15 : ∀ c : K, (ofBits 5) * (ofBits 15) * c = (ofBits 5) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits5 : ∀ b c : K, (ofBits 5) * b * c = (ofBits 5) * (b * c) := by
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
  · exact mul_assoc_5_8
  · exact mul_assoc_5_9
  · exact mul_assoc_5_10
  · exact mul_assoc_5_11
  · exact mul_assoc_5_12
  · exact mul_assoc_5_13
  · exact mul_assoc_5_14
  · exact mul_assoc_5_15

private theorem mul_assoc_6_0 : ∀ c : K, (ofBits 6) * (ofBits 0) * c = (ofBits 6) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_1 : ∀ c : K, (ofBits 6) * (ofBits 1) * c = (ofBits 6) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_2 : ∀ c : K, (ofBits 6) * (ofBits 2) * c = (ofBits 6) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_3 : ∀ c : K, (ofBits 6) * (ofBits 3) * c = (ofBits 6) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_4 : ∀ c : K, (ofBits 6) * (ofBits 4) * c = (ofBits 6) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_5 : ∀ c : K, (ofBits 6) * (ofBits 5) * c = (ofBits 6) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_6 : ∀ c : K, (ofBits 6) * (ofBits 6) * c = (ofBits 6) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_7 : ∀ c : K, (ofBits 6) * (ofBits 7) * c = (ofBits 6) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_8 : ∀ c : K, (ofBits 6) * (ofBits 8) * c = (ofBits 6) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_9 : ∀ c : K, (ofBits 6) * (ofBits 9) * c = (ofBits 6) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_10 : ∀ c : K, (ofBits 6) * (ofBits 10) * c = (ofBits 6) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_11 : ∀ c : K, (ofBits 6) * (ofBits 11) * c = (ofBits 6) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_12 : ∀ c : K, (ofBits 6) * (ofBits 12) * c = (ofBits 6) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_13 : ∀ c : K, (ofBits 6) * (ofBits 13) * c = (ofBits 6) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_14 : ∀ c : K, (ofBits 6) * (ofBits 14) * c = (ofBits 6) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_6_15 : ∀ c : K, (ofBits 6) * (ofBits 15) * c = (ofBits 6) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits6 : ∀ b c : K, (ofBits 6) * b * c = (ofBits 6) * (b * c) := by
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
  · exact mul_assoc_6_8
  · exact mul_assoc_6_9
  · exact mul_assoc_6_10
  · exact mul_assoc_6_11
  · exact mul_assoc_6_12
  · exact mul_assoc_6_13
  · exact mul_assoc_6_14
  · exact mul_assoc_6_15

private theorem mul_assoc_7_0 : ∀ c : K, (ofBits 7) * (ofBits 0) * c = (ofBits 7) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_1 : ∀ c : K, (ofBits 7) * (ofBits 1) * c = (ofBits 7) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_2 : ∀ c : K, (ofBits 7) * (ofBits 2) * c = (ofBits 7) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_3 : ∀ c : K, (ofBits 7) * (ofBits 3) * c = (ofBits 7) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_4 : ∀ c : K, (ofBits 7) * (ofBits 4) * c = (ofBits 7) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_5 : ∀ c : K, (ofBits 7) * (ofBits 5) * c = (ofBits 7) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_6 : ∀ c : K, (ofBits 7) * (ofBits 6) * c = (ofBits 7) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_7 : ∀ c : K, (ofBits 7) * (ofBits 7) * c = (ofBits 7) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_8 : ∀ c : K, (ofBits 7) * (ofBits 8) * c = (ofBits 7) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_9 : ∀ c : K, (ofBits 7) * (ofBits 9) * c = (ofBits 7) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_10 : ∀ c : K, (ofBits 7) * (ofBits 10) * c = (ofBits 7) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_11 : ∀ c : K, (ofBits 7) * (ofBits 11) * c = (ofBits 7) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_12 : ∀ c : K, (ofBits 7) * (ofBits 12) * c = (ofBits 7) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_13 : ∀ c : K, (ofBits 7) * (ofBits 13) * c = (ofBits 7) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_14 : ∀ c : K, (ofBits 7) * (ofBits 14) * c = (ofBits 7) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_7_15 : ∀ c : K, (ofBits 7) * (ofBits 15) * c = (ofBits 7) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits7 : ∀ b c : K, (ofBits 7) * b * c = (ofBits 7) * (b * c) := by
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
  · exact mul_assoc_7_8
  · exact mul_assoc_7_9
  · exact mul_assoc_7_10
  · exact mul_assoc_7_11
  · exact mul_assoc_7_12
  · exact mul_assoc_7_13
  · exact mul_assoc_7_14
  · exact mul_assoc_7_15

private theorem mul_assoc_8_0 : ∀ c : K, (ofBits 8) * (ofBits 0) * c = (ofBits 8) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_1 : ∀ c : K, (ofBits 8) * (ofBits 1) * c = (ofBits 8) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_2 : ∀ c : K, (ofBits 8) * (ofBits 2) * c = (ofBits 8) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_3 : ∀ c : K, (ofBits 8) * (ofBits 3) * c = (ofBits 8) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_4 : ∀ c : K, (ofBits 8) * (ofBits 4) * c = (ofBits 8) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_5 : ∀ c : K, (ofBits 8) * (ofBits 5) * c = (ofBits 8) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_6 : ∀ c : K, (ofBits 8) * (ofBits 6) * c = (ofBits 8) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_7 : ∀ c : K, (ofBits 8) * (ofBits 7) * c = (ofBits 8) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_8 : ∀ c : K, (ofBits 8) * (ofBits 8) * c = (ofBits 8) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_9 : ∀ c : K, (ofBits 8) * (ofBits 9) * c = (ofBits 8) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_10 : ∀ c : K, (ofBits 8) * (ofBits 10) * c = (ofBits 8) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_11 : ∀ c : K, (ofBits 8) * (ofBits 11) * c = (ofBits 8) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_12 : ∀ c : K, (ofBits 8) * (ofBits 12) * c = (ofBits 8) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_13 : ∀ c : K, (ofBits 8) * (ofBits 13) * c = (ofBits 8) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_14 : ∀ c : K, (ofBits 8) * (ofBits 14) * c = (ofBits 8) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_8_15 : ∀ c : K, (ofBits 8) * (ofBits 15) * c = (ofBits 8) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits8 : ∀ b c : K, (ofBits 8) * b * c = (ofBits 8) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_8_0
  · exact mul_assoc_8_1
  · exact mul_assoc_8_2
  · exact mul_assoc_8_3
  · exact mul_assoc_8_4
  · exact mul_assoc_8_5
  · exact mul_assoc_8_6
  · exact mul_assoc_8_7
  · exact mul_assoc_8_8
  · exact mul_assoc_8_9
  · exact mul_assoc_8_10
  · exact mul_assoc_8_11
  · exact mul_assoc_8_12
  · exact mul_assoc_8_13
  · exact mul_assoc_8_14
  · exact mul_assoc_8_15

private theorem mul_assoc_9_0 : ∀ c : K, (ofBits 9) * (ofBits 0) * c = (ofBits 9) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_1 : ∀ c : K, (ofBits 9) * (ofBits 1) * c = (ofBits 9) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_2 : ∀ c : K, (ofBits 9) * (ofBits 2) * c = (ofBits 9) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_3 : ∀ c : K, (ofBits 9) * (ofBits 3) * c = (ofBits 9) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_4 : ∀ c : K, (ofBits 9) * (ofBits 4) * c = (ofBits 9) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_5 : ∀ c : K, (ofBits 9) * (ofBits 5) * c = (ofBits 9) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_6 : ∀ c : K, (ofBits 9) * (ofBits 6) * c = (ofBits 9) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_7 : ∀ c : K, (ofBits 9) * (ofBits 7) * c = (ofBits 9) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_8 : ∀ c : K, (ofBits 9) * (ofBits 8) * c = (ofBits 9) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_9 : ∀ c : K, (ofBits 9) * (ofBits 9) * c = (ofBits 9) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_10 : ∀ c : K, (ofBits 9) * (ofBits 10) * c = (ofBits 9) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_11 : ∀ c : K, (ofBits 9) * (ofBits 11) * c = (ofBits 9) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_12 : ∀ c : K, (ofBits 9) * (ofBits 12) * c = (ofBits 9) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_13 : ∀ c : K, (ofBits 9) * (ofBits 13) * c = (ofBits 9) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_14 : ∀ c : K, (ofBits 9) * (ofBits 14) * c = (ofBits 9) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_9_15 : ∀ c : K, (ofBits 9) * (ofBits 15) * c = (ofBits 9) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits9 : ∀ b c : K, (ofBits 9) * b * c = (ofBits 9) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_9_0
  · exact mul_assoc_9_1
  · exact mul_assoc_9_2
  · exact mul_assoc_9_3
  · exact mul_assoc_9_4
  · exact mul_assoc_9_5
  · exact mul_assoc_9_6
  · exact mul_assoc_9_7
  · exact mul_assoc_9_8
  · exact mul_assoc_9_9
  · exact mul_assoc_9_10
  · exact mul_assoc_9_11
  · exact mul_assoc_9_12
  · exact mul_assoc_9_13
  · exact mul_assoc_9_14
  · exact mul_assoc_9_15

private theorem mul_assoc_10_0 : ∀ c : K, (ofBits 10) * (ofBits 0) * c = (ofBits 10) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_1 : ∀ c : K, (ofBits 10) * (ofBits 1) * c = (ofBits 10) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_2 : ∀ c : K, (ofBits 10) * (ofBits 2) * c = (ofBits 10) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_3 : ∀ c : K, (ofBits 10) * (ofBits 3) * c = (ofBits 10) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_4 : ∀ c : K, (ofBits 10) * (ofBits 4) * c = (ofBits 10) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_5 : ∀ c : K, (ofBits 10) * (ofBits 5) * c = (ofBits 10) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_6 : ∀ c : K, (ofBits 10) * (ofBits 6) * c = (ofBits 10) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_7 : ∀ c : K, (ofBits 10) * (ofBits 7) * c = (ofBits 10) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_8 : ∀ c : K, (ofBits 10) * (ofBits 8) * c = (ofBits 10) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_9 : ∀ c : K, (ofBits 10) * (ofBits 9) * c = (ofBits 10) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_10 : ∀ c : K, (ofBits 10) * (ofBits 10) * c = (ofBits 10) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_11 : ∀ c : K, (ofBits 10) * (ofBits 11) * c = (ofBits 10) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_12 : ∀ c : K, (ofBits 10) * (ofBits 12) * c = (ofBits 10) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_13 : ∀ c : K, (ofBits 10) * (ofBits 13) * c = (ofBits 10) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_14 : ∀ c : K, (ofBits 10) * (ofBits 14) * c = (ofBits 10) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_10_15 : ∀ c : K, (ofBits 10) * (ofBits 15) * c = (ofBits 10) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits10 : ∀ b c : K, (ofBits 10) * b * c = (ofBits 10) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_10_0
  · exact mul_assoc_10_1
  · exact mul_assoc_10_2
  · exact mul_assoc_10_3
  · exact mul_assoc_10_4
  · exact mul_assoc_10_5
  · exact mul_assoc_10_6
  · exact mul_assoc_10_7
  · exact mul_assoc_10_8
  · exact mul_assoc_10_9
  · exact mul_assoc_10_10
  · exact mul_assoc_10_11
  · exact mul_assoc_10_12
  · exact mul_assoc_10_13
  · exact mul_assoc_10_14
  · exact mul_assoc_10_15

private theorem mul_assoc_11_0 : ∀ c : K, (ofBits 11) * (ofBits 0) * c = (ofBits 11) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_1 : ∀ c : K, (ofBits 11) * (ofBits 1) * c = (ofBits 11) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_2 : ∀ c : K, (ofBits 11) * (ofBits 2) * c = (ofBits 11) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_3 : ∀ c : K, (ofBits 11) * (ofBits 3) * c = (ofBits 11) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_4 : ∀ c : K, (ofBits 11) * (ofBits 4) * c = (ofBits 11) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_5 : ∀ c : K, (ofBits 11) * (ofBits 5) * c = (ofBits 11) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_6 : ∀ c : K, (ofBits 11) * (ofBits 6) * c = (ofBits 11) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_7 : ∀ c : K, (ofBits 11) * (ofBits 7) * c = (ofBits 11) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_8 : ∀ c : K, (ofBits 11) * (ofBits 8) * c = (ofBits 11) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_9 : ∀ c : K, (ofBits 11) * (ofBits 9) * c = (ofBits 11) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_10 : ∀ c : K, (ofBits 11) * (ofBits 10) * c = (ofBits 11) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_11 : ∀ c : K, (ofBits 11) * (ofBits 11) * c = (ofBits 11) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_12 : ∀ c : K, (ofBits 11) * (ofBits 12) * c = (ofBits 11) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_13 : ∀ c : K, (ofBits 11) * (ofBits 13) * c = (ofBits 11) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_14 : ∀ c : K, (ofBits 11) * (ofBits 14) * c = (ofBits 11) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_11_15 : ∀ c : K, (ofBits 11) * (ofBits 15) * c = (ofBits 11) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits11 : ∀ b c : K, (ofBits 11) * b * c = (ofBits 11) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_11_0
  · exact mul_assoc_11_1
  · exact mul_assoc_11_2
  · exact mul_assoc_11_3
  · exact mul_assoc_11_4
  · exact mul_assoc_11_5
  · exact mul_assoc_11_6
  · exact mul_assoc_11_7
  · exact mul_assoc_11_8
  · exact mul_assoc_11_9
  · exact mul_assoc_11_10
  · exact mul_assoc_11_11
  · exact mul_assoc_11_12
  · exact mul_assoc_11_13
  · exact mul_assoc_11_14
  · exact mul_assoc_11_15

private theorem mul_assoc_12_0 : ∀ c : K, (ofBits 12) * (ofBits 0) * c = (ofBits 12) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_1 : ∀ c : K, (ofBits 12) * (ofBits 1) * c = (ofBits 12) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_2 : ∀ c : K, (ofBits 12) * (ofBits 2) * c = (ofBits 12) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_3 : ∀ c : K, (ofBits 12) * (ofBits 3) * c = (ofBits 12) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_4 : ∀ c : K, (ofBits 12) * (ofBits 4) * c = (ofBits 12) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_5 : ∀ c : K, (ofBits 12) * (ofBits 5) * c = (ofBits 12) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_6 : ∀ c : K, (ofBits 12) * (ofBits 6) * c = (ofBits 12) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_7 : ∀ c : K, (ofBits 12) * (ofBits 7) * c = (ofBits 12) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_8 : ∀ c : K, (ofBits 12) * (ofBits 8) * c = (ofBits 12) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_9 : ∀ c : K, (ofBits 12) * (ofBits 9) * c = (ofBits 12) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_10 : ∀ c : K, (ofBits 12) * (ofBits 10) * c = (ofBits 12) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_11 : ∀ c : K, (ofBits 12) * (ofBits 11) * c = (ofBits 12) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_12 : ∀ c : K, (ofBits 12) * (ofBits 12) * c = (ofBits 12) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_13 : ∀ c : K, (ofBits 12) * (ofBits 13) * c = (ofBits 12) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_14 : ∀ c : K, (ofBits 12) * (ofBits 14) * c = (ofBits 12) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_12_15 : ∀ c : K, (ofBits 12) * (ofBits 15) * c = (ofBits 12) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits12 : ∀ b c : K, (ofBits 12) * b * c = (ofBits 12) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_12_0
  · exact mul_assoc_12_1
  · exact mul_assoc_12_2
  · exact mul_assoc_12_3
  · exact mul_assoc_12_4
  · exact mul_assoc_12_5
  · exact mul_assoc_12_6
  · exact mul_assoc_12_7
  · exact mul_assoc_12_8
  · exact mul_assoc_12_9
  · exact mul_assoc_12_10
  · exact mul_assoc_12_11
  · exact mul_assoc_12_12
  · exact mul_assoc_12_13
  · exact mul_assoc_12_14
  · exact mul_assoc_12_15

private theorem mul_assoc_13_0 : ∀ c : K, (ofBits 13) * (ofBits 0) * c = (ofBits 13) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_1 : ∀ c : K, (ofBits 13) * (ofBits 1) * c = (ofBits 13) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_2 : ∀ c : K, (ofBits 13) * (ofBits 2) * c = (ofBits 13) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_3 : ∀ c : K, (ofBits 13) * (ofBits 3) * c = (ofBits 13) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_4 : ∀ c : K, (ofBits 13) * (ofBits 4) * c = (ofBits 13) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_5 : ∀ c : K, (ofBits 13) * (ofBits 5) * c = (ofBits 13) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_6 : ∀ c : K, (ofBits 13) * (ofBits 6) * c = (ofBits 13) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_7 : ∀ c : K, (ofBits 13) * (ofBits 7) * c = (ofBits 13) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_8 : ∀ c : K, (ofBits 13) * (ofBits 8) * c = (ofBits 13) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_9 : ∀ c : K, (ofBits 13) * (ofBits 9) * c = (ofBits 13) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_10 : ∀ c : K, (ofBits 13) * (ofBits 10) * c = (ofBits 13) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_11 : ∀ c : K, (ofBits 13) * (ofBits 11) * c = (ofBits 13) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_12 : ∀ c : K, (ofBits 13) * (ofBits 12) * c = (ofBits 13) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_13 : ∀ c : K, (ofBits 13) * (ofBits 13) * c = (ofBits 13) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_14 : ∀ c : K, (ofBits 13) * (ofBits 14) * c = (ofBits 13) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_13_15 : ∀ c : K, (ofBits 13) * (ofBits 15) * c = (ofBits 13) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits13 : ∀ b c : K, (ofBits 13) * b * c = (ofBits 13) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_13_0
  · exact mul_assoc_13_1
  · exact mul_assoc_13_2
  · exact mul_assoc_13_3
  · exact mul_assoc_13_4
  · exact mul_assoc_13_5
  · exact mul_assoc_13_6
  · exact mul_assoc_13_7
  · exact mul_assoc_13_8
  · exact mul_assoc_13_9
  · exact mul_assoc_13_10
  · exact mul_assoc_13_11
  · exact mul_assoc_13_12
  · exact mul_assoc_13_13
  · exact mul_assoc_13_14
  · exact mul_assoc_13_15

private theorem mul_assoc_14_0 : ∀ c : K, (ofBits 14) * (ofBits 0) * c = (ofBits 14) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_1 : ∀ c : K, (ofBits 14) * (ofBits 1) * c = (ofBits 14) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_2 : ∀ c : K, (ofBits 14) * (ofBits 2) * c = (ofBits 14) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_3 : ∀ c : K, (ofBits 14) * (ofBits 3) * c = (ofBits 14) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_4 : ∀ c : K, (ofBits 14) * (ofBits 4) * c = (ofBits 14) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_5 : ∀ c : K, (ofBits 14) * (ofBits 5) * c = (ofBits 14) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_6 : ∀ c : K, (ofBits 14) * (ofBits 6) * c = (ofBits 14) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_7 : ∀ c : K, (ofBits 14) * (ofBits 7) * c = (ofBits 14) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_8 : ∀ c : K, (ofBits 14) * (ofBits 8) * c = (ofBits 14) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_9 : ∀ c : K, (ofBits 14) * (ofBits 9) * c = (ofBits 14) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_10 : ∀ c : K, (ofBits 14) * (ofBits 10) * c = (ofBits 14) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_11 : ∀ c : K, (ofBits 14) * (ofBits 11) * c = (ofBits 14) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_12 : ∀ c : K, (ofBits 14) * (ofBits 12) * c = (ofBits 14) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_13 : ∀ c : K, (ofBits 14) * (ofBits 13) * c = (ofBits 14) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_14 : ∀ c : K, (ofBits 14) * (ofBits 14) * c = (ofBits 14) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_14_15 : ∀ c : K, (ofBits 14) * (ofBits 15) * c = (ofBits 14) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits14 : ∀ b c : K, (ofBits 14) * b * c = (ofBits 14) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_14_0
  · exact mul_assoc_14_1
  · exact mul_assoc_14_2
  · exact mul_assoc_14_3
  · exact mul_assoc_14_4
  · exact mul_assoc_14_5
  · exact mul_assoc_14_6
  · exact mul_assoc_14_7
  · exact mul_assoc_14_8
  · exact mul_assoc_14_9
  · exact mul_assoc_14_10
  · exact mul_assoc_14_11
  · exact mul_assoc_14_12
  · exact mul_assoc_14_13
  · exact mul_assoc_14_14
  · exact mul_assoc_14_15

private theorem mul_assoc_15_0 : ∀ c : K, (ofBits 15) * (ofBits 0) * c = (ofBits 15) * ((ofBits 0) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_1 : ∀ c : K, (ofBits 15) * (ofBits 1) * c = (ofBits 15) * ((ofBits 1) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_2 : ∀ c : K, (ofBits 15) * (ofBits 2) * c = (ofBits 15) * ((ofBits 2) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_3 : ∀ c : K, (ofBits 15) * (ofBits 3) * c = (ofBits 15) * ((ofBits 3) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_4 : ∀ c : K, (ofBits 15) * (ofBits 4) * c = (ofBits 15) * ((ofBits 4) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_5 : ∀ c : K, (ofBits 15) * (ofBits 5) * c = (ofBits 15) * ((ofBits 5) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_6 : ∀ c : K, (ofBits 15) * (ofBits 6) * c = (ofBits 15) * ((ofBits 6) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_7 : ∀ c : K, (ofBits 15) * (ofBits 7) * c = (ofBits 15) * ((ofBits 7) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_8 : ∀ c : K, (ofBits 15) * (ofBits 8) * c = (ofBits 15) * ((ofBits 8) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_9 : ∀ c : K, (ofBits 15) * (ofBits 9) * c = (ofBits 15) * ((ofBits 9) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_10 : ∀ c : K, (ofBits 15) * (ofBits 10) * c = (ofBits 15) * ((ofBits 10) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_11 : ∀ c : K, (ofBits 15) * (ofBits 11) * c = (ofBits 15) * ((ofBits 11) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_12 : ∀ c : K, (ofBits 15) * (ofBits 12) * c = (ofBits 15) * ((ofBits 12) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_13 : ∀ c : K, (ofBits 15) * (ofBits 13) * c = (ofBits 15) * ((ofBits 13) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_14 : ∀ c : K, (ofBits 15) * (ofBits 14) * c = (ofBits 15) * ((ofBits 14) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_15_15 : ∀ c : K, (ofBits 15) * (ofBits 15) * c = (ofBits 15) * ((ofBits 15) * c) := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem mul_assoc_bits15 : ∀ b c : K, (ofBits 15) * b * c = (ofBits 15) * (b * c) := by
  rintro ⟨b⟩
  fin_cases b
  · exact mul_assoc_15_0
  · exact mul_assoc_15_1
  · exact mul_assoc_15_2
  · exact mul_assoc_15_3
  · exact mul_assoc_15_4
  · exact mul_assoc_15_5
  · exact mul_assoc_15_6
  · exact mul_assoc_15_7
  · exact mul_assoc_15_8
  · exact mul_assoc_15_9
  · exact mul_assoc_15_10
  · exact mul_assoc_15_11
  · exact mul_assoc_15_12
  · exact mul_assoc_15_13
  · exact mul_assoc_15_14
  · exact mul_assoc_15_15

private theorem mul_assoc_cert : ∀ a b c : K, a * b * c = a * (b * c) := by
  rintro ⟨a⟩
  fin_cases a
  · exact mul_assoc_bits0
  · exact mul_assoc_bits1
  · exact mul_assoc_bits2
  · exact mul_assoc_bits3
  · exact mul_assoc_bits4
  · exact mul_assoc_bits5
  · exact mul_assoc_bits6
  · exact mul_assoc_bits7
  · exact mul_assoc_bits8
  · exact mul_assoc_bits9
  · exact mul_assoc_bits10
  · exact mul_assoc_bits11
  · exact mul_assoc_bits12
  · exact mul_assoc_bits13
  · exact mul_assoc_bits14
  · exact mul_assoc_bits15
private theorem mul_comm_bits0 : ∀ b : K, (ofBits 0) * b = b * (ofBits 0) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits1 : ∀ b : K, (ofBits 1) * b = b * (ofBits 1) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits2 : ∀ b : K, (ofBits 2) * b = b * (ofBits 2) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits3 : ∀ b : K, (ofBits 3) * b = b * (ofBits 3) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits4 : ∀ b : K, (ofBits 4) * b = b * (ofBits 4) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits5 : ∀ b : K, (ofBits 5) * b = b * (ofBits 5) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits6 : ∀ b : K, (ofBits 6) * b = b * (ofBits 6) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits7 : ∀ b : K, (ofBits 7) * b = b * (ofBits 7) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits8 : ∀ b : K, (ofBits 8) * b = b * (ofBits 8) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits9 : ∀ b : K, (ofBits 9) * b = b * (ofBits 9) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits10 : ∀ b : K, (ofBits 10) * b = b * (ofBits 10) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits11 : ∀ b : K, (ofBits 11) * b = b * (ofBits 11) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits12 : ∀ b : K, (ofBits 12) * b = b * (ofBits 12) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits13 : ∀ b : K, (ofBits 13) * b = b * (ofBits 13) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits14 : ∀ b : K, (ofBits 14) * b = b * (ofBits 14) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_bits15 : ∀ b : K, (ofBits 15) * b = b * (ofBits 15) := by
  rintro ⟨b⟩
  fin_cases b <;> rfl
private theorem mul_comm_cert : ∀ a b : K, a * b = b * a := by
  rintro ⟨a⟩
  fin_cases a
  · exact mul_comm_bits0
  · exact mul_comm_bits1
  · exact mul_comm_bits2
  · exact mul_comm_bits3
  · exact mul_comm_bits4
  · exact mul_comm_bits5
  · exact mul_comm_bits6
  · exact mul_comm_bits7
  · exact mul_comm_bits8
  · exact mul_comm_bits9
  · exact mul_comm_bits10
  · exact mul_comm_bits11
  · exact mul_comm_bits12
  · exact mul_comm_bits13
  · exact mul_comm_bits14
  · exact mul_comm_bits15

private theorem one_mul_cert : ∀ a : K, 1 * a = a := by decide +kernel
private theorem mul_inv_cert : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1 := by decide +kernel
private theorem inv_zero_cert : (0 : K)⁻¹ = 0 := by decide +kernel
private theorem distrib_0_0 : ∀ c : K, (ofBits 0) * ((ofBits 0) + c) = (ofBits 0) * (ofBits 0) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_1 : ∀ c : K, (ofBits 0) * ((ofBits 1) + c) = (ofBits 0) * (ofBits 1) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_2 : ∀ c : K, (ofBits 0) * ((ofBits 2) + c) = (ofBits 0) * (ofBits 2) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_3 : ∀ c : K, (ofBits 0) * ((ofBits 3) + c) = (ofBits 0) * (ofBits 3) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_4 : ∀ c : K, (ofBits 0) * ((ofBits 4) + c) = (ofBits 0) * (ofBits 4) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_5 : ∀ c : K, (ofBits 0) * ((ofBits 5) + c) = (ofBits 0) * (ofBits 5) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_6 : ∀ c : K, (ofBits 0) * ((ofBits 6) + c) = (ofBits 0) * (ofBits 6) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_7 : ∀ c : K, (ofBits 0) * ((ofBits 7) + c) = (ofBits 0) * (ofBits 7) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_8 : ∀ c : K, (ofBits 0) * ((ofBits 8) + c) = (ofBits 0) * (ofBits 8) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_9 : ∀ c : K, (ofBits 0) * ((ofBits 9) + c) = (ofBits 0) * (ofBits 9) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_10 : ∀ c : K, (ofBits 0) * ((ofBits 10) + c) = (ofBits 0) * (ofBits 10) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_11 : ∀ c : K, (ofBits 0) * ((ofBits 11) + c) = (ofBits 0) * (ofBits 11) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_12 : ∀ c : K, (ofBits 0) * ((ofBits 12) + c) = (ofBits 0) * (ofBits 12) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_13 : ∀ c : K, (ofBits 0) * ((ofBits 13) + c) = (ofBits 0) * (ofBits 13) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_14 : ∀ c : K, (ofBits 0) * ((ofBits 14) + c) = (ofBits 0) * (ofBits 14) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_0_15 : ∀ c : K, (ofBits 0) * ((ofBits 15) + c) = (ofBits 0) * (ofBits 15) + (ofBits 0) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits0 : ∀ b c : K, (ofBits 0) * (b + c) = (ofBits 0) * b + (ofBits 0) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_0_0
  · exact distrib_0_1
  · exact distrib_0_2
  · exact distrib_0_3
  · exact distrib_0_4
  · exact distrib_0_5
  · exact distrib_0_6
  · exact distrib_0_7
  · exact distrib_0_8
  · exact distrib_0_9
  · exact distrib_0_10
  · exact distrib_0_11
  · exact distrib_0_12
  · exact distrib_0_13
  · exact distrib_0_14
  · exact distrib_0_15

private theorem distrib_1_0 : ∀ c : K, (ofBits 1) * ((ofBits 0) + c) = (ofBits 1) * (ofBits 0) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_1 : ∀ c : K, (ofBits 1) * ((ofBits 1) + c) = (ofBits 1) * (ofBits 1) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_2 : ∀ c : K, (ofBits 1) * ((ofBits 2) + c) = (ofBits 1) * (ofBits 2) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_3 : ∀ c : K, (ofBits 1) * ((ofBits 3) + c) = (ofBits 1) * (ofBits 3) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_4 : ∀ c : K, (ofBits 1) * ((ofBits 4) + c) = (ofBits 1) * (ofBits 4) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_5 : ∀ c : K, (ofBits 1) * ((ofBits 5) + c) = (ofBits 1) * (ofBits 5) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_6 : ∀ c : K, (ofBits 1) * ((ofBits 6) + c) = (ofBits 1) * (ofBits 6) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_7 : ∀ c : K, (ofBits 1) * ((ofBits 7) + c) = (ofBits 1) * (ofBits 7) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_8 : ∀ c : K, (ofBits 1) * ((ofBits 8) + c) = (ofBits 1) * (ofBits 8) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_9 : ∀ c : K, (ofBits 1) * ((ofBits 9) + c) = (ofBits 1) * (ofBits 9) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_10 : ∀ c : K, (ofBits 1) * ((ofBits 10) + c) = (ofBits 1) * (ofBits 10) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_11 : ∀ c : K, (ofBits 1) * ((ofBits 11) + c) = (ofBits 1) * (ofBits 11) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_12 : ∀ c : K, (ofBits 1) * ((ofBits 12) + c) = (ofBits 1) * (ofBits 12) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_13 : ∀ c : K, (ofBits 1) * ((ofBits 13) + c) = (ofBits 1) * (ofBits 13) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_14 : ∀ c : K, (ofBits 1) * ((ofBits 14) + c) = (ofBits 1) * (ofBits 14) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_1_15 : ∀ c : K, (ofBits 1) * ((ofBits 15) + c) = (ofBits 1) * (ofBits 15) + (ofBits 1) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits1 : ∀ b c : K, (ofBits 1) * (b + c) = (ofBits 1) * b + (ofBits 1) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_1_0
  · exact distrib_1_1
  · exact distrib_1_2
  · exact distrib_1_3
  · exact distrib_1_4
  · exact distrib_1_5
  · exact distrib_1_6
  · exact distrib_1_7
  · exact distrib_1_8
  · exact distrib_1_9
  · exact distrib_1_10
  · exact distrib_1_11
  · exact distrib_1_12
  · exact distrib_1_13
  · exact distrib_1_14
  · exact distrib_1_15

private theorem distrib_2_0 : ∀ c : K, (ofBits 2) * ((ofBits 0) + c) = (ofBits 2) * (ofBits 0) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_1 : ∀ c : K, (ofBits 2) * ((ofBits 1) + c) = (ofBits 2) * (ofBits 1) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_2 : ∀ c : K, (ofBits 2) * ((ofBits 2) + c) = (ofBits 2) * (ofBits 2) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_3 : ∀ c : K, (ofBits 2) * ((ofBits 3) + c) = (ofBits 2) * (ofBits 3) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_4 : ∀ c : K, (ofBits 2) * ((ofBits 4) + c) = (ofBits 2) * (ofBits 4) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_5 : ∀ c : K, (ofBits 2) * ((ofBits 5) + c) = (ofBits 2) * (ofBits 5) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_6 : ∀ c : K, (ofBits 2) * ((ofBits 6) + c) = (ofBits 2) * (ofBits 6) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_7 : ∀ c : K, (ofBits 2) * ((ofBits 7) + c) = (ofBits 2) * (ofBits 7) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_8 : ∀ c : K, (ofBits 2) * ((ofBits 8) + c) = (ofBits 2) * (ofBits 8) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_9 : ∀ c : K, (ofBits 2) * ((ofBits 9) + c) = (ofBits 2) * (ofBits 9) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_10 : ∀ c : K, (ofBits 2) * ((ofBits 10) + c) = (ofBits 2) * (ofBits 10) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_11 : ∀ c : K, (ofBits 2) * ((ofBits 11) + c) = (ofBits 2) * (ofBits 11) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_12 : ∀ c : K, (ofBits 2) * ((ofBits 12) + c) = (ofBits 2) * (ofBits 12) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_13 : ∀ c : K, (ofBits 2) * ((ofBits 13) + c) = (ofBits 2) * (ofBits 13) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_14 : ∀ c : K, (ofBits 2) * ((ofBits 14) + c) = (ofBits 2) * (ofBits 14) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_2_15 : ∀ c : K, (ofBits 2) * ((ofBits 15) + c) = (ofBits 2) * (ofBits 15) + (ofBits 2) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits2 : ∀ b c : K, (ofBits 2) * (b + c) = (ofBits 2) * b + (ofBits 2) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_2_0
  · exact distrib_2_1
  · exact distrib_2_2
  · exact distrib_2_3
  · exact distrib_2_4
  · exact distrib_2_5
  · exact distrib_2_6
  · exact distrib_2_7
  · exact distrib_2_8
  · exact distrib_2_9
  · exact distrib_2_10
  · exact distrib_2_11
  · exact distrib_2_12
  · exact distrib_2_13
  · exact distrib_2_14
  · exact distrib_2_15

private theorem distrib_3_0 : ∀ c : K, (ofBits 3) * ((ofBits 0) + c) = (ofBits 3) * (ofBits 0) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_1 : ∀ c : K, (ofBits 3) * ((ofBits 1) + c) = (ofBits 3) * (ofBits 1) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_2 : ∀ c : K, (ofBits 3) * ((ofBits 2) + c) = (ofBits 3) * (ofBits 2) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_3 : ∀ c : K, (ofBits 3) * ((ofBits 3) + c) = (ofBits 3) * (ofBits 3) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_4 : ∀ c : K, (ofBits 3) * ((ofBits 4) + c) = (ofBits 3) * (ofBits 4) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_5 : ∀ c : K, (ofBits 3) * ((ofBits 5) + c) = (ofBits 3) * (ofBits 5) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_6 : ∀ c : K, (ofBits 3) * ((ofBits 6) + c) = (ofBits 3) * (ofBits 6) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_7 : ∀ c : K, (ofBits 3) * ((ofBits 7) + c) = (ofBits 3) * (ofBits 7) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_8 : ∀ c : K, (ofBits 3) * ((ofBits 8) + c) = (ofBits 3) * (ofBits 8) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_9 : ∀ c : K, (ofBits 3) * ((ofBits 9) + c) = (ofBits 3) * (ofBits 9) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_10 : ∀ c : K, (ofBits 3) * ((ofBits 10) + c) = (ofBits 3) * (ofBits 10) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_11 : ∀ c : K, (ofBits 3) * ((ofBits 11) + c) = (ofBits 3) * (ofBits 11) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_12 : ∀ c : K, (ofBits 3) * ((ofBits 12) + c) = (ofBits 3) * (ofBits 12) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_13 : ∀ c : K, (ofBits 3) * ((ofBits 13) + c) = (ofBits 3) * (ofBits 13) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_14 : ∀ c : K, (ofBits 3) * ((ofBits 14) + c) = (ofBits 3) * (ofBits 14) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_3_15 : ∀ c : K, (ofBits 3) * ((ofBits 15) + c) = (ofBits 3) * (ofBits 15) + (ofBits 3) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits3 : ∀ b c : K, (ofBits 3) * (b + c) = (ofBits 3) * b + (ofBits 3) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_3_0
  · exact distrib_3_1
  · exact distrib_3_2
  · exact distrib_3_3
  · exact distrib_3_4
  · exact distrib_3_5
  · exact distrib_3_6
  · exact distrib_3_7
  · exact distrib_3_8
  · exact distrib_3_9
  · exact distrib_3_10
  · exact distrib_3_11
  · exact distrib_3_12
  · exact distrib_3_13
  · exact distrib_3_14
  · exact distrib_3_15

private theorem distrib_4_0 : ∀ c : K, (ofBits 4) * ((ofBits 0) + c) = (ofBits 4) * (ofBits 0) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_1 : ∀ c : K, (ofBits 4) * ((ofBits 1) + c) = (ofBits 4) * (ofBits 1) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_2 : ∀ c : K, (ofBits 4) * ((ofBits 2) + c) = (ofBits 4) * (ofBits 2) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_3 : ∀ c : K, (ofBits 4) * ((ofBits 3) + c) = (ofBits 4) * (ofBits 3) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_4 : ∀ c : K, (ofBits 4) * ((ofBits 4) + c) = (ofBits 4) * (ofBits 4) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_5 : ∀ c : K, (ofBits 4) * ((ofBits 5) + c) = (ofBits 4) * (ofBits 5) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_6 : ∀ c : K, (ofBits 4) * ((ofBits 6) + c) = (ofBits 4) * (ofBits 6) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_7 : ∀ c : K, (ofBits 4) * ((ofBits 7) + c) = (ofBits 4) * (ofBits 7) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_8 : ∀ c : K, (ofBits 4) * ((ofBits 8) + c) = (ofBits 4) * (ofBits 8) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_9 : ∀ c : K, (ofBits 4) * ((ofBits 9) + c) = (ofBits 4) * (ofBits 9) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_10 : ∀ c : K, (ofBits 4) * ((ofBits 10) + c) = (ofBits 4) * (ofBits 10) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_11 : ∀ c : K, (ofBits 4) * ((ofBits 11) + c) = (ofBits 4) * (ofBits 11) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_12 : ∀ c : K, (ofBits 4) * ((ofBits 12) + c) = (ofBits 4) * (ofBits 12) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_13 : ∀ c : K, (ofBits 4) * ((ofBits 13) + c) = (ofBits 4) * (ofBits 13) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_14 : ∀ c : K, (ofBits 4) * ((ofBits 14) + c) = (ofBits 4) * (ofBits 14) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_4_15 : ∀ c : K, (ofBits 4) * ((ofBits 15) + c) = (ofBits 4) * (ofBits 15) + (ofBits 4) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits4 : ∀ b c : K, (ofBits 4) * (b + c) = (ofBits 4) * b + (ofBits 4) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_4_0
  · exact distrib_4_1
  · exact distrib_4_2
  · exact distrib_4_3
  · exact distrib_4_4
  · exact distrib_4_5
  · exact distrib_4_6
  · exact distrib_4_7
  · exact distrib_4_8
  · exact distrib_4_9
  · exact distrib_4_10
  · exact distrib_4_11
  · exact distrib_4_12
  · exact distrib_4_13
  · exact distrib_4_14
  · exact distrib_4_15

private theorem distrib_5_0 : ∀ c : K, (ofBits 5) * ((ofBits 0) + c) = (ofBits 5) * (ofBits 0) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_1 : ∀ c : K, (ofBits 5) * ((ofBits 1) + c) = (ofBits 5) * (ofBits 1) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_2 : ∀ c : K, (ofBits 5) * ((ofBits 2) + c) = (ofBits 5) * (ofBits 2) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_3 : ∀ c : K, (ofBits 5) * ((ofBits 3) + c) = (ofBits 5) * (ofBits 3) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_4 : ∀ c : K, (ofBits 5) * ((ofBits 4) + c) = (ofBits 5) * (ofBits 4) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_5 : ∀ c : K, (ofBits 5) * ((ofBits 5) + c) = (ofBits 5) * (ofBits 5) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_6 : ∀ c : K, (ofBits 5) * ((ofBits 6) + c) = (ofBits 5) * (ofBits 6) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_7 : ∀ c : K, (ofBits 5) * ((ofBits 7) + c) = (ofBits 5) * (ofBits 7) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_8 : ∀ c : K, (ofBits 5) * ((ofBits 8) + c) = (ofBits 5) * (ofBits 8) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_9 : ∀ c : K, (ofBits 5) * ((ofBits 9) + c) = (ofBits 5) * (ofBits 9) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_10 : ∀ c : K, (ofBits 5) * ((ofBits 10) + c) = (ofBits 5) * (ofBits 10) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_11 : ∀ c : K, (ofBits 5) * ((ofBits 11) + c) = (ofBits 5) * (ofBits 11) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_12 : ∀ c : K, (ofBits 5) * ((ofBits 12) + c) = (ofBits 5) * (ofBits 12) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_13 : ∀ c : K, (ofBits 5) * ((ofBits 13) + c) = (ofBits 5) * (ofBits 13) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_14 : ∀ c : K, (ofBits 5) * ((ofBits 14) + c) = (ofBits 5) * (ofBits 14) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_5_15 : ∀ c : K, (ofBits 5) * ((ofBits 15) + c) = (ofBits 5) * (ofBits 15) + (ofBits 5) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits5 : ∀ b c : K, (ofBits 5) * (b + c) = (ofBits 5) * b + (ofBits 5) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_5_0
  · exact distrib_5_1
  · exact distrib_5_2
  · exact distrib_5_3
  · exact distrib_5_4
  · exact distrib_5_5
  · exact distrib_5_6
  · exact distrib_5_7
  · exact distrib_5_8
  · exact distrib_5_9
  · exact distrib_5_10
  · exact distrib_5_11
  · exact distrib_5_12
  · exact distrib_5_13
  · exact distrib_5_14
  · exact distrib_5_15

private theorem distrib_6_0 : ∀ c : K, (ofBits 6) * ((ofBits 0) + c) = (ofBits 6) * (ofBits 0) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_1 : ∀ c : K, (ofBits 6) * ((ofBits 1) + c) = (ofBits 6) * (ofBits 1) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_2 : ∀ c : K, (ofBits 6) * ((ofBits 2) + c) = (ofBits 6) * (ofBits 2) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_3 : ∀ c : K, (ofBits 6) * ((ofBits 3) + c) = (ofBits 6) * (ofBits 3) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_4 : ∀ c : K, (ofBits 6) * ((ofBits 4) + c) = (ofBits 6) * (ofBits 4) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_5 : ∀ c : K, (ofBits 6) * ((ofBits 5) + c) = (ofBits 6) * (ofBits 5) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_6 : ∀ c : K, (ofBits 6) * ((ofBits 6) + c) = (ofBits 6) * (ofBits 6) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_7 : ∀ c : K, (ofBits 6) * ((ofBits 7) + c) = (ofBits 6) * (ofBits 7) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_8 : ∀ c : K, (ofBits 6) * ((ofBits 8) + c) = (ofBits 6) * (ofBits 8) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_9 : ∀ c : K, (ofBits 6) * ((ofBits 9) + c) = (ofBits 6) * (ofBits 9) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_10 : ∀ c : K, (ofBits 6) * ((ofBits 10) + c) = (ofBits 6) * (ofBits 10) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_11 : ∀ c : K, (ofBits 6) * ((ofBits 11) + c) = (ofBits 6) * (ofBits 11) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_12 : ∀ c : K, (ofBits 6) * ((ofBits 12) + c) = (ofBits 6) * (ofBits 12) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_13 : ∀ c : K, (ofBits 6) * ((ofBits 13) + c) = (ofBits 6) * (ofBits 13) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_14 : ∀ c : K, (ofBits 6) * ((ofBits 14) + c) = (ofBits 6) * (ofBits 14) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_6_15 : ∀ c : K, (ofBits 6) * ((ofBits 15) + c) = (ofBits 6) * (ofBits 15) + (ofBits 6) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits6 : ∀ b c : K, (ofBits 6) * (b + c) = (ofBits 6) * b + (ofBits 6) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_6_0
  · exact distrib_6_1
  · exact distrib_6_2
  · exact distrib_6_3
  · exact distrib_6_4
  · exact distrib_6_5
  · exact distrib_6_6
  · exact distrib_6_7
  · exact distrib_6_8
  · exact distrib_6_9
  · exact distrib_6_10
  · exact distrib_6_11
  · exact distrib_6_12
  · exact distrib_6_13
  · exact distrib_6_14
  · exact distrib_6_15

private theorem distrib_7_0 : ∀ c : K, (ofBits 7) * ((ofBits 0) + c) = (ofBits 7) * (ofBits 0) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_1 : ∀ c : K, (ofBits 7) * ((ofBits 1) + c) = (ofBits 7) * (ofBits 1) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_2 : ∀ c : K, (ofBits 7) * ((ofBits 2) + c) = (ofBits 7) * (ofBits 2) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_3 : ∀ c : K, (ofBits 7) * ((ofBits 3) + c) = (ofBits 7) * (ofBits 3) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_4 : ∀ c : K, (ofBits 7) * ((ofBits 4) + c) = (ofBits 7) * (ofBits 4) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_5 : ∀ c : K, (ofBits 7) * ((ofBits 5) + c) = (ofBits 7) * (ofBits 5) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_6 : ∀ c : K, (ofBits 7) * ((ofBits 6) + c) = (ofBits 7) * (ofBits 6) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_7 : ∀ c : K, (ofBits 7) * ((ofBits 7) + c) = (ofBits 7) * (ofBits 7) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_8 : ∀ c : K, (ofBits 7) * ((ofBits 8) + c) = (ofBits 7) * (ofBits 8) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_9 : ∀ c : K, (ofBits 7) * ((ofBits 9) + c) = (ofBits 7) * (ofBits 9) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_10 : ∀ c : K, (ofBits 7) * ((ofBits 10) + c) = (ofBits 7) * (ofBits 10) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_11 : ∀ c : K, (ofBits 7) * ((ofBits 11) + c) = (ofBits 7) * (ofBits 11) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_12 : ∀ c : K, (ofBits 7) * ((ofBits 12) + c) = (ofBits 7) * (ofBits 12) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_13 : ∀ c : K, (ofBits 7) * ((ofBits 13) + c) = (ofBits 7) * (ofBits 13) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_14 : ∀ c : K, (ofBits 7) * ((ofBits 14) + c) = (ofBits 7) * (ofBits 14) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_7_15 : ∀ c : K, (ofBits 7) * ((ofBits 15) + c) = (ofBits 7) * (ofBits 15) + (ofBits 7) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits7 : ∀ b c : K, (ofBits 7) * (b + c) = (ofBits 7) * b + (ofBits 7) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_7_0
  · exact distrib_7_1
  · exact distrib_7_2
  · exact distrib_7_3
  · exact distrib_7_4
  · exact distrib_7_5
  · exact distrib_7_6
  · exact distrib_7_7
  · exact distrib_7_8
  · exact distrib_7_9
  · exact distrib_7_10
  · exact distrib_7_11
  · exact distrib_7_12
  · exact distrib_7_13
  · exact distrib_7_14
  · exact distrib_7_15

private theorem distrib_8_0 : ∀ c : K, (ofBits 8) * ((ofBits 0) + c) = (ofBits 8) * (ofBits 0) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_1 : ∀ c : K, (ofBits 8) * ((ofBits 1) + c) = (ofBits 8) * (ofBits 1) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_2 : ∀ c : K, (ofBits 8) * ((ofBits 2) + c) = (ofBits 8) * (ofBits 2) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_3 : ∀ c : K, (ofBits 8) * ((ofBits 3) + c) = (ofBits 8) * (ofBits 3) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_4 : ∀ c : K, (ofBits 8) * ((ofBits 4) + c) = (ofBits 8) * (ofBits 4) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_5 : ∀ c : K, (ofBits 8) * ((ofBits 5) + c) = (ofBits 8) * (ofBits 5) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_6 : ∀ c : K, (ofBits 8) * ((ofBits 6) + c) = (ofBits 8) * (ofBits 6) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_7 : ∀ c : K, (ofBits 8) * ((ofBits 7) + c) = (ofBits 8) * (ofBits 7) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_8 : ∀ c : K, (ofBits 8) * ((ofBits 8) + c) = (ofBits 8) * (ofBits 8) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_9 : ∀ c : K, (ofBits 8) * ((ofBits 9) + c) = (ofBits 8) * (ofBits 9) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_10 : ∀ c : K, (ofBits 8) * ((ofBits 10) + c) = (ofBits 8) * (ofBits 10) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_11 : ∀ c : K, (ofBits 8) * ((ofBits 11) + c) = (ofBits 8) * (ofBits 11) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_12 : ∀ c : K, (ofBits 8) * ((ofBits 12) + c) = (ofBits 8) * (ofBits 12) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_13 : ∀ c : K, (ofBits 8) * ((ofBits 13) + c) = (ofBits 8) * (ofBits 13) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_14 : ∀ c : K, (ofBits 8) * ((ofBits 14) + c) = (ofBits 8) * (ofBits 14) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_8_15 : ∀ c : K, (ofBits 8) * ((ofBits 15) + c) = (ofBits 8) * (ofBits 15) + (ofBits 8) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits8 : ∀ b c : K, (ofBits 8) * (b + c) = (ofBits 8) * b + (ofBits 8) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_8_0
  · exact distrib_8_1
  · exact distrib_8_2
  · exact distrib_8_3
  · exact distrib_8_4
  · exact distrib_8_5
  · exact distrib_8_6
  · exact distrib_8_7
  · exact distrib_8_8
  · exact distrib_8_9
  · exact distrib_8_10
  · exact distrib_8_11
  · exact distrib_8_12
  · exact distrib_8_13
  · exact distrib_8_14
  · exact distrib_8_15

private theorem distrib_9_0 : ∀ c : K, (ofBits 9) * ((ofBits 0) + c) = (ofBits 9) * (ofBits 0) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_1 : ∀ c : K, (ofBits 9) * ((ofBits 1) + c) = (ofBits 9) * (ofBits 1) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_2 : ∀ c : K, (ofBits 9) * ((ofBits 2) + c) = (ofBits 9) * (ofBits 2) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_3 : ∀ c : K, (ofBits 9) * ((ofBits 3) + c) = (ofBits 9) * (ofBits 3) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_4 : ∀ c : K, (ofBits 9) * ((ofBits 4) + c) = (ofBits 9) * (ofBits 4) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_5 : ∀ c : K, (ofBits 9) * ((ofBits 5) + c) = (ofBits 9) * (ofBits 5) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_6 : ∀ c : K, (ofBits 9) * ((ofBits 6) + c) = (ofBits 9) * (ofBits 6) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_7 : ∀ c : K, (ofBits 9) * ((ofBits 7) + c) = (ofBits 9) * (ofBits 7) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_8 : ∀ c : K, (ofBits 9) * ((ofBits 8) + c) = (ofBits 9) * (ofBits 8) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_9 : ∀ c : K, (ofBits 9) * ((ofBits 9) + c) = (ofBits 9) * (ofBits 9) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_10 : ∀ c : K, (ofBits 9) * ((ofBits 10) + c) = (ofBits 9) * (ofBits 10) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_11 : ∀ c : K, (ofBits 9) * ((ofBits 11) + c) = (ofBits 9) * (ofBits 11) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_12 : ∀ c : K, (ofBits 9) * ((ofBits 12) + c) = (ofBits 9) * (ofBits 12) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_13 : ∀ c : K, (ofBits 9) * ((ofBits 13) + c) = (ofBits 9) * (ofBits 13) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_14 : ∀ c : K, (ofBits 9) * ((ofBits 14) + c) = (ofBits 9) * (ofBits 14) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_9_15 : ∀ c : K, (ofBits 9) * ((ofBits 15) + c) = (ofBits 9) * (ofBits 15) + (ofBits 9) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits9 : ∀ b c : K, (ofBits 9) * (b + c) = (ofBits 9) * b + (ofBits 9) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_9_0
  · exact distrib_9_1
  · exact distrib_9_2
  · exact distrib_9_3
  · exact distrib_9_4
  · exact distrib_9_5
  · exact distrib_9_6
  · exact distrib_9_7
  · exact distrib_9_8
  · exact distrib_9_9
  · exact distrib_9_10
  · exact distrib_9_11
  · exact distrib_9_12
  · exact distrib_9_13
  · exact distrib_9_14
  · exact distrib_9_15

private theorem distrib_10_0 : ∀ c : K, (ofBits 10) * ((ofBits 0) + c) = (ofBits 10) * (ofBits 0) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_1 : ∀ c : K, (ofBits 10) * ((ofBits 1) + c) = (ofBits 10) * (ofBits 1) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_2 : ∀ c : K, (ofBits 10) * ((ofBits 2) + c) = (ofBits 10) * (ofBits 2) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_3 : ∀ c : K, (ofBits 10) * ((ofBits 3) + c) = (ofBits 10) * (ofBits 3) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_4 : ∀ c : K, (ofBits 10) * ((ofBits 4) + c) = (ofBits 10) * (ofBits 4) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_5 : ∀ c : K, (ofBits 10) * ((ofBits 5) + c) = (ofBits 10) * (ofBits 5) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_6 : ∀ c : K, (ofBits 10) * ((ofBits 6) + c) = (ofBits 10) * (ofBits 6) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_7 : ∀ c : K, (ofBits 10) * ((ofBits 7) + c) = (ofBits 10) * (ofBits 7) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_8 : ∀ c : K, (ofBits 10) * ((ofBits 8) + c) = (ofBits 10) * (ofBits 8) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_9 : ∀ c : K, (ofBits 10) * ((ofBits 9) + c) = (ofBits 10) * (ofBits 9) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_10 : ∀ c : K, (ofBits 10) * ((ofBits 10) + c) = (ofBits 10) * (ofBits 10) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_11 : ∀ c : K, (ofBits 10) * ((ofBits 11) + c) = (ofBits 10) * (ofBits 11) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_12 : ∀ c : K, (ofBits 10) * ((ofBits 12) + c) = (ofBits 10) * (ofBits 12) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_13 : ∀ c : K, (ofBits 10) * ((ofBits 13) + c) = (ofBits 10) * (ofBits 13) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_14 : ∀ c : K, (ofBits 10) * ((ofBits 14) + c) = (ofBits 10) * (ofBits 14) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_10_15 : ∀ c : K, (ofBits 10) * ((ofBits 15) + c) = (ofBits 10) * (ofBits 15) + (ofBits 10) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits10 : ∀ b c : K, (ofBits 10) * (b + c) = (ofBits 10) * b + (ofBits 10) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_10_0
  · exact distrib_10_1
  · exact distrib_10_2
  · exact distrib_10_3
  · exact distrib_10_4
  · exact distrib_10_5
  · exact distrib_10_6
  · exact distrib_10_7
  · exact distrib_10_8
  · exact distrib_10_9
  · exact distrib_10_10
  · exact distrib_10_11
  · exact distrib_10_12
  · exact distrib_10_13
  · exact distrib_10_14
  · exact distrib_10_15

private theorem distrib_11_0 : ∀ c : K, (ofBits 11) * ((ofBits 0) + c) = (ofBits 11) * (ofBits 0) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_1 : ∀ c : K, (ofBits 11) * ((ofBits 1) + c) = (ofBits 11) * (ofBits 1) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_2 : ∀ c : K, (ofBits 11) * ((ofBits 2) + c) = (ofBits 11) * (ofBits 2) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_3 : ∀ c : K, (ofBits 11) * ((ofBits 3) + c) = (ofBits 11) * (ofBits 3) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_4 : ∀ c : K, (ofBits 11) * ((ofBits 4) + c) = (ofBits 11) * (ofBits 4) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_5 : ∀ c : K, (ofBits 11) * ((ofBits 5) + c) = (ofBits 11) * (ofBits 5) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_6 : ∀ c : K, (ofBits 11) * ((ofBits 6) + c) = (ofBits 11) * (ofBits 6) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_7 : ∀ c : K, (ofBits 11) * ((ofBits 7) + c) = (ofBits 11) * (ofBits 7) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_8 : ∀ c : K, (ofBits 11) * ((ofBits 8) + c) = (ofBits 11) * (ofBits 8) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_9 : ∀ c : K, (ofBits 11) * ((ofBits 9) + c) = (ofBits 11) * (ofBits 9) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_10 : ∀ c : K, (ofBits 11) * ((ofBits 10) + c) = (ofBits 11) * (ofBits 10) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_11 : ∀ c : K, (ofBits 11) * ((ofBits 11) + c) = (ofBits 11) * (ofBits 11) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_12 : ∀ c : K, (ofBits 11) * ((ofBits 12) + c) = (ofBits 11) * (ofBits 12) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_13 : ∀ c : K, (ofBits 11) * ((ofBits 13) + c) = (ofBits 11) * (ofBits 13) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_14 : ∀ c : K, (ofBits 11) * ((ofBits 14) + c) = (ofBits 11) * (ofBits 14) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_11_15 : ∀ c : K, (ofBits 11) * ((ofBits 15) + c) = (ofBits 11) * (ofBits 15) + (ofBits 11) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits11 : ∀ b c : K, (ofBits 11) * (b + c) = (ofBits 11) * b + (ofBits 11) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_11_0
  · exact distrib_11_1
  · exact distrib_11_2
  · exact distrib_11_3
  · exact distrib_11_4
  · exact distrib_11_5
  · exact distrib_11_6
  · exact distrib_11_7
  · exact distrib_11_8
  · exact distrib_11_9
  · exact distrib_11_10
  · exact distrib_11_11
  · exact distrib_11_12
  · exact distrib_11_13
  · exact distrib_11_14
  · exact distrib_11_15

private theorem distrib_12_0 : ∀ c : K, (ofBits 12) * ((ofBits 0) + c) = (ofBits 12) * (ofBits 0) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_1 : ∀ c : K, (ofBits 12) * ((ofBits 1) + c) = (ofBits 12) * (ofBits 1) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_2 : ∀ c : K, (ofBits 12) * ((ofBits 2) + c) = (ofBits 12) * (ofBits 2) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_3 : ∀ c : K, (ofBits 12) * ((ofBits 3) + c) = (ofBits 12) * (ofBits 3) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_4 : ∀ c : K, (ofBits 12) * ((ofBits 4) + c) = (ofBits 12) * (ofBits 4) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_5 : ∀ c : K, (ofBits 12) * ((ofBits 5) + c) = (ofBits 12) * (ofBits 5) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_6 : ∀ c : K, (ofBits 12) * ((ofBits 6) + c) = (ofBits 12) * (ofBits 6) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_7 : ∀ c : K, (ofBits 12) * ((ofBits 7) + c) = (ofBits 12) * (ofBits 7) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_8 : ∀ c : K, (ofBits 12) * ((ofBits 8) + c) = (ofBits 12) * (ofBits 8) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_9 : ∀ c : K, (ofBits 12) * ((ofBits 9) + c) = (ofBits 12) * (ofBits 9) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_10 : ∀ c : K, (ofBits 12) * ((ofBits 10) + c) = (ofBits 12) * (ofBits 10) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_11 : ∀ c : K, (ofBits 12) * ((ofBits 11) + c) = (ofBits 12) * (ofBits 11) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_12 : ∀ c : K, (ofBits 12) * ((ofBits 12) + c) = (ofBits 12) * (ofBits 12) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_13 : ∀ c : K, (ofBits 12) * ((ofBits 13) + c) = (ofBits 12) * (ofBits 13) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_14 : ∀ c : K, (ofBits 12) * ((ofBits 14) + c) = (ofBits 12) * (ofBits 14) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_12_15 : ∀ c : K, (ofBits 12) * ((ofBits 15) + c) = (ofBits 12) * (ofBits 15) + (ofBits 12) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits12 : ∀ b c : K, (ofBits 12) * (b + c) = (ofBits 12) * b + (ofBits 12) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_12_0
  · exact distrib_12_1
  · exact distrib_12_2
  · exact distrib_12_3
  · exact distrib_12_4
  · exact distrib_12_5
  · exact distrib_12_6
  · exact distrib_12_7
  · exact distrib_12_8
  · exact distrib_12_9
  · exact distrib_12_10
  · exact distrib_12_11
  · exact distrib_12_12
  · exact distrib_12_13
  · exact distrib_12_14
  · exact distrib_12_15

private theorem distrib_13_0 : ∀ c : K, (ofBits 13) * ((ofBits 0) + c) = (ofBits 13) * (ofBits 0) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_1 : ∀ c : K, (ofBits 13) * ((ofBits 1) + c) = (ofBits 13) * (ofBits 1) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_2 : ∀ c : K, (ofBits 13) * ((ofBits 2) + c) = (ofBits 13) * (ofBits 2) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_3 : ∀ c : K, (ofBits 13) * ((ofBits 3) + c) = (ofBits 13) * (ofBits 3) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_4 : ∀ c : K, (ofBits 13) * ((ofBits 4) + c) = (ofBits 13) * (ofBits 4) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_5 : ∀ c : K, (ofBits 13) * ((ofBits 5) + c) = (ofBits 13) * (ofBits 5) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_6 : ∀ c : K, (ofBits 13) * ((ofBits 6) + c) = (ofBits 13) * (ofBits 6) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_7 : ∀ c : K, (ofBits 13) * ((ofBits 7) + c) = (ofBits 13) * (ofBits 7) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_8 : ∀ c : K, (ofBits 13) * ((ofBits 8) + c) = (ofBits 13) * (ofBits 8) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_9 : ∀ c : K, (ofBits 13) * ((ofBits 9) + c) = (ofBits 13) * (ofBits 9) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_10 : ∀ c : K, (ofBits 13) * ((ofBits 10) + c) = (ofBits 13) * (ofBits 10) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_11 : ∀ c : K, (ofBits 13) * ((ofBits 11) + c) = (ofBits 13) * (ofBits 11) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_12 : ∀ c : K, (ofBits 13) * ((ofBits 12) + c) = (ofBits 13) * (ofBits 12) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_13 : ∀ c : K, (ofBits 13) * ((ofBits 13) + c) = (ofBits 13) * (ofBits 13) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_14 : ∀ c : K, (ofBits 13) * ((ofBits 14) + c) = (ofBits 13) * (ofBits 14) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_13_15 : ∀ c : K, (ofBits 13) * ((ofBits 15) + c) = (ofBits 13) * (ofBits 15) + (ofBits 13) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits13 : ∀ b c : K, (ofBits 13) * (b + c) = (ofBits 13) * b + (ofBits 13) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_13_0
  · exact distrib_13_1
  · exact distrib_13_2
  · exact distrib_13_3
  · exact distrib_13_4
  · exact distrib_13_5
  · exact distrib_13_6
  · exact distrib_13_7
  · exact distrib_13_8
  · exact distrib_13_9
  · exact distrib_13_10
  · exact distrib_13_11
  · exact distrib_13_12
  · exact distrib_13_13
  · exact distrib_13_14
  · exact distrib_13_15

private theorem distrib_14_0 : ∀ c : K, (ofBits 14) * ((ofBits 0) + c) = (ofBits 14) * (ofBits 0) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_1 : ∀ c : K, (ofBits 14) * ((ofBits 1) + c) = (ofBits 14) * (ofBits 1) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_2 : ∀ c : K, (ofBits 14) * ((ofBits 2) + c) = (ofBits 14) * (ofBits 2) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_3 : ∀ c : K, (ofBits 14) * ((ofBits 3) + c) = (ofBits 14) * (ofBits 3) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_4 : ∀ c : K, (ofBits 14) * ((ofBits 4) + c) = (ofBits 14) * (ofBits 4) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_5 : ∀ c : K, (ofBits 14) * ((ofBits 5) + c) = (ofBits 14) * (ofBits 5) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_6 : ∀ c : K, (ofBits 14) * ((ofBits 6) + c) = (ofBits 14) * (ofBits 6) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_7 : ∀ c : K, (ofBits 14) * ((ofBits 7) + c) = (ofBits 14) * (ofBits 7) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_8 : ∀ c : K, (ofBits 14) * ((ofBits 8) + c) = (ofBits 14) * (ofBits 8) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_9 : ∀ c : K, (ofBits 14) * ((ofBits 9) + c) = (ofBits 14) * (ofBits 9) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_10 : ∀ c : K, (ofBits 14) * ((ofBits 10) + c) = (ofBits 14) * (ofBits 10) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_11 : ∀ c : K, (ofBits 14) * ((ofBits 11) + c) = (ofBits 14) * (ofBits 11) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_12 : ∀ c : K, (ofBits 14) * ((ofBits 12) + c) = (ofBits 14) * (ofBits 12) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_13 : ∀ c : K, (ofBits 14) * ((ofBits 13) + c) = (ofBits 14) * (ofBits 13) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_14 : ∀ c : K, (ofBits 14) * ((ofBits 14) + c) = (ofBits 14) * (ofBits 14) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_14_15 : ∀ c : K, (ofBits 14) * ((ofBits 15) + c) = (ofBits 14) * (ofBits 15) + (ofBits 14) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits14 : ∀ b c : K, (ofBits 14) * (b + c) = (ofBits 14) * b + (ofBits 14) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_14_0
  · exact distrib_14_1
  · exact distrib_14_2
  · exact distrib_14_3
  · exact distrib_14_4
  · exact distrib_14_5
  · exact distrib_14_6
  · exact distrib_14_7
  · exact distrib_14_8
  · exact distrib_14_9
  · exact distrib_14_10
  · exact distrib_14_11
  · exact distrib_14_12
  · exact distrib_14_13
  · exact distrib_14_14
  · exact distrib_14_15

private theorem distrib_15_0 : ∀ c : K, (ofBits 15) * ((ofBits 0) + c) = (ofBits 15) * (ofBits 0) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_1 : ∀ c : K, (ofBits 15) * ((ofBits 1) + c) = (ofBits 15) * (ofBits 1) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_2 : ∀ c : K, (ofBits 15) * ((ofBits 2) + c) = (ofBits 15) * (ofBits 2) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_3 : ∀ c : K, (ofBits 15) * ((ofBits 3) + c) = (ofBits 15) * (ofBits 3) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_4 : ∀ c : K, (ofBits 15) * ((ofBits 4) + c) = (ofBits 15) * (ofBits 4) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_5 : ∀ c : K, (ofBits 15) * ((ofBits 5) + c) = (ofBits 15) * (ofBits 5) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_6 : ∀ c : K, (ofBits 15) * ((ofBits 6) + c) = (ofBits 15) * (ofBits 6) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_7 : ∀ c : K, (ofBits 15) * ((ofBits 7) + c) = (ofBits 15) * (ofBits 7) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_8 : ∀ c : K, (ofBits 15) * ((ofBits 8) + c) = (ofBits 15) * (ofBits 8) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_9 : ∀ c : K, (ofBits 15) * ((ofBits 9) + c) = (ofBits 15) * (ofBits 9) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_10 : ∀ c : K, (ofBits 15) * ((ofBits 10) + c) = (ofBits 15) * (ofBits 10) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_11 : ∀ c : K, (ofBits 15) * ((ofBits 11) + c) = (ofBits 15) * (ofBits 11) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_12 : ∀ c : K, (ofBits 15) * ((ofBits 12) + c) = (ofBits 15) * (ofBits 12) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_13 : ∀ c : K, (ofBits 15) * ((ofBits 13) + c) = (ofBits 15) * (ofBits 13) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_14 : ∀ c : K, (ofBits 15) * ((ofBits 14) + c) = (ofBits 15) * (ofBits 14) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_15_15 : ∀ c : K, (ofBits 15) * ((ofBits 15) + c) = (ofBits 15) * (ofBits 15) + (ofBits 15) * c := by
  rintro ⟨c⟩
  fin_cases c <;> rfl
private theorem distrib_bits15 : ∀ b c : K, (ofBits 15) * (b + c) = (ofBits 15) * b + (ofBits 15) * c := by
  rintro ⟨b⟩
  fin_cases b
  · exact distrib_15_0
  · exact distrib_15_1
  · exact distrib_15_2
  · exact distrib_15_3
  · exact distrib_15_4
  · exact distrib_15_5
  · exact distrib_15_6
  · exact distrib_15_7
  · exact distrib_15_8
  · exact distrib_15_9
  · exact distrib_15_10
  · exact distrib_15_11
  · exact distrib_15_12
  · exact distrib_15_13
  · exact distrib_15_14
  · exact distrib_15_15

private theorem distrib_cert : ∀ a b c : K, a * (b + c) = a * b + a * c := by
  rintro ⟨a⟩
  fin_cases a
  · exact distrib_bits0
  · exact distrib_bits1
  · exact distrib_bits2
  · exact distrib_bits3
  · exact distrib_bits4
  · exact distrib_bits5
  · exact distrib_bits6
  · exact distrib_bits7
  · exact distrib_bits8
  · exact distrib_bits9
  · exact distrib_bits10
  · exact distrib_bits11
  · exact distrib_bits12
  · exact distrib_bits13
  · exact distrib_bits14
  · exact distrib_bits15
private theorem nontrivial_cert : ∃ x y : K, x ≠ y := ⟨ofBits 0, ofBits 1, by decide +kernel⟩

instance : Field K := Field.ofMinimalAxioms K
  add_assoc_cert zero_add_cert neg_add_cert mul_assoc_cert mul_comm_cert
  one_mul_cert mul_inv_cert inv_zero_cert distrib_cert nontrivial_cert

instance : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by decide +kernel)
instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The explicit bit enumeration exhausts the concrete field. -/
def bitEquiv : K ≃ Fin 16 where
  toFun := K.bits
  invFun := K.mk
  left_inv _ := rfl
  right_inv _ := rfl

theorem cardinal : Fintype.card K = 16 := by
  rw [Fintype.card_congr bitEquiv, Fintype.card_fin]

def alpha : K := ofBits 2

theorem alpha_relation : alpha ^ 4 + alpha + 1 = 0 := by decide +kernel

/-- Distinct Frobenius powers certify that alpha has degree four. -/
theorem alpha_frobenius_distinct :
    Function.Injective (fun i : Fin 4 => alpha ^ (2 ^ i.val)) := by decide +kernel

end Kourovka2135.BinaryFieldSixteen
