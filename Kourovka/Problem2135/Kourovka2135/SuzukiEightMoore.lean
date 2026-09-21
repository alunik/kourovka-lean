import Kourovka2135.SuzukiTorusMovingRank
import Mathlib.Algebra.CharP.Two

/-! Explicit field-of-eight identities for the exceptional Suzuki triple
pairing. The nonzero Moore value is obtained by avoiding at most four field
elements; there is no enumerated field model or computation oracle. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightMoore

open scoped CharTwo

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The cyclic Moore polynomial attached to the Suzuki commutator. -/
def moore (a b c : F) : F :=
  c ^ 2 * (a * b ^ 4 + b * a ^ 4) +
    a ^ 2 * (b * c ^ 4 + c * b ^ 4) +
    b ^ 2 * (c * a ^ 4 + a * c ^ 4)

omit [CharP F 2] in
theorem pow_eight (hcard : Nat.card F = 8) (x : F) : x ^ 8 = x := by
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 8 := by simpa only [Nat.card_eq_fintype_card] using hcard
  simpa only [hc] using FiniteField.pow_card x

omit [CharP F 2] in
/-- Inverse fifth-power scaling is the Frobenius square on all of F8. -/
theorem inverse_fifth (hcard : Nat.card F = 8) (x : F) : (x ^ 5)⁻¹ = x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  · let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = 8 := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    have hseven : x ^ 7 = 1 := by
      simpa only [hc] using FiniteField.pow_card_sub_one_eq_one x hx
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_add]
    exact hseven

/-- Squaring permutes the six monomials with exponents one, two and four. -/
theorem moore_square (hcard : Nat.card F = 8) (a b c : F) :
    moore a b c ^ 2 = moore a b c := by
  simp only [moore, CharTwo.add_sq, mul_pow, ← pow_mul]
  simp only [pow_eight hcard a, pow_eight hcard b, pow_eight hcard c]
  ring

omit [Finite F] in
/-- The factorization proves nonvanishing for any binary-independent triple. -/
theorem moore_one_factor (b c : F) :
    moore 1 b c = (b ^ 2 + b) * c * (c + 1) * (c + b) * (c + b + 1) := by
  unfold moore
  ring_nf
  simp

/-- The Moore polynomial takes the value one, without choosing a field model. -/
theorem exists_moore_one (hcard : Nat.card F = 8) :
    ∃ b c : F, moore 1 b c = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 8 := by simpa only [Nat.card_eq_fintype_card] using hcard
  have htwo : ({0, 1} : Finset F).card ≤ 2 := by
    have h := Finset.card_insert_le (0 : F) {1}
    simpa only [Finset.card_singleton] using h
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ, hc]
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have hfour : ({0, 1, b, b + 1} : Finset F).card ≤ 4 := by
    have h₁ := Finset.card_insert_le (0 : F) {1, b, b + 1}
    have h₂ := Finset.card_insert_le (1 : F) {b, b + 1}
    have h₃ := Finset.card_insert_le b {b + 1}
    simp only [Finset.card_singleton] at h₃
    omega
  obtain ⟨c, _, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, b, b + 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ, hc]
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
  have hbplus : b + 1 ≠ 0 := fun h => hb.2 (CharTwo.add_eq_zero.mp h)
  have hbpoly : b ^ 2 + b ≠ 0 := by
    simpa only [pow_two, mul_add, mul_one] using mul_ne_zero hb.1 hbplus
  have hcplus : c + 1 ≠ 0 := fun h => hcn.2.1 (CharTwo.add_eq_zero.mp h)
  have hcb : c + b ≠ 0 := fun h => hcn.2.2.1 (CharTwo.add_eq_zero.mp h)
  have hcbplus : c + b + 1 ≠ 0 := by
    intro h
    apply hcn.2.2.2
    apply CharTwo.add_eq_zero.mp
    simpa only [add_assoc] using h
  have hn : moore 1 b c ≠ 0 := by
    rw [moore_one_factor]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hbpoly hcn.1)
      hcplus) hcb) hcbplus
  refine ⟨b, c, ?_⟩
  apply mul_left_cancel₀ hn
  simpa only [pow_two, mul_one] using moore_square hcard 1 b c

/-- The actual Suzuki field at parameter one has eight elements. -/
theorem card_actual : Nat.card (SuzukiTorusMovingRank.K 1) = 8 := by
  simpa using SuzukiTorusMovingRank.card_field 1

end Kourovka2135.SuzukiEightMoore
