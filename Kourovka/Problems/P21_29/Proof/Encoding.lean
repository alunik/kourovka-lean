import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Digits.Lemmas

/-! Fixed-radix encoding and the coverage facts needed for the finite checks. -/

namespace FixedRadix

/-- A width-`n` vector of digits in the alphabet `Fin base`. -/
abbrev Digits (base n : ℕ) := Fin n → Fin base

/-- Little-endian encoding of a raw fixed-width natural-number vector. -/
def encodeNat (base : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _n + 1, digits => digits 0 + base * encodeNat base (Fin.tail digits)

/-- Total little-endian decoding to `n` raw natural-number digits.

For radix zero this still has a value; `decodeNat_lt` records the positive-base
condition under which every output coordinate is a genuine radix digit.
-/
def decodeNat (base : ℕ) : (n code : ℕ) → Fin n → ℕ
  | 0, _, i => Fin.elim0 i
  | n + 1, code, i =>
      Fin.cases (code % base) (decodeNat base n (code / base)) i

@[simp]
theorem encodeNat_zero (base : ℕ) (digits : Fin 0 → ℕ) :
    encodeNat base digits = 0 :=
  rfl

@[simp]
theorem encodeNat_succ (base : ℕ) {n : ℕ} (digits : Fin (n + 1) → ℕ) :
    encodeNat base digits = digits 0 + base * encodeNat base (Fin.tail digits) :=
  rfl

@[simp]
theorem decodeNat_succ_zero (base code : ℕ) (n : ℕ) :
    decodeNat base (n + 1) code 0 = code % base :=
  rfl

@[simp]
theorem decodeNat_succ_succ (base code : ℕ) {n : ℕ} (i : Fin n) :
    decodeNat base (n + 1) code i.succ = decodeNat base n (code / base) i :=
  rfl

/-- Every coordinate produced by the total decoder is below a positive radix. -/
theorem decodeNat_lt {base : ℕ} (hbase : 0 < base) (n code : ℕ)
    (i : Fin n) : decodeNat base n code i < base := by
  induction n generalizing code with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Nat.mod_lt code hbase
      · exact ih (code := code / base) j

/-- Encoding a bounded width-`n` vector produces a canonical code. -/
theorem encodeNat_lt_pow {base n : ℕ} (digits : Fin n → ℕ)
    (hdigits : ∀ i, digits i < base) : encodeNat base digits < base ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hhead : digits 0 < base := hdigits 0
      have htail : encodeNat base (Fin.tail digits) < base ^ n :=
        ih (Fin.tail digits) (fun i => hdigits i.succ)
      calc
        encodeNat base digits
            = digits 0 + base * encodeNat base (Fin.tail digits) := rfl
        _ < base + base * encodeNat base (Fin.tail digits) :=
          Nat.add_lt_add_right hhead _
        _ = base * (encodeNat base (Fin.tail digits) + 1) := by
          simp [Nat.mul_add, Nat.add_comm]
        _ ≤ base * base ^ n :=
          Nat.mul_le_mul_left base (Nat.succ_le_iff.mpr htail)
        _ = base ^ (n + 1) := by rw [pow_succ']

/-- Decoding the encoding of bounded raw digits recovers the digits exactly. -/
theorem decodeNat_encodeNat {base n : ℕ} (hbase : 0 < base)
    (digits : Fin n → ℕ) (hdigits : ∀ i, digits i < base) :
    decodeNat base n (encodeNat base digits) = digits := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [decodeNat_succ_zero, encodeNat_succ]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hdigits 0)]
      · simp only [decodeNat_succ_succ, encodeNat_succ]
        rw [Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt (hdigits 0), zero_add]
        exact congrFun (ih (Fin.tail digits) (fun k => hdigits k.succ)) j

/-- Encode a vector whose digit bounds are carried by `Fin base`. -/
def encode (base : ℕ) {n : ℕ} (digits : Digits base n) : ℕ :=
  encodeNat base fun i => (digits i).val

/-- Decode any code to a width-`n` vector over a positive radix. -/
def decode (base : ℕ) (hbase : 0 < base) (n code : ℕ) : Digits base n :=
  fun i => ⟨decodeNat base n code i, decodeNat_lt hbase n code i⟩

/-- Encodings of typed digit vectors are canonical. -/
theorem encode_lt_pow {base n : ℕ} (digits : Digits base n) :
    encode base digits < base ^ n :=
  encodeNat_lt_pow (fun i => (digits i).val) (fun i => (digits i).isLt)

/-- Typed decoding is a left inverse of encoding for every positive radix. -/
theorem decode_encode {base n : ℕ} (hbase : 0 < base)
    (digits : Digits base n) :
    decode base hbase n (encode base digits) = digits := by
  apply funext
  intro i
  apply Fin.ext
  exact congrFun
    (decodeNat_encodeNat hbase (fun j => (digits j).val)
      (fun j => (digits j).isLt)) i

end FixedRadix
