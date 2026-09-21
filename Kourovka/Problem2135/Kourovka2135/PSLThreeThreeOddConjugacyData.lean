import Kourovka2135.PSLThreeThreeSemidihedralData
import Mathlib.Algebra.BigOperators.Fin

/-! Finite matrix encoding and twelve explicit conjugacy representatives for
SL3(F3). The first seven have odd order. Exhaustiveness is established by the
separate finite certificate, rather than assumed here. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Kourovka2135.PSLThreeThreeOddConjugacyData
open scoped MatrixGroups
open Matrix
abbrev S := SL(3, ZMod 3)
abbrev Q := PSL(3, ZMod 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 3)

/-- Row-major flattening; the first matrix coordinate is the low ternary digit. -/
def matrixVectorEquiv : Mat ≃ (Fin 9 → Fin 3) where
  toFun A n := (ZMod.finEquiv 3).symm
    (A ⟨n.val / 3, by omega⟩ ⟨n.val % 3, Nat.mod_lt _ (by decide)⟩)
  invFun v i j := (ZMod.finEquiv 3)
    (v ⟨i.val * 3 + j.val, by omega⟩)
  left_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv v := by
    funext n
    fin_cases n <;> rfl

def matrixCodeEquiv : Mat ≃ Fin 19683 := matrixVectorEquiv.trans finFunctionFinEquiv

def decode (n : ℕ) : Mat := matrixCodeEquiv.symm ⟨n % 19683, Nat.mod_lt _ (by decide)⟩

theorem decode_code (A : Mat) : decode (matrixCodeEquiv A).val = A := by
  have hn := (matrixCodeEquiv A).isLt
  simp only [decode, Nat.mod_eq_of_lt hn, Fin.eta, Equiv.symm_apply_apply]

def representativeMatrix : Fin 12 → Mat :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 1; 0, 0, 1],
    !![1, 1, 2; 1, 0, 0; 1, 1, 1],
    !![1, 0, 1; 1, 1, 2; 0, 2, 0],
    !![1, 2, 1; 2, 2, 0; 2, 2, 1],
    !![0, 2, 2; 0, 1, 2; 2, 1, 2],
    !![2, 0, 0; 0, 2, 0; 0, 0, 1],
    !![1, 1, 0; 1, 2, 0; 0, 0, 1],
    !![2, 2, 0; 0, 2, 0; 0, 0, 1],
    !![0, 1, 0; 1, 1, 0; 0, 0, 2],
    !![0, 2, 0; 2, 2, 0; 0, 0, 2]]

theorem representativeMatrix_det (i : Fin 12) : (representativeMatrix i).det = 1 := by
  exact (by decide : ∀ j : Fin 12, (representativeMatrix j).det = 1) i

def representative (i : Fin 12) : S := ⟨representativeMatrix i, representativeMatrix_det i⟩
def representativeOrder : Fin 12 → ℕ := ![1, 3, 3, 13, 13, 13, 13, 2, 4, 6, 8, 8]

theorem representative_order (i : Fin 12) : orderOf (representative i) = representativeOrder i := by
  apply (orderOf_eq_iff ((by decide : ∀ j : Fin 12, 0 < representativeOrder j) i)).mpr
  constructor
  · exact (by decide : ∀ j : Fin 12, representative j ^ representativeOrder j = 1) i
  · intro m hm hpos
    exact (by decide : ∀ j : Fin 12, ∀ n : Fin (representativeOrder j),
      0 < n.val → representative j ^ n.val ≠ 1) i ⟨m, hm⟩ hpos

theorem odd_representativeOrder_iff (i : Fin 12) : Odd (representativeOrder i) ↔ i.val < 7 := by
  exact (by decide : ∀ j : Fin 12, Odd (representativeOrder j) ↔ j.val < 7) i

def oddRepresentative (i : Fin 7) : S := representative (i.castLE (by decide))

theorem oddRepresentative_order_odd (i : Fin 7) : Odd (orderOf (oddRepresentative i)) := by
  rw [oddRepresentative, representative_order, odd_representativeOrder_iff]
  exact i.isLt

/-- The packed entry stores a conjugator code and one of the twelve indices.
The equality avoids computing an inverse: c*r=g*c gives the actual conjugacy. -/
def EntryOK (code entry : ℕ) : Prop :=
  (decode code).det = 1 →
    (decode (entry / 12)).det = 1 ∧
      decode (entry / 12) * representativeMatrix ⟨entry % 12, Nat.mod_lt _ (by decide)⟩ =
        decode code * decode (entry / 12)

instance entryOKDecidable (code entry : ℕ) : Decidable (EntryOK code entry) :=
  inferInstanceAs (Decidable ((decode code).det = 1 →
    (decode (entry / 12)).det = 1 ∧
      decode (entry / 12) * representativeMatrix ⟨entry % 12, Nat.mod_lt _ (by decide)⟩ =
        decode code * decode (entry / 12)))

end Kourovka2135.PSLThreeThreeOddConjugacyData
