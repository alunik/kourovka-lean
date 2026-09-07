import Kourovka.Problems.P21_29.Proof.LinearGroup
import Kourovka.Problems.P21_29.Proof.Encoding

/-! Explicit indices for the linear group and its nine-dimensional module. -/

namespace Kourovka.P21_29

def dElement (i : Fin 64) : D := complete fun a b =>
  Multiplicative.ofAdd
    (((FixedRadix.decode 2 (by omega) 6 i.val ⟨2 * a.val + b.val, by omega⟩).val) : ZMod 2)

def pElement (i : Fin 18) : P :=
  if i.val < 9 then .r i.val else .sr (i.val - 9)

def groupElement (i : Fin 1152) : H :=
  ⟨dElement ⟨i.val % 64, Nat.mod_lt _ (by omega)⟩,
    pElement ⟨i.val / 64, by omega⟩⟩

theorem dElement_surjective : Function.Surjective dElement := by decide +kernel

theorem pElement_surjective : Function.Surjective pElement := by decide +kernel

theorem groupElement_surjective : Function.Surjective groupElement := by
  intro g
  obtain ⟨a, ha⟩ := dElement_surjective g.left
  obtain ⟨b, hb⟩ := pElement_surjective g.right
  refine ⟨⟨64 * b.val + a.val, by omega⟩, ?_⟩
  apply SemidirectProduct.ext
  · change dElement ⟨(64 * b.val + a.val) % 64, _⟩ = g.left
    rw [← ha]
    apply congrArg dElement
    apply Fin.ext
    dsimp
    omega
  · change pElement ⟨(64 * b.val + a.val) / 64, _⟩ = g.right
    rw [← hb]
    apply congrArg pElement
    apply Fin.ext
    dsimp
    omega

def vector (code : ℕ) : V := fun x =>
  ((FixedRadix.decode 3 (by omega) 9 code x).val : ZMod 3)

def vectorDigits (v : V) : FixedRadix.Digits 3 9 :=
  fun x => ⟨(v x).val, ZMod.val_lt _⟩

def vectorCode (v : V) : ℕ := FixedRadix.encode 3 (vectorDigits v)

theorem vector_vectorCode (v : V) : vector (vectorCode v) = v := by
  funext x
  have h := congrFun (FixedRadix.decode_encode (by omega) (vectorDigits v)) x
  simpa [vector, vectorCode, vectorDigits] using
    congrArg (fun z : Fin 3 => (z.val : ZMod 3)) h

theorem vectorCode_lt (v : V) : vectorCode v < 19683 := by
  simpa only [vectorCode, show 3 ^ 9 = 19683 by norm_num] using
    FixedRadix.encode_lt_pow (vectorDigits v)

/-- Zero on the residue class of zero modulo three, and one elsewhere. -/
def hole : V := fun x => if x.val % 3 = 0 then 0 else 1

/-- One zero; the products on the two zero-free blocks are opposite. -/
def regularVector : V := fun x => if x = 0 then 0 else if x = 2 then 2 else 1

/-- A witness stores a nonidentity linear element and which difference it fixes. -/
def obstructionCheck (code witness : ℕ) : Bool :=
  let g := groupElement ⟨witness % 1152, Nat.mod_lt _ (by omega)⟩
  let v := if witness < 1152 then vector code else vector code - hole
  decide ((g.left.1 ≠ 1 ∨ g.right ≠ 1) ∧ g • v = v)

theorem obstructionCheck_sound {code witness : ℕ}
    (h : obstructionCheck code witness = true) :
    (∃ g : H, g ≠ 1 ∧ g • vector code = vector code) ∨
      (∃ g : H, g ≠ 1 ∧ g • (vector code - hole) = vector code - hole) := by
  have nonidentity (g : H) (hg : g.left.1 ≠ 1 ∨ g.right ≠ 1) : g ≠ 1 := by
    rintro rfl
    rcases hg with hg | hg <;> exact hg rfl
  unfold obstructionCheck at h
  split_ifs at h with hw
  · have hh := of_decide_eq_true h
    exact Or.inl ⟨_, nonidentity _ hh.1, hh.2⟩
  · have hh := of_decide_eq_true h
    exact Or.inr ⟨_, nonidentity _ hh.1, hh.2⟩

end Kourovka.P21_29
