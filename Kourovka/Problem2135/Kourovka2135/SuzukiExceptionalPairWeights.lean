import Kourovka2135.BinaryEvenIntervals
import Kourovka2135.SuzukiPairWeightFinite

/-! Uniform arithmetic behind the fixed exceptional-gap difference graph.
The vertex values below are the twelve doubled pair weights translated by
`4r+3`. The arithmetic-to-graph implication is proved for every `r=2^m`,
`m≥3`; only the final graph bound is a finite certificate. -/

set_option autoImplicit false
namespace Kourovka2135.SuzukiExceptionalPairWeights

open Finset BinaryWeights BinaryCyclicIntervals BinaryEvenIntervals SuzukiPairWeightFinite

/-- The exceptional pair weights after a common translation. -/
def value (r : ℕ) (i : Fin 12) : ℕ :=
  ![0, 2, 2*r, 2*r+2, 2*r+4, 4*r+2, 4*r+4,
    6*r+2, 6*r+4, 6*r+6, 8*r+4, 8*r+6] i

@[simp] theorem value_0 (r : ℕ) : value r 0 = 0 := rfl
@[simp] theorem value_1 (r : ℕ) : value r 1 = 2 := rfl
@[simp] theorem value_2 (r : ℕ) : value r 2 = 2*r := rfl
@[simp] theorem value_3 (r : ℕ) : value r 3 = 2*r+2 := rfl
@[simp] theorem value_4 (r : ℕ) : value r 4 = 2*r+4 := rfl
@[simp] theorem value_5 (r : ℕ) : value r 5 = 4*r+2 := rfl
@[simp] theorem value_6 (r : ℕ) : value r 6 = 4*r+4 := rfl
@[simp] theorem value_7 (r : ℕ) : value r 7 = 6*r+2 := rfl
@[simp] theorem value_8 (r : ℕ) : value r 8 = 6*r+4 := rfl
@[simp] theorem value_9 (r : ℕ) : value r 9 = 6*r+6 := rfl
@[simp] theorem value_10 (r : ℕ) : value r 10 = 8*r+4 := rfl
@[simp] theorem value_11 (r : ℕ) : value r 11 = 8*r+6 := rfl

theorem value_le (r : ℕ) (i : Fin 12) : value r i ≤ 8*r+6 := by
  fin_cases i <;> norm_num [value] <;> omega

theorem value_even (r : ℕ) (i : Fin 12) : value r i % 2 = 0 := by
  fin_cases i <;> norm_num [value] <;> omega

theorem value_strictMono {r : ℕ} (hr : 8 ≤ r) : StrictMono (value r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [value] at * <;> omega

theorem adjacent_symm (i j : Fin 12) : adjacent i j ↔ adjacent j i := by
  revert i j
  decide +kernel

set_option maxHeartbeats 2000000 in
/-- Every forbidden graph edge has either an impossible block residue, or
would force the nonbinary coefficient six to be a power of two.  This is
symbolic in the unbounded parameter `r`; the case split is only on the
fixed twelve graph vertices. -/
theorem forbidden_difference_shape {r : ℕ} (hr : 8 ≤ r) (hdiv : 8 ∣ r)
    (i j : Fin 12) (hij : i < j) (hbad : ¬ adjacent i j) :
    let d := value r j - value r i
    8 ≤ d ∧ d % 2 = 0 ∧
      ((d % 16 ≠ 0 ∧ d % 16 ≠ 8 ∧ d % 16 ≠ 12 ∧ d % 16 ≠ 14) ∨
       (d % 16 = 12 ∧ d + 4 = 6*r) ∨
       (d % 16 = 14 ∧ d + 2 = 6*r)) := by
  obtain ⟨t, rfl⟩ := hdiv
  fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
  all_goals
    first
    | exact False.elim (hbad (by decide))
    | norm_num [value, Matrix.cons_val_succ', Nat.mul_assoc]; omega

/-- The actual uniform arithmetic-to-graph implication. -/
theorem adjacent_of_block {m : ℕ} (hm : 3 ≤ m) (i j : Fin 12)
    (hij : i < j) (hblock : IsBlock (value (2^m) j - value (2^m) i)) :
    adjacent i j := by
  have hr : 8 ≤ 2^m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hdiv : 8 ∣ 2^m := by
    refine ⟨2^(m-3), ?_⟩
    have he : m = 3 + (m-3) := by omega
    conv_lhs => rw [he, pow_add]
    norm_num
  by_contra hbad
  obtain ⟨hd, heven, hshape⟩ := forbidden_difference_shape hr hdiv i j hij hbad
  obtain ⟨hres, h12, h14⟩ := block_constraints hd heven hblock
  rcases hshape with hbadres | ⟨hr12, he12⟩ | ⟨hr14, he14⟩
  · rcases hres with h | h | h | h <;> omega
  · obtain ⟨a, ha⟩ := h12 hr12
    exact six_mul_power_ne_power m a (he12.symm.trans ha)
  · obtain ⟨a, ha⟩ := h14 hr14
    exact six_mul_power_ne_power m a (he14.symm.trans ha)

abbrev Residue (m : ℕ) := ZMod (2^(2*m+1)-1)

/-- Actual selected exceptional weights, retaining repetitions later through
`multiplicity`. -/
def selected (m : ℕ) (s : Residue m) : Finset (Fin 12) :=
  univ.filter fun i => ∃ a : Fin (2*m+1), s + (value (2^m) i : Residue m) = 2^a.val

theorem modulus_eq (m : ℕ) : 2^(2*m+1)-1 = 2*(2^m)^2-1 := by
  congr 1
  rw [show 2*m+1 = m*2+1 by omega, pow_add, pow_mul]
  ring

theorem value_lt_modulus {m : ℕ} (hm : 3 ≤ m) (i : Fin 12) :
    value (2^m) i < 2^(2*m+1)-1 := by
  have hr : 8 ≤ 2^m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hprod := Nat.mul_le_mul_right (2^m) hr
  have hv := value_le (2^m) i
  have hsub := Nat.sub_add_cancel (show 1 ≤ 2*(2^m)^2 by
    have hp : 0 < 2*(2^m)^2 := by positivity
    omega)
  rw [modulus_eq]
  nlinarith

theorem residue_value_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (fun i : Fin 12 => (value (2^m) i : Residue m)) := by
  intro i j h
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hv := he.eq_of_lt_of_lt (value_lt_modulus hm i) (value_lt_modulus hm j)
  exact (value_strictMono (by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm)).injective hv

theorem selected_adjacent {m : ℕ} (hm : 3 ≤ m) (s : Residue m)
    {i j : Fin 12} (hi : i ∈ selected m s) (hj : j ∈ selected m s) (hne : i ≠ j) :
    adjacent i j := by
  suffices hforward : ∀ i j : Fin 12, i ∈ selected m s → j ∈ selected m s →
      i < j → adjacent i j by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hforward i j hi hj hlt
    · exact (adjacent_symm i j).mpr (hforward j i hj hi hgt)
  intro i j hi hj hij
  obtain ⟨a, ha⟩ := (mem_filter.mp hi).2
  obtain ⟨b, hb⟩ := (mem_filter.mp hj).2
  have hr : 8 ≤ 2^m := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hv : value (2^m) i < value (2^m) j := value_strictMono hr hij
  let d := value (2^m) j - value (2^m) i
  have hd : 0 < d := by dsimp [d]; omega
  have hdN : d < 2^(2*m+1)-1 := lt_of_le_of_lt (Nat.sub_le _ _)
    (value_lt_modulus hm j)
  have heven : d % 2 = 0 := by
    have hiEven := value_even (2^m) i
    have hjEven := value_even (2^m) j
    dsimp [d]
    omega
  have he : (d : Residue m) = 2^b.val - 2^a.val := by
    dsimp [d]
    rw [Nat.cast_sub (Nat.le_of_lt hv)]
    linear_combination hb - ha
  exact adjacent_of_block hm i j hij
    (isBlock_of_even_difference (by omega) b.isLt a.isLt hd hdN heven he)

/-- A selected translate inherits the exact Sidon property of the Frobenius
powers. The conclusion is about actual graph vertices, not just residues. -/
theorem selected_sidon {m : ℕ} (hm : 3 ≤ m) (s : Residue m)
    {i j k l : Fin 12} (hi : i ∈ selected m s) (hj : j ∈ selected m s)
    (hk : k ∈ selected m s) (hl : l ∈ selected m s) (hne : i ≠ j)
    (h : (value (2^m) i : Residue m) - value (2^m) j =
      value (2^m) k - value (2^m) l) : i = k ∧ j = l := by
  obtain ⟨a, ha⟩ := (mem_filter.mp hi).2
  obtain ⟨b, hb⟩ := (mem_filter.mp hj).2
  obtain ⟨c, hc⟩ := (mem_filter.mp hk).2
  obtain ⟨d, hd⟩ := (mem_filter.mp hl).2
  have hab : a.val ≠ b.val := by
    intro he
    apply hne
    apply residue_value_injective hm
    have hp : (2 : Residue m)^a.val = 2^b.val := by rw [he]
    linear_combination ha - hb + hp
  have hdiff : (2 : Residue m)^a.val - 2^b.val = 2^c.val - 2^d.val := by
    linear_combination h - ha + hb + hc - hd
  obtain ⟨hac, hbd⟩ := difference_injective (by omega) a.isLt b.isLt c.isLt d.isLt hab hdiff
  constructor
  · apply residue_value_injective hm
    have hp : (2 : Residue m)^a.val = 2^c.val := by rw [hac]
    linear_combination ha - hc + hp
  · apply residue_value_injective hm
    have hp : (2 : Residue m)^b.val = 2^d.val := by rw [hbd]
    linear_combination hb - hd + hp

/-- None of the five exceptional non-Sidon quadruples is selected. -/
theorem badQuadruple_not_subset {m : ℕ} (hm : 3 ≤ m) (s : Residue m)
    (T : Finset (Fin 12)) (hT : T ∈ badQuadruples) : ¬ T ⊆ selected m s := by
  intro hsub
  simp only [badQuadruples, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl
  · have hh := selected_sidon hm s (i := 3) (j := 1) (k := 5) (l := 3)
      (hsub (by decide : (3 : Fin 12) ∈ ({1,3,5,7} : Finset (Fin 12))))
      (hsub (by decide : (1 : Fin 12) ∈ ({1,3,5,7} : Finset (Fin 12))))
      (hsub (by decide : (5 : Fin 12) ∈ ({1,3,5,7} : Finset (Fin 12))))
      (hsub (by decide : (3 : Fin 12) ∈ ({1,3,5,7} : Finset (Fin 12)))) (by decide)
      (by norm_num; ring)
    norm_num [Fin.ext_iff] at hh
  · have hh := selected_sidon hm s (i := 5) (j := 3) (k := 7) (l := 5)
      (hsub (by decide : (5 : Fin 12) ∈ ({3,4,5,7} : Finset (Fin 12))))
      (hsub (by decide : (3 : Fin 12) ∈ ({3,4,5,7} : Finset (Fin 12))))
      (hsub (by decide : (7 : Fin 12) ∈ ({3,4,5,7} : Finset (Fin 12))))
      (hsub (by decide : (5 : Fin 12) ∈ ({3,4,5,7} : Finset (Fin 12)))) (by decide)
      (by norm_num; ring)
    norm_num [Fin.ext_iff] at hh
  · have hh := selected_sidon hm s (i := 5) (j := 4) (k := 7) (l := 6)
      (hsub (by decide : (5 : Fin 12) ∈ ({4,5,6,7} : Finset (Fin 12))))
      (hsub (by decide : (4 : Fin 12) ∈ ({4,5,6,7} : Finset (Fin 12))))
      (hsub (by decide : (7 : Fin 12) ∈ ({4,5,6,7} : Finset (Fin 12))))
      (hsub (by decide : (6 : Fin 12) ∈ ({4,5,6,7} : Finset (Fin 12)))) (by decide)
      (by norm_num; ring)
    norm_num [Fin.ext_iff] at hh
  · have hh := selected_sidon hm s (i := 6) (j := 4) (k := 8) (l := 6)
      (hsub (by decide : (6 : Fin 12) ∈ ({4,6,7,8} : Finset (Fin 12))))
      (hsub (by decide : (4 : Fin 12) ∈ ({4,6,7,8} : Finset (Fin 12))))
      (hsub (by decide : (8 : Fin 12) ∈ ({4,6,7,8} : Finset (Fin 12))))
      (hsub (by decide : (6 : Fin 12) ∈ ({4,6,7,8} : Finset (Fin 12)))) (by decide)
      (by norm_num; ring)
    norm_num [Fin.ext_iff] at hh
  · have hh := selected_sidon hm s (i := 6) (j := 4) (k := 8) (l := 6)
      (hsub (by decide : (6 : Fin 12) ∈ ({4,6,8,10} : Finset (Fin 12))))
      (hsub (by decide : (4 : Fin 12) ∈ ({4,6,8,10} : Finset (Fin 12))))
      (hsub (by decide : (8 : Fin 12) ∈ ({4,6,8,10} : Finset (Fin 12))))
      (hsub (by decide : (6 : Fin 12) ∈ ({4,6,8,10} : Finset (Fin 12)))) (by decide)
      (by norm_num; ring)
    norm_num [Fin.ext_iff] at hh

/-- The doubled exceptional-gap weights have at most five Frobenius targets,
with their genuine multiplicities. -/
theorem weighted_selected_le_five {m : ℕ} (hm : 3 ≤ m) (s : Residue m) :
    ∑ i ∈ selected m s, SuzukiPairWeightFinite.multiplicity i ≤ 5 := by
  apply weighted_clique_le_five
  · intro i hi j hj hne
    exact selected_adjacent hm s hi hj hne
  · intro T hT
    exact badQuadruple_not_subset hm s T hT

end Kourovka2135.SuzukiExceptionalPairWeights
