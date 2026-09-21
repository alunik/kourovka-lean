import Kourovka2135.BinaryCyclicRotations

/-! The only nonzero twist gaps producing a repeated Suzuki pair weight are
`m` and `m+1`, for cycle length `2m+1`. This is an actual binary-support
rotation statement, rather than an assumption of distinct tensor weights. -/

set_option autoImplicit false
namespace Kourovka2135.SuzukiPairWeightCollisions

open Finset BinaryWeights BinaryCyclicIntervals BinaryCyclicRotations

/-- The four positive difference supports of the natural weight set. -/
def positiveSupport (m : ℕ) (t : Fin 4) : Finset ℕ :=
  ![{0}, {m+1}, {0,m+1}, {1,m+1}] t

theorem positiveSupport_subset {m : ℕ} (hm : 2 ≤ m) (t : Fin 4) :
    positiveSupport m t ⊆ range (2*m+1) := by
  intro x hx
  fin_cases t <;> simp [positiveSupport] at hx <;>
    simp only [mem_range] <;> omega

theorem positiveSupport_card {m : ℕ} (hm : 2 ≤ m) (t : Fin 4) :
    (positiveSupport m t).card = if t.val < 2 then 1 else 2 := by
  fin_cases t
  · rfl
  · rfl
  · change ({0,m+1} : Finset ℕ).card = 2
    exact card_pair (by omega)
  · change ({1,m+1} : Finset ℕ).card = 2
    exact card_pair (by omega)

theorem positiveSupport_ne_range {m : ℕ} (hm : 2 ≤ m) (t : Fin 4) :
    positiveSupport m t ≠ range (2*m+1) := by
  intro h
  have hh := congrArg Finset.card h
  rw [positiveSupport_card hm, card_range] at hh
  split_ifs at hh <;> omega

/-- Exact rotation restrictions for the four positive difference supports. -/
theorem positive_rotation_gap {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2*m+1)
    (u v : Fin 4) (h : rotate (2*m+1) j (positiveSupport m u) = positiveSupport m v) :
    j = 0 ∨ j = m ∨ j = m+1 := by
  have hcard := congrArg Finset.card h
  rw [rotate_card j (positiveSupport_subset hm u), positiveSupport_card hm,
    positiveSupport_card hm] at hcard
  fin_cases u <;> fin_cases v <;> norm_num at hcard
  · have hx : (0+j)%(2*m+1) = 0 := by simpa [positiveSupport, rotate] using h
    have := reduced_add_eq (by omega) (by omega) hj (by omega) hx
    omega
  · have hx : (0+j)%(2*m+1) = m+1 := by simpa [positiveSupport, rotate] using h
    have := reduced_add_eq (by omega) (by omega) hj (by omega) hx
    omega
  · have hx : (m+1+j)%(2*m+1) = 0 := by simpa [positiveSupport, rotate] using h
    have := reduced_add_eq (by omega) (by omega) hj (by omega) hx
    omega
  · have hx : (m+1+j)%(2*m+1) = m+1 := by simpa [positiveSupport, rotate] using h
    have := reduced_add_eq (by omega) (by omega) hj (by omega) hx
    omega
  · change rotate (2*m+1) j {0,m+1} = {0,m+1} at h
    rcases rotate_pair_eq_cases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals
      have hx' := reduced_add_eq (by omega) (by omega) hj (by omega) hx
      have hy' := reduced_add_eq (by omega) (by omega) hj (by omega) hy
      omega
  · change rotate (2*m+1) j {0,m+1} = {1,m+1} at h
    rcases rotate_pair_eq_cases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals
      have hx' := reduced_add_eq (by omega) (by omega) hj (by omega) hx
      have hy' := reduced_add_eq (by omega) (by omega) hj (by omega) hy
      omega
  · change rotate (2*m+1) j {1,m+1} = {0,m+1} at h
    rcases rotate_pair_eq_cases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals
      have hx' := reduced_add_eq (by omega) (by omega) hj (by omega) hx
      have hy' := reduced_add_eq (by omega) (by omega) hj (by omega) hy
      omega
  · change rotate (2*m+1) j {1,m+1} = {1,m+1} at h
    rcases rotate_pair_eq_cases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals
      have hx' := reduced_add_eq (by omega) (by omega) hj (by omega) hx
      have hy' := reduced_add_eq (by omega) (by omega) hj (by omega) hy
      omega

/-- A negative difference is encoded by the complementary binary support. -/
def signedSupport (m : ℕ) (neg : Bool) (t : Fin 4) : Finset ℕ :=
  if neg then range (2*m+1) \ positiveSupport m t else positiveSupport m t

theorem signedSupport_subset {m : ℕ} (hm : 2 ≤ m) (neg : Bool) (t : Fin 4) :
    signedSupport m neg t ⊆ range (2*m+1) := by
  cases neg
  · exact positiveSupport_subset hm t
  · exact sdiff_subset

theorem signedSupport_ne_range {m : ℕ} (hm : 2 ≤ m) (neg : Bool) (t : Fin 4) :
    signedSupport m neg t ≠ range (2*m+1) := by
  cases neg
  · exact positiveSupport_ne_range hm t
  · intro he
    have hp : 0 < (positiveSupport m t).card := by
      rw [positiveSupport_card hm]
      split_ifs <;> omega
    obtain ⟨x, hx⟩ := card_pos.mp hp
    have hr := positiveSupport_subset hm t hx
    have hn : x ∈ range (2*m+1) \ positiveSupport m t := by
      change x ∈ signedSupport m true t
      rw [he]
      exact hr
    exact (mem_sdiff.mp hn).2 hx

theorem signedSupport_card {m : ℕ} (hm : 2 ≤ m) (neg : Bool) (t : Fin 4) :
    (signedSupport m neg t).card =
      if neg then (2*m+1) - (if t.val < 2 then 1 else 2)
      else if t.val < 2 then 1 else 2 := by
  cases neg
  · exact positiveSupport_card hm t
  · change (range (2*m+1) \ positiveSupport m t).card =
      (2*m+1) - (if t.val < 2 then 1 else 2)
    rw [card_sdiff_of_subset (positiveSupport_subset hm t), card_range, positiveSupport_card hm]

theorem signedSupport_weight {m : ℕ} (hm : 2 ≤ m) (neg : Bool) (t : Fin 4) :
    (weight (signedSupport m neg t) : ZMod (2^(2*m+1)-1)) =
      if neg then -(weight (positiveSupport m t) : ZMod (2^(2*m+1)-1))
      else weight (positiveSupport m t) := by
  cases neg
  · rfl
  · exact complement_weight (positiveSupport_subset hm t)

/-- Rotations of signed natural differences cannot mix signs, since their
binary support cardinalities are `1,2,f−2,f−1` with `f≥5`. -/
theorem signed_rotation_gap {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2*m+1)
    (u v : Fin 4) (nu nv : Bool)
    (h : (weight (signedSupport m nu u) : ZMod (2^(2*m+1)-1)) =
      2^j * (weight (signedSupport m nv v) : ZMod (2^(2*m+1)-1))) :
    j = 0 ∨ j = m ∨ j = m+1 := by
  have hs := (rotate_weight_eq_iff (by omega : 0 < 2*m+1) j
    (signedSupport_subset hm nv v) (signedSupport_subset hm nu u)
    (signedSupport_ne_range hm nv v) (signedSupport_ne_range hm nu u)).mp h.symm
  have hc := congrArg Finset.card hs
  rw [rotate_card j (signedSupport_subset hm nv v), signedSupport_card hm,
    signedSupport_card hm] at hc
  have hsign : nu = nv := by
    cases nu <;> cases nv <;> try rfl
    all_goals simp at hc; split_ifs at hc <;> omega
  subst nv
  have hp : (2 : ZMod (2^(2*m+1)-1))^j * weight (positiveSupport m v) =
      weight (positiveSupport m u) := by
    rw [signedSupport_weight hm, signedSupport_weight hm] at h
    cases nu
    · exact h.symm
    · simpa only [↓reduceIte, mul_neg, neg_inj] using h.symm
  exact positive_rotation_gap hm hj v u
    ((rotate_weight_eq_iff (by omega) j (positiveSupport_subset hm v)
      (positiveSupport_subset hm u) (positiveSupport_ne_range hm v)
      (positiveSupport_ne_range hm u)).mp hp)

abbrev Residue (m : ℕ) := ZMod (2^(2*m+1)-1)

/-- A common translation puts the natural four weights in increasing order. -/
def baseValue (r : ℕ) (i : Fin 4) : ℕ := ![0,1,2*r+1,2*r+2] i

def baseWeight (m : ℕ) (i : Fin 4) : Residue m :=
  (baseValue (2^m) i : Residue m) - (2^m : ℕ) - 1

/-- Index of the positive magnitude of a difference; diagonal entries are
irrelevant and deliberately carry no separate meaning. -/
def differenceType (i j : Fin 4) : Fin 4 :=
  (!![0,0,2,3; 0,0,1,2; 2,1,0,0; 3,2,0,0] : Matrix (Fin 4) (Fin 4) (Fin 4)) i j

theorem base_difference {m : ℕ} (hm : 2 ≤ m) (i j : Fin 4) (hij : i ≠ j) :
    baseWeight m i - baseWeight m j =
      (weight (signedSupport m (decide (i < j)) (differenceType i j)) : Residue m) := by
  rw [signedSupport_weight hm]
  have h0 : 0 ≠ m+1 := by omega
  have h1 : 1 ≠ m+1 := by omega
  fin_cases i <;> fin_cases j <;>
    norm_num [baseWeight, baseValue, differenceType, positiveSupport, weight,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.lt_def, h0, h1, pow_succ] at * <;> try ring
  all_goals
    rw [sum_pair (by omega : 1 ≠ 1+m)]
    norm_num [pow_add]
    ring

/-- Every equality between rotated nonzero natural differences has precisely
the three stated possible gaps. -/
theorem difference_rotation_gap {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2*m+1)
    (a b c d : Fin 4) (hab : a ≠ b) (hcd : c ≠ d)
    (h : baseWeight m a - baseWeight m b = 2^j * (baseWeight m c - baseWeight m d)) :
    j = 0 ∨ j = m ∨ j = m+1 := by
  rw [base_difference hm a b hab, base_difference hm c d hcd] at h
  exact signed_rotation_gap hm hj (differenceType a b) (differenceType c d)
    (decide (a < b)) (decide (c < d)) h

end Kourovka2135.SuzukiPairWeightCollisions
