import Kourovka2135.BinaryCyclicIntervals

/-! Rotation of actual finite binary supports, and equality of their residues.
All cardinality arguments are for subsets of the actual exponent cycle. -/

set_option autoImplicit false
namespace Kourovka2135.BinaryCyclicRotations

open Finset BinaryWeights BinaryCyclicIntervals

def rotate (f j : ℕ) (I : Finset ℕ) : Finset ℕ := I.image fun i => (i+j)%f

theorem rotation_injOn {f : ℕ} (j : ℕ) {I : Finset ℕ} (hI : I ⊆ range f) :
    Set.InjOn (fun i : ℕ => (i+j)%f) I := by
  intro a ha b hb he
  exact cyclic_add_injective (mem_range.mp (hI ha)) (mem_range.mp (hI hb)) j he

theorem rotate_subset {f : ℕ} (hf : 0 < f) (j : ℕ) (I : Finset ℕ) :
    rotate f j I ⊆ range f := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := mem_image.mp ha
  exact mem_range.mpr (Nat.mod_lt _ hf)

theorem rotate_card {f : ℕ} (j : ℕ) {I : Finset ℕ} (hI : I ⊆ range f) :
    (rotate f j I).card = I.card := card_image_of_injOn (rotation_injOn j hI)

theorem rotate_range {f : ℕ} (hf : 0 < f) (j : ℕ) :
    rotate f j (range f) = range f := by
  apply eq_of_subset_of_card_le (rotate_subset hf j _)
  rw [rotate_card j Subset.rfl]

theorem rotate_ne_range {f : ℕ} (j : ℕ) {I : Finset ℕ}
    (hI : I ⊆ range f) (hne : I ≠ range f) : rotate f j I ≠ range f := by
  intro h
  apply hne
  apply eq_of_subset_of_card_le hI
  rw [← rotate_card j hI, h]

theorem rotate_complement {f : ℕ} (hf : 0 < f) (j : ℕ)
    {I : Finset ℕ} (hI : I ⊆ range f) :
    rotate f j (range f \ I) = range f \ rotate f j I := by
  unfold rotate
  rw [image_sdiff_of_injOn (rotation_injOn j Subset.rfl) hI]
  change rotate f j (range f) \ rotate f j I = _
  rw [rotate_range hf]
  rfl

/-- Rotating the support multiplies its actual modular binary weight by the
corresponding power of two. -/
theorem rotate_weight {f : ℕ} (j : ℕ) {I : Finset ℕ} (hI : I ⊆ range f) :
    (weight (rotate f j I) : ZMod (2^f-1)) =
      2^j * (weight I : ZMod (2^f-1)) := by
  unfold weight rotate
  rw [sum_image (rotation_injOn j hI)]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (two_pow_modEq_reduced f (i+j))
  push_cast at h
  simpa only [pow_add, mul_comm] using h.symm

theorem rotate_weight_eq_iff {f : ℕ} (hf : 0 < f) (j : ℕ)
    {I J : Finset ℕ} (hI : I ⊆ range f) (hJ : J ⊆ range f)
    (hI' : I ≠ range f) (hJ' : J ≠ range f) :
    (2 : ZMod (2^f-1))^j * (weight I : ZMod (2^f-1)) = weight J ↔
      rotate f j I = J := by
  rw [← rotate_weight j hI]
  rw [ZMod.natCast_eq_natCast_iff]
  exact weight_modEq_iff (rotate_subset hf j I) hJ (rotate_ne_range j hI hI') hJ'

/-- Complementation negates a binary weight modulo the torus order. -/
theorem complement_weight {f : ℕ} {I : Finset ℕ} (hI : I ⊆ range f) :
    (weight (range f \ I) : ZMod (2^f-1)) = -(weight I : ZMod (2^f-1)) := by
  have hs := sum_sdiff (f := fun i : ℕ => 2^i) hI
  change weight (range f \ I) + weight I = weight (range f) at hs
  rw [weight_range] at hs
  have hh := congrArg (fun n : ℕ => (n : ZMod (2^f-1))) hs
  push_cast at hh
  have hn : ((2^f-1 : ℕ) : ZMod (2^f-1)) = 0 := by simp
  rw [hn] at hh
  exact eq_neg_of_add_eq_zero_left hh

/-- A sum of two reduced indices wraps at most once. -/
theorem reduced_add_eq {f x j y : ℕ} (hf : 0 < f)
    (hx : x < f) (hj : j < f) (_hy : y < f) (h : (x+j)%f = y) :
    x+j = y ∨ x+j = y+f := by
  have hq : (x+j)/f < 2 := (Nat.div_lt_iff_lt_mul hf).mpr (by omega)
  have hd := Nat.mod_add_div (x+j) f
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq)) with hzero | hone
  · rw [h, hzero] at hd
    exact Or.inl (by simpa using hd.symm)
  · rw [h, hone] at hd
    exact Or.inr (by simpa using hd.symm)

/-- Explicit endpoint alternatives for a rotated two-element support. -/
theorem rotate_pair_eq_cases {f j x y a b : ℕ}
    (h : rotate f j {x,y} = {a,b}) :
    ((x+j)%f = a ∧ (y+j)%f = b) ∨
      ((x+j)%f = b ∧ (y+j)%f = a) := by
  have hs := congrArg (fun I : Finset ℕ => (I : Set ℕ)) h
  simp only [rotate, image_insert, image_singleton, coe_insert, coe_singleton] at hs
  exact Set.pair_eq_pair_iff.mp hs

end Kourovka2135.BinaryCyclicRotations
