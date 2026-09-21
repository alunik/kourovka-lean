import Kourovka2135.SuzukiEightMoore
import Kourovka2135.ScalarInvariantBiadditive
import Mathlib.GroupTheory.Index

/-! An invariant biadditive form with Suzuki F8 weights five and one,
satisfying the actual cyclic Jacobi equation, generates an elementary
binary additive subgroup of order at most four. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightPairingBound

open SuzukiEightMoore
open scoped CharTwo

variable {F A : Type*} [Field F] [AddCommGroup A]

/-- Restriction to second input one is an actual additive homomorphism. -/
def parameter (B : F →+ (F →+ A)) : F →+ A where
  toFun d := B d 1
  map_zero' := by simp
  map_add' x y := by simp

@[simp] theorem parameter_apply (B : F →+ (F →+ A)) (d : F) :
    parameter B d = B d 1 := rfl

def pairingValues (B : F →+ (F →+ A)) : Set A :=
  Set.range (fun p : F × F => B p.1 p.2)

def pairingSpan (B : F →+ (F →+ A)) : AddSubgroup A :=
  AddSubgroup.closure (pairingValues B)

variable [Finite F]
variable (hcard : Nat.card F = 8) (B : F →+ (F →+ A))
variable (hB : ∀ (u : Fˣ) (d a : F), B ((u : F) ^ 5 * d) ((u : F) * a) = B d a)

include hcard hB in
/-- The entire form is the Frobenius-square scalar form associated to its parameter. -/
theorem reconstruct (d a : F) : B d a = parameter B (d * a ^ 2) := by
  rw [ScalarInvariantBiadditive.value_eq 5 (by decide) B hB d a,
    inverse_fifth hcard a, mul_comm]
  rfl

include hcard hB in
/-- Invariance makes the set of values an additive subgroup, not just a generating set. -/
theorem pairingValues_eq_range : pairingValues B = (parameter B).range := by
  ext v
  constructor
  · rintro ⟨⟨d, a⟩, rfl⟩
    exact ⟨d * a ^ 2, (reconstruct hcard B hB d a).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨(d, 1), rfl⟩

include hcard hB in
theorem pairingSpan_eq_range : pairingSpan B = (parameter B).range := by
  rw [pairingSpan, pairingValues_eq_range hcard B hB, AddSubgroup.closure_eq]

include hcard hB in
/-- The generated value subgroup is finite even when the target group is infinite. -/
theorem finite_pairingSpan : Finite (pairingSpan B) := by
  rw [pairingSpan_eq_range hcard B hB]
  exact Finite.of_surjective (parameter B).rangeRestrict
    (parameter B).rangeRestrict_surjective

variable [CharP F 2]

include hcard hB in
/-- Every value has additive order dividing two. -/
theorem add_self_eq_zero_of_mem_pairingSpan (v : A) (hv : v ∈ pairingSpan B) :
    v + v = 0 := by
  rw [pairingSpan_eq_range hcard B hB] at hv
  obtain ⟨d, rfl⟩ := hv
  rw [← map_add]
  simp

variable (hJacobi : ∀ a b c : F,
  B (a * b ^ 4 + b * a ^ 4) c +
    B (b * c ^ 4 + c * b ^ 4) a +
    B (c * a ^ 4 + a * c ^ 4) b = 0)

include hcard hB hJacobi in
/-- Hall-Witt's scalar Jacobi equation kills one under the parameter map. -/
theorem parameter_one_eq_zero : parameter B 1 = 0 := by
  obtain ⟨b, c, hbc⟩ := exists_moore_one hcard
  have h := hJacobi 1 b c
  rw [reconstruct hcard B hB, reconstruct hcard B hB,
    reconstruct hcard B hB, ← map_add, ← map_add] at h
  have he : (1 * b ^ 4 + b * 1 ^ 4) * c ^ 2 +
      (b * c ^ 4 + c * b ^ 4) * 1 ^ 2 +
      (c * 1 ^ 4 + 1 * c ^ 4) * b ^ 2 = moore 1 b c := by
    unfold moore
    ring
  rw [he, hbc] at h
  exact h

omit [CharP F 2] in
include hcard in
/-- Killing one forces a kernel of size at least two in the eight-element domain. -/
theorem card_range_le_four_of_map_one_zero (f : F →+ A) (hf : f 1 = 0) :
    Nat.card f.range ≤ 4 := by
  have hne : (⟨1, hf⟩ : f.ker) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  let : Nontrivial f.ker := nontrivial_of_ne _ _ hne
  have hk : 2 ≤ Nat.card f.ker := Finite.one_lt_card
  have he := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, hcard] at he
  have hle := Nat.mul_le_mul_right (Nat.card f.range) hk
  rw [he] at hle
  omega

include hcard hB hJacobi in
/-- The actual generated image has at most four elements. -/
theorem card_pairingSpan_le_four : Nat.card (pairingSpan B) ≤ 4 := by
  rw [pairingSpan_eq_range hcard B hB]
  exact card_range_le_four_of_map_one_zero hcard (parameter B)
    (parameter_one_eq_zero hcard B hB hJacobi)

omit [CharP F 2] in
include hcard hB in
/-- If the pairing values generate the target, the target is finite. -/
theorem finite_of_pairingSpan_eq_top (hgen : pairingSpan B = ⊤) : Finite A := by
  have hfin := finite_pairingSpan hcard B hB
  rw [hgen] at hfin
  let : Finite (⊤ : AddSubgroup A) := hfin
  exact Finite.of_equiv (⊤ : AddSubgroup A) AddSubgroup.topEquiv.toEquiv

include hcard hB hJacobi in
/-- Generation upgrades the image bound to a bound on the whole target. -/
theorem card_le_four_of_pairingSpan_eq_top (hgen : pairingSpan B = ⊤) : Nat.card A ≤ 4 := by
  have h := card_pairingSpan_le_four hcard B hB hJacobi
  rw [hgen, Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h
  exact h

/-- Specialization to the actual field used by the Suzuki group at parameter one. -/
theorem actual_card_pairingSpan_le_four
    (C : SuzukiTorusMovingRank.K 1 →+ (SuzukiTorusMovingRank.K 1 →+ A))
    (hC : ∀ (u : (SuzukiTorusMovingRank.K 1)ˣ) (d a : SuzukiTorusMovingRank.K 1),
      C ((u : SuzukiTorusMovingRank.K 1) ^ 5 * d)
        ((u : SuzukiTorusMovingRank.K 1) * a) = C d a)
    (hJ : ∀ a b c : SuzukiTorusMovingRank.K 1,
      C (a * b ^ 4 + b * a ^ 4) c +
        C (b * c ^ 4 + c * b ^ 4) a +
        C (c * a ^ 4 + a * c ^ 4) b = 0) :
    Nat.card (pairingSpan C) ≤ 4 :=
  card_pairingSpan_le_four card_actual C hC hJ

end Kourovka2135.SuzukiEightPairingBound
