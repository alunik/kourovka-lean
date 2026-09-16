import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.CompactCoreGerms
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Endpoint characters of a concrete Thompson group

The group `F` is the rational dyadic piecewise-linear interval group supplied
by the imported Thompson development. Its endpoint exponents are obtained
from proved affine germ formulas, and their group laws follow from composition.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- Thompson's group in its rational dyadic PL interval model. -/
abbrev F : Type := ↥(compactF 0 1)

/-- The right-hand germ at zero has slope `2^n`. -/
def HasLeftExponent (g : F) (n : ℤ) : Prop :=
  ∃ ε : ℚ, 0 < ε ∧ ∀ t : ℚ, 0 ≤ t → t ≤ ε →
    g.1 t = (2 : ℚ) ^ n * t

/-- The left-hand germ at one has slope `2^n`. -/
def HasRightExponent (g : F) (n : ℤ) : Prop :=
  ∃ ε : ℚ, 0 < ε ∧ ∀ t : ℚ, 1 - ε ≤ t → t ≤ 1 →
    g.1 t = 1 + (2 : ℚ) ^ n * (t - 1)

theorem exists_leftExponent (g : F) : ∃ n : ℤ, HasLeftExponent g n := by
  obtain ⟨ε, hε, n, hn⟩ := compactF_germ_zero g.property
  exact ⟨n, ε, hε, by simpa using hn⟩

theorem exists_rightExponent (g : F) : ∃ n : ℤ, HasRightExponent g n := by
  obtain ⟨ε, hε, n, hn⟩ := compactF_germ_one g.property
  exact ⟨n, ε, hε, by simpa using hn⟩

theorem HasLeftExponent.unique {g : F} {n k : ℤ}
    (hn : HasLeftExponent g n) (hk : HasLeftExponent g k) : n = k := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨η, hη, hk⟩ := hk
  let t : ℚ := min ε η / 2
  have ht : 0 < t := div_pos (lt_min hε hη) (by norm_num)
  have htε : t ≤ ε := by
    dsimp [t]
    linarith [min_le_left ε η, lt_min hε hη]
  have htη : t ≤ η := by
    dsimp [t]
    linarith [min_le_right ε η, lt_min hε hη]
  apply zpow_right_injective₀ (show (0 : ℚ) < 2 by norm_num)
    (show (2 : ℚ) ≠ 1 by norm_num)
  exact mul_right_cancel₀ ht.ne' ((hn t ht.le htε).symm.trans (hk t ht.le htη))

theorem HasRightExponent.unique {g : F} {n k : ℤ}
    (hn : HasRightExponent g n) (hk : HasRightExponent g k) : n = k := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨η, hη, hk⟩ := hk
  let t : ℚ := 1 - min ε η / 2
  have ht : t < 1 := by
    dsimp [t]
    linarith [lt_min hε hη]
  have htε : 1 - ε ≤ t := by
    dsimp [t]
    linarith [min_le_left ε η, lt_min hε hη]
  have htη : 1 - η ≤ t := by
    dsimp [t]
    linarith [min_le_right ε η, lt_min hε hη]
  apply zpow_right_injective₀ (show (0 : ℚ) < 2 by norm_num)
    (show (2 : ℚ) ≠ 1 by norm_num)
  apply mul_right_cancel₀ (show t - 1 ≠ 0 by linarith)
  linarith [hn t htε ht.le, hk t htη ht.le]

theorem HasLeftExponent.mul {g h : F} {n k : ℤ}
    (hg : HasLeftExponent g n) (hh : HasLeftExponent h k) :
    HasLeftExponent (g * h) (n + k) := by
  obtain ⟨ε, hε, hg⟩ := hg
  obtain ⟨η, hη, hh⟩ := hh
  have hp : (0 : ℚ) < 2 ^ k := zpow_pos (by norm_num) k
  refine ⟨min η (ε / 2 ^ k), lt_min hη (div_pos hε hp), fun t ht0 ht => ?_⟩
  have htη : t ≤ η := ht.trans (min_le_left _ _)
  have htε : (2 : ℚ) ^ k * t ≤ ε := by
    have h := (le_div_iff₀ hp).mp (ht.trans (min_le_right _ _))
    nlinarith
  change g.1 (h.1 t) = _
  rw [hh t ht0 htη, hg _ (mul_nonneg hp.le ht0) htε,
    zpow_add₀ (show (2 : ℚ) ≠ 0 by norm_num)]
  ring

theorem HasRightExponent.mul {g h : F} {n k : ℤ}
    (hg : HasRightExponent g n) (hh : HasRightExponent h k) :
    HasRightExponent (g * h) (n + k) := by
  obtain ⟨ε, hε, hg⟩ := hg
  obtain ⟨η, hη, hh⟩ := hh
  have hp : (0 : ℚ) < 2 ^ k := zpow_pos (by norm_num) k
  refine ⟨min η (ε / 2 ^ k), lt_min hη (div_pos hε hp), fun t ht ht1 => ?_⟩
  have htη : 1 - η ≤ t := by linarith [min_le_left η (ε / 2 ^ k)]
  have htε : (2 : ℚ) ^ k * (1 - t) ≤ ε := by
    have h : 1 - t ≤ ε / 2 ^ k := by linarith [min_le_right η (ε / 2 ^ k)]
    have h' := (le_div_iff₀ hp).mp h
    nlinarith
  have hlow : 1 - ε ≤ 1 + (2 : ℚ) ^ k * (t - 1) := by nlinarith
  have hhigh : 1 + (2 : ℚ) ^ k * (t - 1) ≤ 1 := by nlinarith
  change g.1 (h.1 t) = _
  rw [hh t htη ht1, hg _ hlow hhigh,
    zpow_add₀ (show (2 : ℚ) ≠ 0 by norm_num)]
  ring

theorem hasLeftExponent_one : HasLeftExponent 1 0 := by
  refine ⟨1, by norm_num, fun t _ _ => ?_⟩
  simp

theorem hasRightExponent_one : HasRightExponent 1 0 := by
  refine ⟨1, by norm_num, fun t _ _ => ?_⟩
  simp

/-- The unique integer exponent of the germ at zero. -/
noncomputable def leftExponent (g : F) : ℤ := (exists_leftExponent g).choose

/-- The unique integer exponent of the germ at one. -/
noncomputable def rightExponent (g : F) : ℤ := (exists_rightExponent g).choose

theorem leftExponent_spec (g : F) : HasLeftExponent g (leftExponent g) :=
  (exists_leftExponent g).choose_spec

theorem rightExponent_spec (g : F) : HasRightExponent g (rightExponent g) :=
  (exists_rightExponent g).choose_spec

theorem leftExponent_eq {g : F} {n : ℤ} (h : HasLeftExponent g n) :
    leftExponent g = n := (leftExponent_spec g).unique h

theorem rightExponent_eq {g : F} {n : ℤ} (h : HasRightExponent g n) :
    rightExponent g = n := (rightExponent_spec g).unique h

@[simp] theorem leftExponent_one : leftExponent 1 = 0 := leftExponent_eq hasLeftExponent_one

@[simp] theorem rightExponent_one : rightExponent 1 = 0 := rightExponent_eq hasRightExponent_one

@[simp] theorem leftExponent_mul (g h : F) :
    leftExponent (g * h) = leftExponent g + leftExponent h :=
  leftExponent_eq ((leftExponent_spec g).mul (leftExponent_spec h))

@[simp] theorem rightExponent_mul (g h : F) :
    rightExponent (g * h) = rightExponent g + rightExponent h :=
  rightExponent_eq ((rightExponent_spec g).mul (rightExponent_spec h))

@[simp] theorem leftExponent_inv (g : F) : leftExponent g⁻¹ = -leftExponent g := by
  have h := leftExponent_mul g⁻¹ g
  rw [inv_mul_cancel, leftExponent_one] at h
  omega

@[simp] theorem rightExponent_inv (g : F) : rightExponent g⁻¹ = -rightExponent g := by
  have h := rightExponent_mul g⁻¹ g
  rw [inv_mul_cancel, rightExponent_one] at h
  omega

theorem HasLeftExponent.inv {g : F} {n : ℤ} (h : HasLeftExponent g n) :
    HasLeftExponent g⁻¹ (-n) := by
  simpa only [leftExponent_inv, leftExponent_eq h] using leftExponent_spec g⁻¹

theorem HasRightExponent.inv {g : F} {n : ℤ} (h : HasRightExponent g n) :
    HasRightExponent g⁻¹ (-n) := by
  simpa only [rightExponent_inv, rightExponent_eq h] using rightExponent_spec g⁻¹

/-- The two endpoint exponents as a group character. -/
noncomputable def endpointCharacter : F →* Multiplicative (ℤ × ℤ) where
  toFun g := Multiplicative.ofAdd (leftExponent g, rightExponent g)
  map_one' := by simp
  map_mul' g h := by
    simp only [leftExponent_mul, rightExponent_mul]
    rfl

@[simp] theorem endpointCharacter_apply (g : F) :
    endpointCharacter g = Multiplicative.ofAdd (leftExponent g, rightExponent g) := rfl

/-- The concrete subgroup whose two endpoint slopes agree. -/
def diagonalSubgroup : Subgroup F where
  carrier := {g | leftExponent g = rightExponent g}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change leftExponent g = rightExponent g at hg
    change leftExponent h = rightExponent h at hh
    change leftExponent (g * h) = rightExponent (g * h)
    simp only [leftExponent_mul, rightExponent_mul, hg, hh]
  inv_mem' := by
    intro g hg
    change leftExponent g = rightExponent g at hg
    change leftExponent g⁻¹ = rightExponent g⁻¹
    simp only [leftExponent_inv, rightExponent_inv, hg]

@[simp] theorem mem_diagonalSubgroup (g : F) :
    g ∈ diagonalSubgroup ↔ leftExponent g = rightExponent g := Iff.rfl

/-- Every element fixing neighborhoods of both endpoints has zero characters. -/
theorem endpointExponents_eq_zero_of_mem_compactCore {g : F}
    (hg : g.1 ∈ compactCore 0) : leftExponent g = 0 ∧ rightExponent g = 0 := by
  obtain ⟨_, ε, hε, hg0, hg1⟩ := hg
  constructor
  · apply leftExponent_eq
    exact ⟨ε, hε, fun t _ ht => by simpa using hg0 t ht⟩
  · apply rightExponent_eq
    exact ⟨ε, hε, fun t ht _ => by simpa using hg1 t ht⟩

theorem mem_diagonalSubgroup_of_mem_compactCore {g : F}
    (hg : g.1 ∈ compactCore 0) : g ∈ diagonalSubgroup := by
  obtain ⟨h0, h1⟩ := endpointExponents_eq_zero_of_mem_compactCore hg
  exact h0.trans h1.symm

/-- The endpoint characters vanish exactly on maps that are the identity
near both endpoints. This makes no assertion about the derived subgroup. -/
theorem mem_compactCore_iff_endpointExponents_eq_zero (g : F) :
    g.1 ∈ compactCore 0 ↔ leftExponent g = 0 ∧ rightExponent g = 0 := by
  refine ⟨endpointExponents_eq_zero_of_mem_compactCore, ?_⟩
  rintro ⟨hleft, hright⟩
  have hl := leftExponent_spec g
  have hr := rightExponent_spec g
  rw [hleft] at hl
  rw [hright] at hr
  obtain ⟨ε, hε, hl⟩ := hl
  obtain ⟨η, hη, hr⟩ := hr
  refine ⟨g.property, min ε η, lt_min hε hη, ?_, ?_⟩
  · intro t ht
    by_cases ht0 : t ≤ 0
    · exact compactF_fix_nonpos g.property ht0
    · simpa using hl t (lt_of_not_ge ht0).le (ht.trans (min_le_left _ _))
  · intro t ht
    by_cases ht1 : 1 ≤ t
    · exact compactF_fix_one g.property ht1
    · have hlow : 1 - η ≤ t := by linarith [min_le_right ε η]
      simpa using hr t hlow (lt_of_not_ge ht1).le

@[simp] theorem endpointCharacter_eq_one_iff (g : F) :
    endpointCharacter g = 1 ↔ leftExponent g = 0 ∧ rightExponent g = 0 := by
  change (leftExponent g, rightExponent g) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]

theorem mem_endpointCharacter_ker_iff (g : F) :
    g ∈ endpointCharacter.ker ↔ g.1 ∈ compactCore 0 := by
  change endpointCharacter g = 1 ↔ _
  rw [endpointCharacter_eq_one_iff, mem_compactCore_iff_endpointExponents_eq_zero]

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.endpointCharacter
#audit_axioms Kourovka.P21_38.mem_endpointCharacter_ker_iff
#audit_axioms Kourovka.P21_38.mem_diagonalSubgroup_of_mem_compactCore
