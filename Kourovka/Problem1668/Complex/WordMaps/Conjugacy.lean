import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped MatrixGroups
open Matrix

namespace WordMaps

variable {K : Type*} [Field K]

/-- The companion matrix of `X² - t X + 1`, as an element of `SL₂`. -/
def sl2Companion (t : K) : SL(2, K) :=
  ⟨!![0, -1; 1, t], by simp⟩

/-- A nonscalar matrix of size two has a cyclic vector.  The two columns of `P`
are that vector and its image. -/
theorem sl2_cyclic_basis (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ P : Matrix (Fin 2) (Fin 2) K, P.det ≠ 0 ∧
      (A : Matrix (Fin 2) (Fin 2) K) * P =
        P * (sl2Companion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K) := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.prop
    rw [Matrix.det_fin_two] at h
    exact h
  by_cases hc : A 1 0 = 0
  · by_cases hb : A 0 1 = 0
    · have had : A 0 0 ≠ A 1 1 := by
        intro had
        apply hA
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
      simp only [hb, hc, mul_zero, sub_zero] at hdet
      refine ⟨!![1, A 0 0; 1, A 1 1], ?_, ?_⟩
      · simpa using sub_ne_zero.mpr had.symm
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2Companion, Matrix.mul_apply, Matrix.trace_fin_two, hb, hc] <;>
          linear_combination -hdet
    · refine ⟨!![0, A 0 1; 1, A 1 1], by simpa using hb, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2Companion, Matrix.mul_apply, Matrix.trace_fin_two] <;> ring_nf
      all_goals linear_combination -hdet
  · refine ⟨!![1, A 0 0; 0, A 1 0], by simpa using hc, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Companion, Matrix.mul_apply, Matrix.trace_fin_two] <;> ring_nf
    all_goals linear_combination -hdet

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- A scalar rescaling makes a nonsingular two-dimensional change of basis special linear. -/
theorem sl2_companion_isConj (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2))) :
    IsConj A (sl2Companion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K))) := by
  obtain ⟨P, hP, hAP⟩ := sl2_cyclic_basis A hA
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq P.det⁻¹ (by decide : 0 < 2)
  have hQ : (r • P).det = 1 := by
    simpa [Matrix.det_smul, hr] using inv_mul_cancel₀ hP
  let Q : SL(2, K) := ⟨r • P, hQ⟩
  have hAQ : A * Q = Q * sl2Companion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) K) * (r • P) =
      (r • P) * (sl2Companion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K)
    simp only [Matrix.mul_smul, Matrix.smul_mul, hAP]
  apply isConj_iff.mpr
  refine ⟨Q⁻¹, ?_⟩
  simpa only [inv_inv, mul_assoc, inv_mul_cancel_left] using congrArg (Q⁻¹ * ·) hAQ

/-- Trace determines every nonscalar `SL₂` conjugacy class over an algebraically closed field. -/
theorem sl2_isConj_of_trace_eq (A B : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)))
    (hB : (B : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)))
    (htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) K)) : IsConj A B := by
  exact (sl2_companion_isConj A hA).trans (htr ▸ sl2_companion_isConj B hB).symm

end AlgebraicallyClosed

/-- A scalar element of `SL₂` is `1` or `-1`, as detected by its trace. -/
theorem sl2_nonscalar_of_trace_ne (A : SL(2, K))
    (hplus : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) ≠ 2)
    (hminus : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) ≠ -2) :
    (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  have hsq : a ^ 2 = 1 := by
    have h := A.prop
    rw [← ha] at h
    simpa [Matrix.det_fin_two, pow_two] using h
  rcases sq_eq_one_iff.mp hsq with ha1 | ha1
  · apply hplus
    simp [← ha, ha1]
  · apply hminus
    simp [← ha, ha1]

/-- The standard diagonal torus of `SL₂`. -/
def sl2Diagonal : Kˣ →* SL(2, K) where
  toFun a := ⟨!![a.val, 0; 0, a⁻¹.val], by simp⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change (!![(a * b).val, 0; 0, (a * b)⁻¹.val] : Matrix (Fin 2) (Fin 2) K) =
      !![a.val, 0; 0, a⁻¹.val] * !![b.val, 0; 0, b⁻¹.val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, mul_comm]

/-- The upper unipotent one-parameter subgroup. -/
def sl2Upper (s : K) : SL(2, K) := ⟨!![1, s; 0, 1], by simp⟩

theorem sl2Upper_add (s t : K) : sl2Upper (s + t) = sl2Upper s * sl2Upper t := by
  apply Subtype.ext
  change !![1, s + t; 0, 1] = (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, add_comm]

@[simp] theorem sl2Upper_zero : sl2Upper (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

theorem sl2Upper_pow (s : K) (n : ℕ) : sl2Upper s ^ n = sl2Upper ((n : K) * s) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, Nat.cast_add, add_mul, sl2Upper_add]

/-- The quotient map used throughout the projective conjugacy arguments. -/
def sl2Project : SL(2, K) →* PSL(2, K) := QuotientGroup.mk' _

theorem sl2Project_surjective : Function.Surjective (sl2Project (K := K)) :=
  Quotient.mk_surjective

@[simp] theorem sl2Project_neg (A : SL(2, K)) : sl2Project (-A) = sl2Project A := by
  have hneg : sl2Project (-1 : SL(2, K)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.mem_center_iff.mpr
    intro B
    simp
  rw [← neg_one_mul, map_mul, hneg, one_mul]

/-- Scalar determinant-one matrices in dimension two are precisely the two signs of identity. -/
theorem sl2_scalar_iff (A : SL(2, K)) :
    (A : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2)) ↔
      A = 1 ∨ A = -1 := by
  constructor
  · rintro ⟨a, ha⟩
    have hsq : a ^ 2 = 1 := by
      have h := A.prop
      rw [← ha] at h
      simpa [Matrix.det_fin_two, pow_two] using h
    rcases sq_eq_one_iff.mp hsq with h | h
    · left
      apply Subtype.ext
      simp [← ha, h]
    · right
      apply Subtype.ext
      rw [← ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h]
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · refine ⟨-1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp

/-- The matrix scalar predicate agrees with membership in the group center. -/
theorem sl2_mem_center_iff_scalar (A : SL(2, K)) :
    A ∈ Subgroup.center SL(2, K) ↔
      (A : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2)) := by
  rw [SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    have h := A.prop
    rw [← ha] at h
    simpa [Matrix.det_fin_two, pow_two] using h

theorem sl2Project_eq_one_iff (A : SL(2, K)) :
    sl2Project A = 1 ↔ A = 1 ∨ A = -1 := by
  rw [show sl2Project A = (A : PSL(2, K)) from rfl, QuotientGroup.eq_one_iff,
    sl2_mem_center_iff_scalar, sl2_scalar_iff]

/-- At a fixed trace, excluding its only possible scalar value excludes all scalars. -/
theorem sl2_nonscalar_of_trace_scalar_ne [CharZero K] (A : SL(2, K)) (ε : K)
    (htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = ε * 2)
    (hne : (A : Matrix (Fin 2) (Fin 2) K) ≠ Matrix.scalar (Fin 2) ε) :
    (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  have haε : a = ε := by
    have ht : a * 2 = ε * 2 := by simpa [← ha, Matrix.trace_fin_two, mul_two, two_mul] using htr
    exact mul_right_cancel₀ (by norm_num : (2 : K) ≠ 0) ht
  exact hne (ha.symm.trans (congrArg (Matrix.scalar (Fin 2)) haε))

theorem sl2_nonscalar_neg (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2))) :
    ((-A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [sl2_scalar_iff] at hA ⊢
  simpa only [neg_eq_iff_eq_neg, neg_neg] using hA ∘ Or.symm

theorem sl2Upper_nonscalar {s : K} (hs : s ≠ 0) :
    (sl2Upper s : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) ha
  exact hs (by simpa [sl2Upper] using h.symm)

section AlgebraicallyClosed

variable [IsAlgClosed K]

/-- Diagonal matrices provide every trace over an algebraically closed field. -/
theorem sl2_exists_diagonal_trace (t : K) :
    ∃ a : Kˣ, Matrix.trace (sl2Diagonal a : Matrix (Fin 2) (Fin 2) K) = t := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 : Polynomial K) (by
      intro hc
      have h : (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 : Polynomial K).coeff 2 = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (by rw [hc]; norm_num)
      simp [Polynomial.coeff_one] at h)
  have heq : a ^ 2 - t * a + 1 = 0 := by simpa using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at heq
  refine ⟨Units.mk0 a ha0, ?_⟩
  rw [Matrix.trace_fin_two]
  change a + a⁻¹ = t
  field_simp
  linear_combination heq

/-- Nonzero powers are surjective on the diagonal torus. -/
theorem sl2Diagonal_exists_pow (a : Kˣ) {n : ℕ} (hn : n ≠ 0) :
    ∃ B : SL(2, K), B ^ n = sl2Diagonal a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a.val (Nat.pos_of_ne_zero hn)
  have hb0 : b ≠ 0 := by
    intro h
    simp [h, hn] at hb
    exact a.ne_zero hb.symm
  refine ⟨sl2Diagonal (Units.mk0 b hb0), ?_⟩
  rw [← map_pow]
  congr 1
  apply Units.ext
  simpa using hb

end AlgebraicallyClosed

private theorem exists_pow_of_isConj {G : Type*} [Group G] {a b : G} {n : ℕ}
    (hab : IsConj a b) (hb : ∃ y, y ^ n = b) : ∃ x, x ^ n = a := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab.symm
  obtain ⟨y, hy⟩ := hb
  exact ⟨c * y * c⁻¹, by rw [conj_pow, hy, hc]⟩

section PowerSurjectivity

variable [IsAlgClosed K] [CharZero K]

private theorem psl2_exists_pow_of_trace_two (A : SL(2, K))
    (hA : (A : Matrix (Fin 2) (Fin 2) K) ∉ Set.range (Matrix.scalar (Fin 2)))
    (htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = 2)
    {n : ℕ} (hn : n ≠ 0) : ∃ x : PSL(2, K), x ^ n = sl2Project A := by
  have hc : IsConj A (sl2Upper 1) := sl2_isConj_of_trace_eq A (sl2Upper 1) hA
    (sl2Upper_nonscalar one_ne_zero) (by rw [htr]; norm_num [sl2Upper, Matrix.trace_fin_two])
  apply exists_pow_of_isConj ((sl2Project (K := K)).map_isConj hc)
  refine ⟨sl2Project (sl2Upper ((n : K)⁻¹)), ?_⟩
  rw [← map_pow, sl2Upper_pow, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)]

/-- Every positive integral power map on `PSL₂` is surjective in characteristic zero. -/
theorem psl2_pow_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun x : PSL(2, K) => x ^ n) := by
  intro g
  obtain ⟨A, rfl⟩ := sl2Project_surjective g
  by_cases hA : (A : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2))
  · rcases (sl2_scalar_iff A).mp hA with rfl | rfl <;> exact ⟨1, by simp⟩
  · by_cases ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = 2
    · exact psl2_exists_pow_of_trace_two A hA ht hn
    · by_cases htm : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = -2
      · simpa using psl2_exists_pow_of_trace_two (-A) (sl2_nonscalar_neg A hA)
          (by simp [htm]) hn
      · obtain ⟨a, ha⟩ := sl2_exists_diagonal_trace (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K))
        have haN := sl2_nonscalar_of_trace_ne (sl2Diagonal a) (ha ▸ ht) (ha ▸ htm)
        have hc := sl2_isConj_of_trace_eq A (sl2Diagonal a) hA haN ha.symm
        apply exists_pow_of_isConj ((sl2Project (K := K)).map_isConj hc)
        obtain ⟨B, hB⟩ := sl2Diagonal_exists_pow a hn
        exact ⟨sl2Project B, by rw [← map_pow, hB]⟩

/-- Every nonzero integral power map on `PSL₂` is surjective in characteristic zero. -/
theorem psl2_zpow_surjective {m : ℤ} (hm : m ≠ 0) :
    Function.Surjective (fun x : PSL(2, K) => x ^ m) := by
  intro g
  cases m with
  | ofNat n =>
      have hn : n ≠ 0 := by intro hn; apply hm; simp [hn]
      simpa using psl2_pow_surjective (K := K) hn g
  | negSucc n =>
      obtain ⟨x, hx⟩ := psl2_pow_surjective (K := K) (Nat.succ_ne_zero n) g⁻¹
      exact ⟨x, by simp [zpow_negSucc, hx]⟩

end PowerSurjectivity

end WordMaps
