import Kourovka2135.BinaryQuadraticWalsh

/-! A Fourier bound for binary quadratic maps. This is the numerical form
needed when restriction changes the radicals of the scalar polar forms. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open scoped BigOperators
open Classical

@[simp] theorem abs_sign (a : ZMod 2) : |sign a| = 1 := by
  unfold sign
  split_ifs <;> norm_num

variable {V Z : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup Z] [Module (ZMod 2) Z]
variable [Fintype V] [Fintype Z] [Fintype (Module.Dual (ZMod 2) Z)]

/-- Nontrivial Fourier coefficients bounded by |V|/|Z*| force every fiber to be nonempty. -/
theorem surjective_of_walsh_bound (Q : V → Z)
    (hb : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 →
      (Fintype.card (Module.Dual (ZMod 2) Z) : ℤ) * |walsh (fun x => ell (Q x))| ≤
        Fintype.card V) : Function.Surjective Q := by
  classical
  intro t
  by_contra ht
  have hmiss : ∀ x, Q x ≠ t := by simpa only [not_exists] using ht
  let f : Module.Dual (ZMod 2) Z → ℤ :=
    fun ell => sign (ell t) * walsh (fun x => ell (Q x))
  let E := Finset.univ.erase (0 : Module.Dual (ZMod 2) Z)
  let C : ℤ := Fintype.card (Module.Dual (ZMod 2) Z)
  let N : ℤ := Fintype.card V
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hf0 : f 0 = N := by simp [f, N, walsh]
  have hsum : ∑ ell, f ell = 0 := missing_point_fourier Q t hmiss
  have hE : ∑ ell ∈ E, f ell = -N := by
    have he := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ 0)
    rw [hsum, hf0] at he
    exact eq_neg_of_add_eq_zero_left he
  have habs (ell : Module.Dual (ZMod 2) Z) : |f ell| = |walsh (fun x => ell (Q x))| := by
    simp only [f, abs_mul, abs_sign, one_mul]
  have hineq : C * N ≤ (E.card : ℤ) * N := calc
    C * N = C * |∑ ell ∈ E, f ell| := by rw [hE, abs_neg, abs_of_pos hN]
    _ ≤ C * ∑ ell ∈ E, |f ell| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _ = ∑ ell ∈ E, C * |f ell| := Finset.mul_sum ..
    _ ≤ ∑ _ell ∈ E, N := Finset.sum_le_sum fun ell hell => by
      rw [habs]
      exact hb ell (Finset.mem_erase.mp hell).1
    _ = _ := by simp
  have hcount : (E.card : ℤ) + 1 = C := by
    dsimp [E, C]
    exact_mod_cast Finset.card_erase_add_one (s := Finset.univ) (Finset.mem_univ (0 : Module.Dual (ZMod 2) Z))
  nlinarith

/-- The square of a quadratic character sum is bounded by the size of its polar radical. -/
theorem walsh_sq_le_card_mul_radical (q : QuadraticForm (ZMod 2) V) :
    walsh q ^ 2 ≤ (Fintype.card V : ℤ) *
      ((Finset.univ.filter fun h : V => q.polarBilin h = 0).card : ℤ) := by
  classical
  rw [walsh_sq_sum_radical]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    (∑ h : V, if q.polarBilin h = 0 then sign (q h) else 0) ≤
        ∑ h : V, if q.polarBilin h = 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro h _
      split_ifs
      · exact (le_abs_self _).trans (le_of_eq (abs_sign _))
      · exact le_rfl
    _ = _ := by simp [← Finset.sum_filter]

/-- A cardinal version of the usual polar-rank criterion. -/
theorem quadratic_surjective_of_radical_card_bound (Q : QuadraticMap (ZMod 2) V Z)
    (hb : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 →
      Fintype.card (Module.Dual (ZMod 2) Z) ^ 2 *
        (Finset.univ.filter fun h : V => ∀ x : V, ell (Q.polarBilin h x) = 0).card ≤
          Fintype.card V) : Function.Surjective Q := by
  apply surjective_of_walsh_bound
  intro ell hell
  let q : QuadraticForm (ZMod 2) V := ell.compQuadraticMap Q
  let C : ℤ := Fintype.card (Module.Dual (ZMod 2) Z)
  let N : ℤ := Fintype.card V
  let R : ℤ := (Finset.univ.filter fun h : V => q.polarBilin h = 0).card
  have he (h : V) : q.polarBilin h = 0 ↔ ∀ x : V, ell (Q.polarBilin h x) = 0 := by
    rw [LinearMap.ext_iff]
    simp only [q, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.compQuadraticMap_apply, map_sub, LinearMap.zero_apply]
  have hR : C ^ 2 * R ≤ N := by
    dsimp [C, R, N]
    simp only [he]
    exact_mod_cast hb ell hell
  have hsq : walsh q ^ 2 ≤ N * R := walsh_sq_le_card_mul_radical q
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hs : (C * |walsh q|) ^ 2 ≤ N ^ 2 := calc
    (C * |walsh q|) ^ 2 = C ^ 2 * walsh q ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ C ^ 2 * (N * R) := mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
    _ = N * (C ^ 2 * R) := by ring
    _ ≤ N * N := mul_le_mul_of_nonneg_left hR hN
    _ = N ^ 2 := by ring
  change C * |walsh q| ≤ N
  nlinarith [mul_nonneg (show 0 ≤ C from Nat.cast_nonneg _) (abs_nonneg (walsh q))]

end Kourovka2135.BinaryFourier
