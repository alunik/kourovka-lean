import Kourovka2135.BinaryQuadraticWalsh
import Kourovka2135.BinaryWalshParity

/-! Surjectivity of vector-valued binary quadratic maps with nondegenerate
scalar polar forms. The proof uses exact integer character sums and parity,
without a Pfaffian identity or a dimension bound. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open scoped BigOperators
open Classical
variable {V Z : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup Z] [Module (ZMod 2) Z]
variable [Fintype V] [Fintype Z] [Nontrivial V]

/-- The abstract Fourier criterion needs only the exact squares of all nontrivial sums. -/
theorem surjective_of_walsh_sq (Q : V → Z)
    (hsq : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 →
      walsh (fun x => ell (Q x)) ^ 2 = Fintype.card V) :
    Function.Surjective Q := by
  classical
  letI : Finite (Module.Dual (ZMod 2) Z) :=
    Finite.of_injective (fun ell : Module.Dual (ZMod 2) Z => (ell : Z → ZMod 2))
      DFunLike.coe_injective
  letI : Fintype (Module.Dual (ZMod 2) Z) := Fintype.ofFinite _
  rcases subsingleton_or_nontrivial Z with hZ | hZ
  · intro z
    exact ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨ell0, hell0⟩ := exists_ne (0 : Module.Dual (ZMod 2) Z)
    let a := walsh (fun x => ell0 (Q x))
    have ha_sq : a ^ 2 = (Fintype.card V : ℤ) := hsq ell0 hell0
    have ha : a ≠ 0 := by
      intro hz
      rw [hz, zero_pow (by decide)] at ha_sq
      exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) ha_sq.symm
    have ha_two : (a : ZMod 2) = 0 := by
      have hh := congrArg (fun n : ℤ => (n : ZMod 2)) ha_sq
      simp only [Int.cast_pow, Int.cast_natCast, card_cast_two_eq_zero] at hh
      exact eq_zero_of_pow_eq_zero hh
    intro t
    by_contra ht
    have hmiss : ∀ x, Q x ≠ t := by simpa only [not_exists] using ht
    let f : Module.Dual (ZMod 2) Z → ℤ :=
      fun ell => sign (ell t) * walsh (fun x => ell (Q x))
    have hf0 : f 0 = a ^ 2 := by
      simp only [f, LinearMap.zero_apply, sign_zero, walsh, Finset.sum_const,
        nsmul_eq_mul, mul_one, one_mul]
      exact ha_sq.symm
    have hfsq (ell : Module.Dual (ZMod 2) Z) (hell : ell ≠ 0) : f ell ^ 2 = a ^ 2 := by
      dsimp [f]
      rw [mul_pow, sign_sq, one_mul, hsq ell hell, ha_sq]
    apply square_root_sum_ne_zero f a ha ha_two card_cast_two_eq_zero hf0 hfsq
    exact missing_point_fourier Q t hmiss

/-- Every target is attained if every nonzero scalar polar form is nondegenerate. -/
theorem quadratic_surjective_of_nondegenerate_polar (Q : QuadraticMap (ZMod 2) V Z)
    (hnd : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 →
      ∀ h : V, (∀ x : V, ell (Q.polarBilin h x) = 0) → h = 0) :
    Function.Surjective Q := by
  apply surjective_of_walsh_sq
  intro ell hell
  let q : QuadraticForm (ZMod 2) V := ell.compQuadraticMap Q
  change walsh q ^ 2 = _
  apply walsh_sq_of_nondegenerate
  intro h hh
  apply hnd ell hell h
  intro x
  simpa only [q, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    LinearMap.compQuadraticMap_apply, map_sub] using hh x

end Kourovka2135.BinaryFourier
