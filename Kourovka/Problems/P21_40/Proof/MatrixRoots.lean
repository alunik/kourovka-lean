import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Large prime roots in rational matrix groups

Powering by a sufficiently large prime is injective on the units of every
finite-dimensional rational algebra. In particular, it is injective on
`GL (Fin n) ℚ`, uniformly over all matrices of the given dimension.

The key observation is that a cyclotomic polynomial of degree larger than the
dimension of an algebra is coprime to the minimal polynomial of each element.
For a rational linear map, this implies that every vector fixed by its `p`-th
power is fixed by the map itself. Apply this to conjugation by a unit: an
element commuting with its `p`-th power already commutes with the unit.
Two equal `p`-th powers therefore have commuting roots, and their quotient is
trivial by the same cyclotomic argument.

This proof makes no semisimplicity or finite-generation assumption.
-/

open Polynomial

namespace Kourovka.P21_40

section Algebra

variable {R : Type*} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]

/-- A cyclotomic polynomial of sufficiently large prime index evaluates to an
element with a left inverse in a finite-dimensional rational algebra. -/
theorem exists_cyclotomic_left_inverse (a : R) {p : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ R < p - 1) :
    ∃ b : R, b * aeval a (cyclotomic p ℚ) = 1 := by
  have hcop : IsCoprime (cyclotomic p ℚ) (minpoly ℚ a) := by
    apply (cyclotomic.irreducible_rat hp.pos).coprime_iff_not_dvd.mpr
    intro hdiv
    have hdeg := natDegree_le_of_dvd hdiv (minpoly.ne_zero_of_finite ℚ a)
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at hdeg
    exact (not_le_of_gt hdim) (hdeg.trans (minpoly.natDegree_le a))
  obtain ⟨f, g, hfg⟩ := hcop
  refine ⟨aeval a f, ?_⟩
  simpa only [map_add, map_mul, minpoly.aeval, mul_zero, add_zero, map_one]
    using congrArg (aeval a) hfg

/-- A finite-dimensional rational algebra has no nontrivial elements of
sufficiently large prime order. -/
theorem eq_one_of_prime_pow_eq_one {a : R} {p : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ R < p - 1) (ha : a ^ p = 1) : a = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := exists_cyclotomic_left_inverse a hp hdim
  have hfac : aeval a (cyclotomic p ℚ) * (a - 1) = 0 := by
    have h := congrArg (aeval a) (cyclotomic_prime_mul_X_sub_one ℚ p)
    simpa only [map_mul, map_sub, map_one, map_pow, aeval_X, ha, sub_self] using h
  apply sub_eq_zero.mp
  calc
    a - 1 = (b * aeval a (cyclotomic p ℚ)) * (a - 1) := by rw [hb, one_mul]
    _ = 0 := by rw [mul_assoc, hfac, mul_zero]

end Algebra

/-- For a sufficiently large prime, taking a prime power of a rational linear
map does not introduce new fixed vectors. The dimension bound used here is
deliberately coarse, since only existence of such a prime is needed. -/
theorem fixed_of_prime_pow_fixed {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (T : Module.End ℚ V) {p : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ (Module.End ℚ V) < p - 1) {v : V}
    (hv : (T ^ p) v = v) : T v = v := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := exists_cyclotomic_left_inverse T hp hdim
  have hfac : aeval T (cyclotomic p ℚ) * (T - 1) = T ^ p - 1 := by
    simpa only [map_mul, map_sub, map_one, map_pow, aeval_X]
      using congrArg (aeval T) (cyclotomic_prime_mul_X_sub_one ℚ p)
  have hz : (aeval T (cyclotomic p ℚ)) ((T - 1) v) = 0 := by
    have h := congrArg (fun f : Module.End ℚ V => f v) hfac
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hv,
      sub_self] using h
  have hzv : (T - 1) v = 0 := by
    calc
      (T - 1) v = (b * aeval T (cyclotomic p ℚ)) ((T - 1) v) := by rw [hb]; rfl
      _ = b ((aeval T (cyclotomic p ℚ)) ((T - 1) v)) := rfl
      _ = 0 := by rw [hz, map_zero]
  exact sub_eq_zero.mp hzv

section Units

variable {R : Type*} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]

/-- Conjugation by a unit, viewed as a rational linear endomorphism. -/
def conjugationLinear (u : Rˣ) : Module.End ℚ R :=
  LinearMap.mulLeftRight ℚ ((u : R), (↑u⁻¹ : R))

omit [FiniteDimensional ℚ R] in
theorem conjugationLinear_pow_apply (u : Rˣ) (k : ℕ) (x : R) :
    (conjugationLinear u ^ k) x = (u : R) ^ k * x * (↑u⁻¹ : R) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change (u : R) * ((u : R) ^ k * x * (↑u⁻¹ : R) ^ k) * (↑u⁻¹ : R) = _
    calc
      _ = ((u : R) * (u : R) ^ k) * x * ((↑u⁻¹ : R) ^ k * (↑u⁻¹ : R)) := by
        simp only [mul_assoc]
      _ = _ := by rw [← pow_succ', ← pow_succ]

/-- Commuting with a sufficiently large prime power of a unit implies commuting
with the unit itself. -/
theorem commute_of_commute_prime_pow (u : Rˣ) (x : R) {p : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ (Module.End ℚ R) < p - 1)
    (hx : Commute ((u : R) ^ p) x) : Commute (u : R) x := by
  have hfix : (conjugationLinear u ^ p) x = x := by
    rw [conjugationLinear_pow_apply, hx.eq, mul_assoc]
    have hinv : (u : R) ^ p * (↑u⁻¹ : R) ^ p = 1 := by
      simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]
    rw [hinv, mul_one]
  have h := fixed_of_prime_pow_fixed (conjugationLinear u) hp hdim hfix
  change (u : R) * x * (↑u⁻¹ : R) = x at h
  have h' := congrArg (fun y : R => y * (u : R)) h
  exact show (u : R) * x = x * (u : R) from by simpa only [mul_assoc,
    Units.inv_mul, mul_one] using h'

/-- Large-prime powering is injective on the unit group of a finite-dimensional
rational algebra. -/
theorem units_pow_injective_of_prime {p : ℕ} (hp : p.Prime)
    (hdim : Module.finrank ℚ R < p - 1)
    (hdimEnd : Module.finrank ℚ (Module.End ℚ R) < p - 1) :
    Function.Injective (fun u : Rˣ => u ^ p) := by
  intro u v huv
  have hpow : (u : R) ^ p = (v : R) ^ p := by
    exact_mod_cast huv
  have hc : Commute (u : R) (v : R) :=
    commute_of_commute_prime_pow u (v : R) hp hdimEnd
      (hpow ▸ (Commute.refl (v : R)).pow_left p)
  have hz : ((u : R) * (↑v⁻¹ : R)) ^ p = 1 := by
    rw [hc.units_inv_right.mul_pow, hpow]
    simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]
  have heq := eq_one_of_prime_pow_eq_one hp hdim hz
  apply Units.ext
  have h' := congrArg (fun y : R => y * (v : R)) heq
  simpa only [mul_assoc, Units.inv_mul, mul_one, one_mul] using h'

/-- Every finite-dimensional rational algebra admits a prime for which powering
is injective on its entire unit group. -/
theorem exists_prime_units_pow_injective (R : Type*) [Ring R] [Algebra ℚ R]
    [FiniteDimensional ℚ R] :
    ∃ p : ℕ, p.Prime ∧ 2 ≤ p ∧ Function.Injective (fun u : Rˣ => u ^ p) := by
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes
    (Module.finrank ℚ R + Module.finrank ℚ (Module.End ℚ R) + 2)
  exact ⟨p, hp, hp.two_le, units_pow_injective_of_prime hp (by omega) (by omega)⟩

end Units

/-- A prime whose power map is injective on all invertible rational `n × n`
matrices. This also covers `n = 0`. -/
theorem exists_prime_pow_injective (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 2 ≤ p ∧
      Function.Injective (fun A : Matrix.GeneralLinearGroup (Fin n) ℚ => A ^ p) :=
  exists_prime_units_pow_injective (Matrix (Fin n) (Fin n) ℚ)

end Kourovka.P21_40
