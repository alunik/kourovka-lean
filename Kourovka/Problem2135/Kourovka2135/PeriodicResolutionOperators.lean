import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-! The A-linear operators of a tensor-periodic resolution. A positive
exponent is lowered once and its coefficient is multiplied by the relevant
square-zero algebra generator. No exponent multiplicity is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PeriodicResolution
open Finset
open scoped CharTwo
variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [CommRing A]

abbrev Space (ι : Type*) (A : Type*) [Zero A] := (ι →₀ ℕ) →₀ A

def lower (x : ι → A) (i : ι) : Module.End A (Space ι A) :=
  Finsupp.linearCombination A fun a =>
    if a i = 0 then 0 else Finsupp.single (a - Finsupp.single i 1) (x i)

omit [DecidableEq ι] in
@[simp] theorem lower_single (x : ι → A) (i : ι) (a : ι →₀ ℕ) (c : A) :
    lower x i (Finsupp.single a c) =
      if a i = 0 then 0 else Finsupp.single (a - Finsupp.single i 1) (c * x i) := by
  by_cases hi : a i = 0 <;>
    simp [lower, hi, Finsupp.smul_single, smul_eq_mul]

omit [DecidableEq ι] in
theorem lower_mul_self (x : ι → A) (i : ι) (hx : x i * x i = 0) :
    lower x i * lower x i = 0 := by
  apply Finsupp.lhom_ext
  intro a c
  by_cases hi : a i = 0
  · simp [Module.End.mul_apply, hi]
  · simp only [Module.End.mul_apply, lower_single, hi, ↓reduceIte]
    split_ifs <;> simp [mul_assoc, hx]

theorem lower_commute (x : ι → A) (i j : ι) : Commute (lower x i) (lower x j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  change lower x i * lower x j = lower x j * lower x i
  apply Finsupp.lhom_ext
  intro a c
  by_cases hi : a i = 0 <;> by_cases hj : a j = 0
  all_goals simp [Module.End.mul_apply, hi, hj, Finsupp.tsub_apply,
    hij, Ne.symm hij, mul_left_comm, mul_comm]
  congr 1
  ext z
  simp [Finsupp.tsub_apply, Nat.sub_sub, add_comm]

def differential (x : ι → A) (S : Finset ι) : Module.End A (Space ι A) :=
  ∑ i ∈ S, lower x i

theorem lower_commute_differential (x : ι → A) (S : Finset ι) (i : ι) :
    Commute (lower x i) (differential x S) := by
  exact Commute.sum_right S (lower x) (lower x i) (fun j _ => lower_commute x i j)

theorem differential_square_zero [CharP A 2]
    (x : ι → A) (S : Finset ι) (hx : ∀ i ∈ S, x i * x i = 0) :
    differential x S * differential x S = 0 := by
  induction S using Finset.induction_on with
  | empty => simp [differential]
  | @insert i S hi ih =>
    have hxi := hx i (Finset.mem_insert_self i S)
    have hxS : ∀ j ∈ S, x j * x j = 0 := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hcomm := lower_commute_differential x S i
    have hd : differential x (insert i S) = lower x i + differential x S := by
      simp [differential, hi]
    rw [hd, add_mul, mul_add, mul_add, lower_mul_self x i hxi, ih hxS]
    simp only [zero_add, add_zero]
    rw [hcomm.eq]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro a
    change ((differential x S * lower x i) v) a +
      ((differential x S * lower x i) v) a = (0 : A)
    exact CharTwo.add_self_eq_zero _

end Kourovka2135.PeriodicResolution
