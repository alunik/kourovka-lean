import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Eigenvectors from a split annihilator over an embedded coefficient field.

Induction takes place over the original field before coefficients are mapped.
Consequently the resulting eigenvalue belongs to that field's image. No
finite-dimensionality, algebraic closure, or commutativity of the full
endomorphism ring is required.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.EmbeddedFieldEigenvector

open Polynomial
open scoped Polynomial

section General
variable {F : Type u} [Field F] {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (σ : F →+* k) (T : Module.End k V)

/-- If every embedded linear factor acts injectively, so does every nonzero
split polynomial evaluated after mapping its coefficients. -/
theorem injective_aeval_map_of_splits
    (hlinear : ∀ a : F, Function.Injective (T + algebraMap k (Module.End k V) (σ a)))
    (p : F[X]) (hp : p.Splits) (hp0 : p ≠ 0) :
    Function.Injective (Polynomial.aeval T (p.map σ)) := by
  classical
  revert hp0
  induction hp using Submonoid.closure_induction with
  | mem p hp =>
      intro hp0
      rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · have ha : a ≠ 0 := by intro h; apply hp0; simp [h]
        have hσa : σ a ≠ 0 := by
          intro h
          apply ha
          exact σ.injective (by simpa only [map_zero] using h)
        rw [Polynomial.map_C, Polynomial.aeval_C]
        intro x y hxy
        exact smul_right_injective V hσa hxy
      · simpa only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
          Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C] using hlinear a
  | one =>
      intro _
      rw [Polynomial.map_one, Polynomial.aeval_one]
      intro x y hxy
      exact hxy
  | mul p q _ _ ihp ihq =>
      intro hpq
      rw [Polynomial.map_mul, Polynomial.aeval_mul]
      intro x y hxy
      exact ihq (right_ne_zero_of_mul hpq) (ihp (left_ne_zero_of_mul hpq) hxy)

/-- A nonzero split annihilator gives an eigenvector with eigenvalue in the
embedded field, even on an infinite-dimensional vector space. -/
theorem exists_eigenvector_of_split_annihilator [Nontrivial V]
    (p : F[X]) (hp : p.Splits) (hp0 : p ≠ 0)
    (hann : Polynomial.aeval T (p.map σ) = 0) :
    ∃ a : F, ∃ v : V, v ≠ 0 ∧ T v = σ a • v := by
  classical
  have hnot : ¬ ∀ a : F,
      Function.Injective (T + algebraMap k (Module.End k V) (σ a)) := by
    intro hlinear
    have hi := injective_aeval_map_of_splits σ T hlinear p hp hp0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply hi
    rw [hann]
    rfl
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp ha
  refine ⟨-a, x - y, sub_ne_zero.mpr hne, ?_⟩
  have hz : (T + algebraMap k (Module.End k V) (σ a)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  change T (x - y) + σ a • (x - y) = 0 at hz
  rw [map_neg, neg_smul]
  exact eq_neg_of_add_eq_zero_left hz

end General

/-- The multiplicative finite-field annihilator splits, by removing X from
the known split additive finite-field polynomial. -/
theorem splits_X_pow_card_sub_one (F : Type u) [Field F] [Fintype F] :
    (X ^ (Fintype.card F - 1) - 1 : F[X]).Splits := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hs : (X ^ Fintype.card F - X : F[X]).Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F hq]
    simp
  have hfactor : X * (X ^ (Fintype.card F - 1) - 1 : F[X]) =
      X ^ Fintype.card F - X := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (Nat.le_of_lt hq)]
  apply Polynomial.Splits.of_X_mul
  rwa [hfactor]

/-- A finite-order operator whose order divides the multiplicative-field
order has an eigenvector with a nonzero eigenvalue in the embedded field. -/
theorem exists_unit_eigenvector_of_pow_card_sub_one
    {F : Type u} [Field F] [Fintype F] {k : Type v} [Field k]
    {V : Type w} [AddCommGroup V] [Module k V] [Nontrivial V]
    (σ : F →+* k) (T : Module.End k V) (hT : T ^ (Fintype.card F - 1) = 1) :
    ∃ a : Fˣ, ∃ v : V, v ≠ 0 ∧ T v = σ (a : F) • v := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hm : Fintype.card F - 1 ≠ 0 := (Nat.sub_pos_of_lt hq).ne'
  have hp0 : (X ^ (Fintype.card F - 1) - 1 : F[X]) ≠ 0 := by
    simpa only [Polynomial.C_1] using
      Polynomial.X_pow_sub_C_ne_zero (Nat.sub_pos_of_lt hq) (1 : F)
  have hann : Polynomial.aeval T
      ((X ^ (Fintype.card F - 1) - 1 : F[X]).map σ) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, map_sub, map_pow, Polynomial.aeval_X, map_one, hT, sub_self]
  obtain ⟨a, v, hv, he⟩ := exists_eigenvector_of_split_annihilator σ T _
    (splits_X_pow_card_sub_one F) hp0 hann
  have ha : a ≠ 0 := by
    intro ha
    have hve : T.HasEigenvector (σ a) v := ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
    have hpow := hve.pow_apply (Fintype.card F - 1)
    apply hv
    simpa only [ha, map_zero, zero_pow hm, zero_smul, hT, Module.End.one_apply] using hpow
  exact ⟨Units.mk0 a ha, v, hv, he⟩

end Kourovka2135.EmbeddedFieldEigenvector
