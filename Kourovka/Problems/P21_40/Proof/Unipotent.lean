/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0; the full license text is included in
LICENSE in this directory. See THIRD_PARTY.md for pinned provenance.
Authors: The Tau Ceti contributors

The superdiagonal filtration proof below is adapted from
TauCetiProject/TauCeti at 355c248fa848acd70c2a4b412ca5f53d37b0402a,
TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/UpperUnitriangular/Nilpotent.lean.
The adaptation handles arbitrary upper-unitriangular subgroups directly.
-/
import Kourovka.Problems.P21_40.Statement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.Separable

namespace Kourovka.P21_40.Unipotent
open Matrix
open scoped commutatorElement

variable {R : Type*} [Ring R] {n : ℕ}
variable (S : Subgroup (Matrix.GeneralLinearGroup (Fin n) R))
variable (hS : ∀ g : S, ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R).IsUpperTriangular ∧
  ∀ i, ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1)

/-- A matrix vanishes strictly below its `r`-th superdiagonal. This private predicate is the
calculation behind `superdiagonalSubgroup`; the public membership theorem is its stable API. -/
private def VanishesBelow (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j.val < i.val + r → M i j = 0

private theorem VanishesBelow.zero (r : ℕ) :
    VanishesBelow (R := R) r (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j hij
  rfl

private theorem VanishesBelow.add {r : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow r N) :
    VanishesBelow r (M + N) := by
  intro i j hij
  simp [hM i j hij, hN i j hij]

private theorem VanishesBelow.neg {r : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) : VanishesBelow r (-M) := by
  intro i j hij
  simp [hM i j hij]

private theorem VanishesBelow.sub {r : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow r N) :
    VanishesBelow r (M - N) := by
  simpa only [sub_eq_add_neg] using hM.add hN.neg

private theorem VanishesBelow.mono {r s : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow s M) (hrs : r ≤ s) : VanishesBelow r M := by
  intro i j hij
  exact hM i j (by omega)

/-- Products add the number of forced zero superdiagonals. -/
private theorem VanishesBelow.mul {r s : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : VanishesBelow r M) (hN : VanishesBelow s N) :
    VanishesBelow (r + s) (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val < i.val + r
  · rw [hM i k hik, zero_mul]
  · rw [hN k j (by omega), mul_zero]

/-- Right multiplication by an upper-triangular matrix preserves the number of forced zero
superdiagonals. -/
private theorem VanishesBelow.mul_isUpperTriangular {r : ℕ}
    {M N : Matrix (Fin n) (Fin n) R} (hM : VanishesBelow r M)
    (hN : N.IsUpperTriangular) : VanishesBelow r (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val < i.val + r
  · rw [hM i k hik, zero_mul]
  · have hjk : j < k := by omega
    rw [hN hjk, mul_zero]

include hS

private theorem upperTriangular (g : S) :
    ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R).IsUpperTriangular :=
  (hS g).1

private theorem diagonal_one (g : S) (i : Fin n) :
    ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1 :=
  (hS g).2 i

private theorem sub_one_vanishesBelow_one
    (g : S) :
    VanishesBelow 1
      (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) := by
  intro i j hij
  by_cases hji : j < i
  · simp [Matrix.sub_apply, upperTriangular S hS g hji, ne_of_gt hji]
  · have hji' : j = i := by
      apply Fin.ext
      omega
    subst j
    simp [Matrix.sub_apply, diagonal_one S hS]

private theorem sub_one_isUpperTriangular
    (g : S) :
    Matrix.IsUpperTriangular
      (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) :=
  (upperTriangular S hS g).sub Matrix.blockTriangular_one

/-- The subgroup `U^r` of upper-unitriangular matrices whose entries below the `r`-th
superdiagonal vanish. Thus `U^1 = U_n`, and `U^n = 1` for `n × n` matrices. -/
def superdiagonalSubgroup (r : ℕ) : Subgroup (S) where
  carrier := {g | VanishesBelow r
    (((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1)}
  one_mem' := by
    simpa using VanishesBelow.zero (R := R) (n := n) r
  mul_mem' := by
    intro g h hg hh
    let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    let H := ((h : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    have hprod : VanishesBelow r ((G - 1) * (H - 1)) :=
      hg.mul_isUpperTriangular (sub_one_isUpperTriangular S hS h)
    have hsum : VanishesBelow r ((G - 1) + (H - 1) + (G - 1) * (H - 1)) :=
      (hg.add hh).add hprod
    have heq : G * H - 1 = (G - 1) + (H - 1) + (G - 1) * (H - 1) := by
      noncomm_ring
    -- Reduce subgroup membership to the matrix filtration used to define it.
    change VanishesBelow r (G * H - 1)
    rw [heq]
    exact hsum
  inv_mem' := by
    intro g hg
    let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    let Ginv := (((g⁻¹ : S) :
      Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
    have hprod : VanishesBelow r ((G - 1) * Ginv) :=
      hg.mul_isUpperTriangular (upperTriangular S hS (g⁻¹))
    have heq : Ginv - 1 = -((G - 1) * Ginv) := by
      have hmul : G * Ginv = 1 := by
        -- The two matrices are the values of a unit and its inverse.
        change (g.1 : Matrix (Fin n) (Fin n) R) *
          (g.1⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) = 1
        exact Units.mul_inv g.1
      calc
        Ginv - 1 = -(1 - Ginv) := by abel
        _ = -(G * Ginv - 1 * Ginv) := by rw [hmul, one_mul]
        _ = -((G - 1) * Ginv) := by rw [sub_mul]
    -- Reduce subgroup membership to the matrix filtration used to define it.
    change VanishesBelow r (Ginv - 1)
    rw [heq]
    exact hprod.neg

/-- Membership in `U^r` means that the matrix differs from the identity only on the `r`-th and
higher superdiagonals. -/
@[simp]
theorem mem_superdiagonalSubgroup_iff (r : ℕ)
    (g : S) :
    g ∈ superdiagonalSubgroup S hS r ↔
      ∀ i j, j.val < i.val + r →
        ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
          (1 : Matrix (Fin n) (Fin n) R) i j := by
  constructor
  · intro hg i j hij
    have h := hg i j hij
    simpa only [Matrix.sub_apply, sub_eq_zero] using h
  · intro hg i j hij
    simpa only [Matrix.sub_apply, sub_eq_zero] using hg i j hij

/-- The superdiagonal filtration is decreasing: requiring more initial superdiagonals to vanish
gives a smaller subgroup. -/
theorem superdiagonalSubgroup_antitone :
    Antitone (superdiagonalSubgroup S hS) := by
  intro r s hrs g hg
  exact hg.mono hrs

/-- The first superdiagonal subgroup is the whole upper-unitriangular group. -/
@[simp]
theorem superdiagonalSubgroup_one :
    superdiagonalSubgroup S hS 1 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  exact sub_one_vanishesBelow_one S hS g

/-- Once the filtration index reaches the matrix size, the superdiagonal subgroup is trivial. -/
theorem superdiagonalSubgroup_eq_bot_of_le {r : ℕ} (hnr : n ≤ r) :
    superdiagonalSubgroup S hS r = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (mem_superdiagonalSubgroup_iff S hS r g).mp hg i j (by omega)

/-- Commutators add filtration degrees: `[U^r, U^s] ≤ U^(r+s)`. -/
theorem commutator_superdiagonalSubgroup_le (r s : ℕ) :
    ⁅superdiagonalSubgroup S hS r,
        superdiagonalSubgroup S hS s⁆ ≤
      superdiagonalSubgroup S hS (r + s) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  let G := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let H := ((h : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  have hGH : VanishesBelow (r + s) ((G - 1) * (H - 1)) := hg.mul hh
  have hHG : VanishesBelow (r + s) ((H - 1) * (G - 1)) := by
    simpa only [Nat.add_comm] using hh.mul hg
  have hdiff : VanishesBelow (r + s) (G * H - H * G) := by
    have heq : G * H - H * G = (G - 1) * (H - 1) - (H - 1) * (G - 1) := by
      noncomm_ring
    exact heq.symm ▸ hGH.sub hHG
  let Ginv := (((g⁻¹ : S) :
    Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let Hinv := (((h⁻¹ : S) :
    Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let K := (((h * g)⁻¹ : S) :
    Matrix.GeneralLinearGroup (Fin n) R)
  have hright : VanishesBelow (r + s) ((G * H - H * G) * (K : Matrix (Fin n) (Fin n) R)) :=
    hdiff.mul_isUpperTriangular (upperTriangular S hS ((h * g)⁻¹))
  have heq :
      (((⁅g, h⁆ : S) :
          Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
        (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R) := by
    have hmul : H * G * (K : Matrix (Fin n) (Fin n) R) = 1 := by
      -- The product and `K` are the values of a unit and its inverse.
      change ((h * g).1 : Matrix (Fin n) (Fin n) R) *
        ((h * g).1⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) = 1
      exact Units.mul_inv (h * g).1
    have hK :
        Ginv * Hinv = (K : Matrix (Fin n) (Fin n) R) := by
      simp [Ginv, Hinv, K]
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Units.val_mul]
    -- The group wrappers have reduced; name their four underlying matrices explicitly.
    change G * H * Ginv * Hinv - 1 = (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R)
    rw [mul_assoc (G * H), hK]
    calc
      G * H * (K : Matrix (Fin n) (Fin n) R) - 1 =
          G * H * (K : Matrix (Fin n) (Fin n) R) -
            H * G * (K : Matrix (Fin n) (Fin n) R) := by rw [hmul]
      _ = (G * H - H * G) * (K : Matrix (Fin n) (Fin n) R) := by rw [sub_mul]
  -- Reduce subgroup membership to the matrix filtration used to define it.
  change VanishesBelow (r + s)
    (((((⁅g, h⁆ : S) :
      Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)) - 1)
  exact heq.symm ▸ hright

private theorem lowerCentralSeries_le_superdiagonalSubgroup (r : ℕ) :
    (⊤ : Subgroup (S)).lowerCentralSeries r ≤
      superdiagonalSubgroup S hS (r + 1) := by
  induction r with
  | zero =>
      simpa only [Subgroup.lowerCentralSeries_zero, zero_add, superdiagonalSubgroup_one S hS] using
        (le_refl (⊤ : Subgroup (S)))
  | succ r ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      refine (Subgroup.commutator_mono ih le_top).trans ?_
      simpa only [superdiagonalSubgroup_one S hS, Nat.succ_eq_add_one, add_assoc] using
        commutator_superdiagonalSubgroup_le S hS (r + 1) 1


/-- Upper-unitriangular subgroups have nilpotency class at most `n - 1`. -/
theorem lowerCentralSeries_pred_eq_bot :
    (⊤ : Subgroup S).lowerCentralSeries (n - 1) = ⊥ := by
  apply le_antisymm _ bot_le
  refine (lowerCentralSeries_le_superdiagonalSubgroup S hS (n - 1)).trans ?_
  rw [superdiagonalSubgroup_eq_bot_of_le S hS (by omega : n ≤ n - 1 + 1)]

theorem isNilpotent : Group.IsNilpotent S := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  exact ⟨n - 1, lowerCentralSeries_pred_eq_bot S hS⟩

theorem nilpotencyClass_le : Group.nilpotencyClass S ≤ n - 1 := by
  let := isNilpotent S hS
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (lowerCentralSeries_pred_eq_bot S hS)


/-- Each element of an upper-unitriangular subgroup differs from one by a nilpotent matrix. -/
theorem isNilpotent_sub_one (g : S) :
    _root_.IsNilpotent (((g : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) - 1) := by
  let N := ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1
  have hN : VanishesBelow 1 N := sub_one_vanishesBelow_one S hS g
  have hp : ∀ k : ℕ, VanishesBelow k (N ^ k) := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have hji : j < i := by omega
      simp [pow_zero, ne_of_gt hji]
    | succ k ih =>
      simpa only [pow_succ] using ih.mul hN
  refine ⟨n, ?_⟩
  ext i j
  exact hp n i j (by omega)

end Kourovka.P21_40.Unipotent

namespace Kourovka.P21_40

/-- A unipotent rational matrix of finite multiplicative order is the identity. -/
theorem matrix_eq_one_of_isNilpotent_sub_one_of_pow_eq_one
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℚ) (hn : IsNilpotent (A - 1))
    {k : ℕ} (hk : k ≠ 0) (hp : A ^ k = 1) : A = 1 := by
  let e := Matrix.toLinAlgEquiv' (R := ℚ) (n := m)
  let f : Module.End ℚ (m → ℚ) := e A
  have hf : f ^ k = 1 := by
    dsimp [f]
    rw [← map_pow, hp, map_one]
  have hs : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      ((Polynomial.separable_X_pow_sub_C (1 : ℚ) (Nat.cast_ne_zero.mpr hk) one_ne_zero).squarefree)
    simpa using sub_eq_zero.mpr hf
  have hn' : IsNilpotent (f - 1) := by
    simpa [f, map_sub, map_one] using hn.map e.toMonoidWithZeroHom
  have hs' : (f - 1).IsSemisimple := by
    exact Module.End.IsSemisimple.sub_of_commute (Commute.one_right f) hs
      Module.End.isSemisimple_id
  apply e.injective
  rw [map_one]
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn' hs')

/-- A subgroup of rational matrices all of whose elements are unipotent is torsion-free. -/
theorem eq_one_of_isOfFinOrder_of_unipotent
    {n : ℕ} (S : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (hS : ∀ g : S, IsNilpotent (((g : Matrix.GeneralLinearGroup (Fin n) ℚ) :
      Matrix (Fin n) (Fin n) ℚ) - 1))
    (g : S) (hg : IsOfFinOrder g) : g = 1 := by
  obtain ⟨k, hk, hp⟩ := hg.exists_pow_eq_one
  apply Subtype.ext
  apply Units.ext
  apply matrix_eq_one_of_isNilpotent_sub_one_of_pow_eq_one _ (hS g) hk.ne'
  exact congrArg (fun x : S => ((x : Matrix.GeneralLinearGroup (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ)) hp

end Kourovka.P21_40
