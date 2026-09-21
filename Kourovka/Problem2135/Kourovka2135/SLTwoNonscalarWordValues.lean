import Kourovka2135.SLTwoGeneralLinearConjugation
import Kourovka2135.DerivedCentralization

/-! Every nonscalar SL₂ matrix is a single value of every outer commutator
word, provided the field has a unit whose square is not one. A fixed diagonal
and an explicit one-parameter matrix give nonscalar commutators of every trace.
Actual GL₂ conjugation then reaches the prescribed nonscalar matrix. No Ore,
character, representation-classification, or word-width theorem is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SLTwoNonscalarWordValues

open scoped Matrix
open SLTwoGeneralLinearConjugation

variable {F : Type*} [Field F]

def Nonscalar (g : SLTwo.SL2 F) : Prop :=
  ¬ ∃ r : F, g.val = Matrix.scalar (Fin 2) r

/-- Its lower-left coefficient is always one. -/
def shear (t : F) : SLTwo.SL2 F :=
  ⟨!![1, t; 1, 1 + t], by simp [Matrix.det_fin_two_of]⟩

theorem shear_inv (t : F) :
    (shear t)⁻¹ = (⟨!![1 + t, -t; -1, 1], by
      simp [Matrix.det_fin_two_of]⟩ : SLTwo.SL2 F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [shear, Matrix.adjugate_fin_two]

theorem commutator_val (s : Fˣ) (t : F) :
    (paperCommutator (SLTwo.tor s) (shear t)).val =
      !![1 + t - (s : F)⁻¹ ^ 2 * t,
          t * (1 + t) * (1 - (s : F)⁻¹ ^ 2);
        1 - (s : F) ^ 2, 1 + t - (s : F) ^ 2 * t] := by
  unfold paperCommutator
  rw [SLTwo.tor_inv, shear_inv]
  change (SLTwo.tor s⁻¹).val * (!![1 + t, -t; -1, 1] : Matrix (Fin 2) (Fin 2) F) *
    (SLTwo.tor s).val * (shear t).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SLTwo.tor, shear, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The trace parameter is affine with nonzero slope when s²≠1. -/
theorem commutator_trace (s : Fˣ) (t : F) :
    (paperCommutator (SLTwo.tor s) (shear t)).val.trace =
      2 - ((s : F) - (s : F)⁻¹) ^ 2 * t := by
  rw [commutator_val, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

theorem unit_sub_inv_ne_zero (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1) :
    (s : F) - (s : F)⁻¹ ≠ 0 := by
  intro he
  have hh := congrArg (fun x : F => (s : F) * x) (sub_eq_zero.mp he)
  apply hs
  simpa only [← pow_two, mul_inv_cancel₀ s.ne_zero] using hh

theorem tor_nonscalar (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1) :
    Nonscalar (SLTwo.tor s) := by
  rintro ⟨r, hr⟩
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hr
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hr
  have he : (s : F) - (s : F)⁻¹ = 0 := by
    have h0' : (s : F) = r := by simpa [SLTwo.tor] using h0
    have h1' : (s : F)⁻¹ = r := by simpa [SLTwo.tor] using h1
    exact sub_eq_zero.mpr (h0'.trans h1'.symm)
  exact unit_sub_inv_ne_zero s hs he

theorem shear_nonscalar (t : F) : Nonscalar (shear t) := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr
  simp [shear] at h

theorem commutator_nonscalar (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1) (t : F) :
    Nonscalar (paperCommutator (SLTwo.tor s) (shear t)) := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr
  have hz : 1 - (s : F) ^ 2 = 0 := by simpa [commutator_val] using h
  exact hs (sub_eq_zero.mp hz).symm

/-- The construction is valid over any field with a suitable actual unit. -/
theorem nonscalar_mem_values_of_unit (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1)
    (w : OuterWord) (g : SLTwo.SL2 F) (hg : Nonscalar g) :
    g ∈ w.values (SLTwo.SL2 F) := by
  induction w generalizing g with
  | leaf => simp
  | bracket l r ihl ihr =>
      let t : F := (2 - g.val.trace) / ((s : F) - (s : F)⁻¹) ^ 2
      have hc : (paperCommutator (SLTwo.tor s) (shear t)).val.trace = g.val.trace := by
        rw [commutator_trace]
        dsimp only [t]
        have hn := pow_ne_zero 2 (unit_sub_inv_ne_zero s hs)
        field_simp [hn]
        ring
      obtain ⟨C, hC⟩ := exists_automorphism_of_trace
        (paperCommutator (SLTwo.tor s) (shear t)) g
        (commutator_nonscalar s hs t) hg hc
      have hv : paperCommutator (SLTwo.tor s) (shear t) ∈
          (OuterWord.bracket l r).values (SLTwo.SL2 F) :=
        (OuterWord.mem_values_bracket l r _).mpr
          ⟨SLTwo.tor s, ihl _ (tor_nonscalar s hs),
            shear t, ihr _ (shear_nonscalar t), rfl⟩
      have hm := (OuterWord.bracket l r).map_mem_values (automorphism C).toMonoidHom hv
      change automorphism C (paperCommutator (SLTwo.tor s) (shear t)) ∈
        (OuterWord.bracket l r).values (SLTwo.SL2 F) at hm
      rwa [hC] at hm

/-- Every finite field with more than three elements supplies the diagonal. -/
theorem nonscalar_mem_values [Finite F] (hcard : 3 < Nat.card F)
    (w : OuterWord) (g : SLTwo.SL2 F) (hg : Nonscalar g) :
    g ∈ w.values (SLTwo.SL2 F) := by
  obtain ⟨s, hs⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ)
    (by decide : (2 : ℕ) ≠ 0) (show 2 < Nat.card Fˣ by rw [Nat.card_units]; omega)
  have hs' : (s : F) ^ 2 ≠ 1 := by
    intro h
    apply hs
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  exact nonscalar_mem_values_of_unit s hs' w g hg

end Kourovka2135.SLTwoNonscalarWordValues
