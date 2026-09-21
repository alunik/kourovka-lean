import Kourovka2135.SLTwoNonscalarWordValues
import Kourovka2135.GeneratingPairNielsen
import Mathlib.Tactic.LinearCombination

/-! A broad generating good set from the explicit trace family. The only
generation input is the concrete diagonal/shear criterion; the trace-zero
and trace-two adjustments are proved here by elementary Nielsen changes. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoTraceGoodSet
open scoped Matrix
open SLTwoNonscalarWordValues SLTwoGeneralLinearConjugation GeneratingPairNielsen
variable {F : Type*} [Field F]

def goodSet : Set (SLTwo.SL2 F) :=
  {g | Nonscalar g ∧ g.val.trace ≠ 2 ∧ g.val.trace ≠ 0}

theorem nonscalar_automorphism (C : Matrix.GeneralLinearGroup (Fin 2) F)
    {g : SLTwo.SL2 F} (hg : Nonscalar g) : Nonscalar (automorphism C g) := by
  rintro ⟨r, hr⟩
  apply hg
  refine ⟨r, ?_⟩
  calc
    g.val = (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F) * (automorphism C g).val *
        (↑C : Matrix (Fin 2) (Fin 2) F) := by
      rw [automorphism_val]
      simp [Matrix.mul_assoc]
    _ = (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) r *
        (↑C : Matrix (Fin 2) (Fin 2) F) := by rw [hr]
    _ = Matrix.scalar (Fin 2) r := by
      rw [← Matrix.scalar_comm r (fun z => Commute.all r z)
        (↑C⁻¹ : Matrix (Fin 2) (Fin 2) F), Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem automorphism_mem (C : Matrix.GeneralLinearGroup (Fin 2) F)
    {g : SLTwo.SL2 F} (hg : g ∈ goodSet) : automorphism C g ∈ goodSet := by
  exact ⟨nonscalar_automorphism C hg.1, by simpa only [trace_automorphism] using hg.2.1,
    by simpa only [trace_automorphism] using hg.2.2⟩

private theorem nonscalar_of_lower_left (g : SLTwo.SL2 F) (hg : g.val 1 0 ≠ 0) :
    Nonscalar g := by
  rintro ⟨r, hr⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hr
  exact hg (by simpa [Matrix.scalar] using h)

theorem shear_trace (t : F) : (shear t).val.trace = 2 + t := by
  simp [shear, Matrix.trace_fin_two]
  ring

theorem tor_shear_trace (s : Fˣ) (t : F) :
    (SLTwo.tor s * shear t).val.trace = (s : F) + (s : F)⁻¹ * (1 + t) := by
  change ((SLTwo.tor s).val * (shear t).val).trace = _
  simp [SLTwo.tor, shear, Matrix.trace_fin_two]

theorem tor_shear_nonscalar (s : Fˣ) (t : F) : Nonscalar (SLTwo.tor s * shear t) := by
  apply nonscalar_of_lower_left
  change ((SLTwo.tor s).val * (shear t).val) 1 0 ≠ 0
  simp [SLTwo.tor, shear]

theorem adjusted_shear (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1) (h2 : (2 : F) ≠ 0)
    (t : F) (ht : t ≠ 0)
    (hgen : Subgroup.closure ({SLTwo.tor s, shear t} : Set (SLTwo.SL2 F)) = ⊤) :
    ∃ b ∈ goodSet, paperCommutator (SLTwo.tor s) b =
      paperCommutator (SLTwo.tor s) (shear t) ∧
      Subgroup.closure ({SLTwo.tor s, b} : Set (SLTwo.SL2 F)) = ⊤ := by
  by_cases hz : (shear t).val.trace = 0
  · have ht2 : t = -2 := by rw [shear_trace] at hz; linear_combination hz
    have hp : (SLTwo.tor s * shear t).val.trace = (s : F) - (s : F)⁻¹ := by
      rw [tor_shear_trace, ht2]
      ring
    have hm : ((SLTwo.tor s)⁻¹ * shear t).val.trace = -((s : F) - (s : F)⁻¹) := by
      rw [SLTwo.tor_inv, tor_shear_trace, ht2]
      simp only [Units.val_inv_eq_inv_val, inv_inv]
      ring
    have hnp := unit_sub_inv_ne_zero s hs
    by_cases he : (SLTwo.tor s * shear t).val.trace = 2
    · refine ⟨(SLTwo.tor s)⁻¹ * shear t, ⟨?_, ?_, ?_⟩,
        commutator_inv_mul_left _ _, ?_⟩
      · rw [SLTwo.tor_inv]
        exact tor_shear_nonscalar _ _
      · rw [hm, ← hp, he]
        intro hbad
        have hf : (2 : F) * 2 = 0 := by linear_combination -hbad
        exact mul_ne_zero h2 h2 hf
      · rw [hm]
        exact neg_ne_zero.mpr hnp
      · rw [closure_pair_inv_mul_left, hgen]
    · refine ⟨SLTwo.tor s * shear t, ⟨tor_shear_nonscalar _ _, he, ?_⟩,
        commutator_mul_left _ _, ?_⟩
      · rwa [hp]
      · rw [closure_pair_mul_left, hgen]
  · refine ⟨shear t, ⟨shear_nonscalar t, ?_, hz⟩, rfl, hgen⟩
    rw [shear_trace]
    intro he
    apply ht
    linear_combination he

/-- The remaining structural input is a concrete two-matrix generation
criterion, to be proved from the actual soluble-overgroup calculation. -/
theorem isGeneratingGoodSet_of_shear_generation
    (s : Fˣ) (hs : (s : F) ^ 2 ≠ 1) (h2 : (2 : F) ≠ 0)
    (hsgood : SLTwo.tor s ∈ goodSet)
    (hgen : ∀ t : F, t ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, shear t} : Set (SLTwo.SL2 F)) = ⊤) :
    IsGeneratingGoodSet (goodSet (F := F)) := by
  intro g hg
  let t : F := (2 - g.val.trace) / ((s : F) - (s : F)⁻¹) ^ 2
  have hn := pow_ne_zero 2 (unit_sub_inv_ne_zero s hs)
  have ht : t ≠ 0 := div_ne_zero (sub_ne_zero.mpr hg.2.1.symm) hn
  have hc : (paperCommutator (SLTwo.tor s) (shear t)).val.trace = g.val.trace := by
    rw [commutator_trace]
    dsimp only [t]
    field_simp [hn]
    ring
  obtain ⟨b, hb, hcomm, hpair⟩ := adjusted_shear s hs h2 t ht (hgen t ht)
  obtain ⟨C, hC⟩ := exists_automorphism_of_trace
    (paperCommutator (SLTwo.tor s) (shear t)) g
    (commutator_nonscalar s hs t) hg.1 hc
  let f := (automorphism C).toMonoidHom
  refine ⟨f (SLTwo.tor s), automorphism_mem C hsgood, f b, automorphism_mem C hb, ?_, ?_⟩
  · calc
      paperCommutator (f (SLTwo.tor s)) (f b) = f (paperCommutator (SLTwo.tor s) b) := by
        simp only [paperCommutator, map_mul, map_inv]
      _ = f (paperCommutator (SLTwo.tor s) (shear t)) := congrArg f hcomm
      _ = g := hC
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hpair]
    exact Subgroup.map_top_of_surjective f (automorphism C).surjective

end Kourovka2135.SLTwoTraceGoodSet
