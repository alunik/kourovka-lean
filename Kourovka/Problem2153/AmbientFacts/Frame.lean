import Kourovka.Problem2153.AmbientFacts.Frame.Checks
import Kourovka.Problem2153.AmbientFacts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Kourovka.Problem2153.WilsonModel.Frame

open Field8 Matrix

def generator : Fin 6 → GL26 := ![tUnit, xUnit, rhoUnit, sigmaUnit, torusUnit 1 0, torusUnit 0 1]

theorem generator_matrix (k : Fin 6) : ((generator k : GL26) : Mat) = generatorMatrix k := by
  fin_cases k <;> rfl

/-- Matrix-word prefixes use only generators already proved to belong to the actual ambient group. -/
def wordPrefix (j : Fin 27) : ℕ → GL26
  | 0 => 1
  | n + 1 => wordPrefix j n * generator (words j (Fin.ofNat 48 n))

theorem generator_mem (k : Fin 6) : generator k ∈ ambient := by
  fin_cases k
  · exact tUnit_mem
  · exact xUnit_mem
  · exact rhoUnit_mem
  · exact sigmaUnit_mem
  · exact torusUnit_mem 1 0
  · exact torusUnit_mem 0 1

theorem prefix_mem (j : Fin 27) (n : ℕ) : wordPrefix j n ∈ ambient := by
  induction n with
  | zero => exact ambient.one_mem
  | succ n ih => exact ambient.mul_mem ih (generator_mem _)

/-- Each sparse transition certificate is transported to the actual matrix product. -/
theorem prefix_row (j : Fin 27) (k : Fin 49) :
    vecMul basisZero ((wordPrefix j k.val : GL26) : Mat) = traces j k := by
  induction k using Fin.induction with
  | zero => simpa only [wordPrefix, Units.val_one, vecMul_one] using (trace_starts j).symm
  | succ k ih =>
    change vecMul basisZero ((wordPrefix j k.val : GL26) : Mat) = traces j k.castSucc at ih
    change vecMul basisZero ((wordPrefix j k.val * generator (words j (Fin.ofNat 48 k.val)) : GL26) : Mat) = _
    have hk : Fin.ofNat 48 k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
    rw [hk, Units.val_mul, generator_matrix, ← vecMul_vecMul, ih,
      sparseRowAction_eq _ _ (generator_alignment _), trace_steps]

def orbitElement (j : Fin 27) : ambient := ⟨wordPrefix j 48, prefix_mem j 48⟩

theorem orbitElement_row (j : Fin 27) :
    vecMul basisZero ((orbitElement j).val : Mat) = traces j 48 := prefix_row j 48

/-- The actual 27-line certificate makes any ambient matrix preserving these lines scalar,
then its proved determinant one forces it to be the identity. -/
theorem eq_one_of_frame_lines (g : ambient)
    (hFrame : ∀ i : Fin 26, ∃ a : F8, vecMul (frameMatrix i) (g.val : Mat) = a • frameMatrix i)
    (hBridge : ∃ a : F8, vecMul bridgeVector (g.val : Mat) = a • bridgeVector) : g = 1 := by
  have hb : ∃ a : F8, vecMul (vecMul bridgeCoordinates frameMatrix) (g.val : Mat) =
      a • vecMul bridgeCoordinates frameMatrix := by
    simpa only [bridge_coordinates_check] using hBridge
  obtain ⟨a, ha⟩ := scalar_of_row_frame frameMatrix frameInverse (g.val : Mat)
    bridgeCoordinates frame_mul_inverse inverse_mul_frame bridge_coordinates_nonzero hFrame hb
  have hg := scalar_matrix_eq_one_of_card_eight Field8.card (g.val : Mat) a ha (ambient_det g)
  apply Subtype.ext
  exact Units.ext hg

/-- Faithfulness on the orbit of the base line, proved for the actual Wilson group. -/
theorem eq_one_of_orbit_lines (g : ambient)
    (hLines : ∀ k : ambient, ∃ a : F8,
      vecMul (vecMul basisZero (k.val : Mat)) (g.val : Mat) =
        a • vecMul basisZero (k.val : Mat)) : g = 1 := by
  apply eq_one_of_frame_lines g
  · intro i
    simpa only [orbitElement_row, trace_ends] using hLines (orbitElement i.castSucc)
  · simpa only [orbitElement_row, bridge_trace_end] using hLines (orbitElement 26)

private def matrixHom : ambient →* Mat := (Units.coeHom Mat).comp ambient.subtype

/-- Every subgroup stabilizing the base line has trivial normal core. This discharges the
faithfulness input for the intended parabolic once its line-stabilizing property is proved. -/
theorem normalCore_eq_bot_of_line_stabilizing (P : Subgroup ambient)
    (hLine : ∀ g ∈ P, ∃ a : F8, vecMul basisZero (g.val : Mat) = a • basisZero) :
    P.normalCore = ⊥ := by
  apply P.normalCore.eq_bot_iff_forall.mpr
  intro g hg
  apply eq_one_of_orbit_lines g
  intro k
  obtain ⟨a, ha⟩ := hLine (k * g * k⁻¹) (hg k)
  refine ⟨a, ?_⟩
  change vecMul basisZero (matrixHom (k * g * k⁻¹)) = a • basisZero at ha
  have hh := congrArg (fun v => vecMul v (matrixHom k)) ha
  rw [vecMul_vecMul, ← map_mul, show (k * g * k⁻¹) * k = k * g by simp [mul_assoc],
    map_mul, ← vecMul_vecMul, smul_vecMul] at hh
  exact hh

/-- The actual subgroup stabilizing the base row line, with a nonzero scalar witness. -/
def baseLineStabilizer : Subgroup ambient where
  carrier := {g | ∃ a : F8ˣ, vecMul basisZero (matrixHom g) = (a : F8) • basisZero}
  one_mem' := ⟨1, by simp only [map_one, vecMul_one, Units.val_one, one_smul]⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨a, ha⟩ := hg
    obtain ⟨b, hb⟩ := hh
    refine ⟨a * b, ?_⟩
    rw [map_mul, ← vecMul_vecMul, ha, smul_vecMul, hb, smul_smul, Units.val_mul]
  inv_mem' := by
    intro g hg
    obtain ⟨a, ha⟩ := hg
    refine ⟨a⁻¹, ?_⟩
    have hh := congrArg (fun v => vecMul v (matrixHom g⁻¹)) ha
    rw [vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, vecMul_one, smul_vecMul] at hh
    have hi := congrArg (fun v => ((a⁻¹ : F8ˣ) : F8) • v) hh
    simp only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at hi
    exact hi.symm

theorem mem_baseLineStabilizer_iff (g : ambient) :
    g ∈ baseLineStabilizer ↔
      ∃ a : F8ˣ, vecMul basisZero (g.val : Mat) = (a : F8) • basisZero := Iff.rfl

theorem baseLineStabilizer_core : baseLineStabilizer.normalCore = ⊥ := by
  apply normalCore_eq_bot_of_line_stabilizing
  intro g hg
  obtain ⟨a, ha⟩ := hg
  exact ⟨(a : F8), ha⟩

theorem normalCore_eq_bot_of_le_baseLineStabilizer (P : Subgroup ambient)
    (hP : P ≤ baseLineStabilizer) : P.normalCore = ⊥ := by
  apply le_antisymm _ bot_le
  simpa only [baseLineStabilizer_core] using Subgroup.normalCore_mono hP

theorem sigma_not_mem_baseLineStabilizer :
    (⟨sigmaUnit, sigmaUnit_mem⟩ : ambient) ∉ baseLineStabilizer := by
  intro hg
  obtain ⟨a, ha⟩ := hg
  have hh := congrFun ha (1 : Fin 26)
  change vecMul basisZero sigma 1 = (a : F8) * 0 at hh
  have hs : vecMul basisZero sigma 1 = 1 := by decide +kernel
  rw [hs, mul_zero] at hh
  exact one_ne_zero hh

theorem baseLineStabilizer_ne_top : baseLineStabilizer ≠ ⊤ := by
  intro heq
  apply sigma_not_mem_baseLineStabilizer
  rw [heq]
  exact Subgroup.mem_top _

#print axioms prefix_row
#print axioms eq_one_of_frame_lines
#print axioms eq_one_of_orbit_lines
#print axioms normalCore_eq_bot_of_line_stabilizing
#print axioms baseLineStabilizer_core
#print axioms normalCore_eq_bot_of_le_baseLineStabilizer
#print axioms baseLineStabilizer_ne_top

end Kourovka.Problem2153.WilsonModel.Frame
