import Kourovka.Problem2153.Borel
import Kourovka.Problem2153.AmbientFacts.Frame

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem
open WilsonModel Field8 Matrix

theorem basisZero_single : Frame.basisZero = Pi.single (0 : Fin 26) (1 : F8) := by
  decide +kernel

theorem rootMatrix_first_diagonal :
    (fun (i : Fin 12) (a : Fin 8) => RootData.rootMatrix i a 0 0) =
      (fun _ _ => (1 : F8)) := by decide +kernel

theorem root_fixes_base (i : Fin 12) (a : Fin 8) :
    vecMul Frame.basisZero ((root i a).val : WilsonModel.Mat) = Frame.basisZero := by
  rw [RootData.root_alignment, basisZero_single, single_vecMul, one_smul]
  funext j
  by_cases hj : j = 0
  · subst j
    simpa using congrFun (congrFun rootMatrix_first_diagonal i) a
  · have hz := rootMatrix_lower i a 0 j (Fin.pos_iff_ne_zero.mpr hj)
    simpa [Pi.single_apply, hj, Ne.symm hj] using hz

theorem root_mem_baseLineStabilizer (i : Fin 12) (a : Fin 8) :
    root i a ∈ Frame.baseLineStabilizer := by
  rw [Frame.mem_baseLineStabilizer_iff]
  exact ⟨1, by simpa using root_fixes_base i a⟩

theorem U_le_baseLineStabilizer : U ≤ Frame.baseLineStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨curve,hcurve,a,rfl⟩
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hcurve
  rcases hcurve with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact root_mem_baseLineStabilizer _ a

theorem torus_mem_baseLineStabilizer (a b : Fin 7) :
    torus a b ∈ Frame.baseLineStabilizer := by
  rw [Frame.mem_baseLineStabilizer_iff]
  refine ⟨Units.mk0 (torusDiag a b 0) (torusDiag_ne_zero a b 0), ?_⟩
  change vecMul Frame.basisZero (diagonal (torusDiag a b)) = torusDiag a b 0 • Frame.basisZero
  rw [basisZero_single, single_vecMul, one_smul]
  funext j
  by_cases hj : j = 0
  · subst j
    simp
  · simp [diagonal_apply, hj, Ne.symm hj, Pi.single_apply]

theorem H_le_baseLineStabilizer : H ≤ Frame.baseLineStabilizer := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact torus_mem_baseLineStabilizer a b

theorem r_mem_baseLineStabilizer : r ∈ Frame.baseLineStabilizer := by
  rw [Frame.mem_baseLineStabilizer_iff]
  refine ⟨1, ?_⟩
  change vecMul Frame.basisZero rho = (1 : F8) • Frame.basisZero
  rw [one_smul, basisZero_single, single_vecMul, one_smul]
  decide +kernel

theorem P_le_baseLineStabilizer : P ≤ Frame.baseLineStabilizer := by
  apply sup_le (sup_le U_le_baseLineStabilizer H_le_baseLineStabilizer)
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain rfl := Set.mem_singleton_iff.mp hg
  exact r_mem_baseLineStabilizer

/-- The intended parabolic is proper, without identifying it with the full line stabilizer. -/
theorem P_ne_top : P ≠ ⊤ := by
  intro h
  apply Frame.sigma_not_mem_baseLineStabilizer
  apply P_le_baseLineStabilizer
  rw [h]
  exact Subgroup.mem_top _

/-- The actual 27 orbit lines make the parabolic core trivial. -/
theorem P_normalCore : P.normalCore = ⊥ :=
  Frame.normalCore_eq_bot_of_le_baseLineStabilizer P P_le_baseLineStabilizer

end Kourovka.Problem2153.RootSystem
