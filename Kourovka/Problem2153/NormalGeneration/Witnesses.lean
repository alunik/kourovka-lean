import Kourovka.Problem2153.NormalGeneration.RootSubgroup
import Kourovka.Problem2153.Borel

set_option autoImplicit false
namespace Kourovka.Problem2153.RootSystem

theorem witnessX_eq_root : WilsonModel.X = root 11 1 := by
  rw [root_one]
  apply Subtype.ext
  change WilsonModel.witnessXUnit =
    (WilsonModel.sigmaUnit * WilsonModel.rhoUnit * WilsonModel.sigmaUnit)⁻¹ *
      WilsonModel.xUnit ^ 2 *
      (WilsonModel.sigmaUnit * WilsonModel.rhoUnit * WilsonModel.sigmaUnit)
  rw [WilsonModel.witnessXUnit_word, WilsonModel.srsUnit_word]

theorem witnessY_eq_root : WilsonModel.Y = root 11 2 := by
  rw [WilsonModel.Y_eq_conj_X]
  change rightConj WilsonModel.X (torus 1 0) = _
  rw [witnessX_eq_root, root_conj_torus]
  have h : parameterAction 11 1 0 1 = 2 := by decide +kernel
  rw [h]

theorem witnessX_mem_Z : WilsonModel.X ∈ Z := by
  rw [witnessX_eq_root]
  exact Subgroup.subset_closure ⟨1, rfl⟩

theorem witnessY_mem_Z : WilsonModel.Y ∈ Z := by
  rw [witnessY_eq_root]
  exact Subgroup.subset_closure ⟨2, rfl⟩

theorem witnessX_commute_U {u : G} (hu : u ∈ U) : Commute WilsonModel.X u :=
  U_le_centralizer_Z hu WilsonModel.X witnessX_mem_Z

theorem witnessY_commute_U {u : G} (hu : u ∈ U) : Commute WilsonModel.Y u :=
  U_le_centralizer_Z hu WilsonModel.Y witnessY_mem_Z

#print axioms witnessX_eq_root
#print axioms witnessY_eq_root
end Kourovka.Problem2153.RootSystem
