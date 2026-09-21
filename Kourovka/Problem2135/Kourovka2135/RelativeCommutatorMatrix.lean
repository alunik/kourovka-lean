import Kourovka2135.IrreducibleMatrixAveraging
import Kourovka2135.DerivedCentralization

/-! Actual relative commutator sums for a genuine extension of an irreducible
representation. The convention is `[x,y] = x⁻¹ * y⁻¹ * x * y`. Both finite
matrix averages are derived from Schur's lemma in the imported module. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RelativeCommutatorMatrix

open Representation
open scoped BigOperators

variable {k G V : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (N : Subgroup G) [Fintype N]
variable (ρ : Representation k N V) [ρ.IsIrreducible]
variable (α : Representation k G V) (hα : ∀ n : N, α (n : G) = ρ n)

/-- Inverting the summation variable gives the other conjugation convention. -/
theorem sum_inverse_conjugates (T : Module.End k V) :
    (∑ n : N, ρ n⁻¹ * T * ρ n) =
      (((Fintype.card N : k) / (Module.finrank k V : k)) * LinearMap.trace k V T) •
        (1 : Module.End k V) := by
  calc
    (∑ n : N, ρ n⁻¹ * T * ρ n) =
        ∑ n : N, ρ n * T * ρ n⁻¹ := by
      refine Fintype.sum_bijective Inv.inv inv_involutive.bijective _ _ ?_
      intro n
      rw [inv_inv]
    _ = _ := IrreducibleMatrixAveraging.sum_conjugates ρ T

include hα in
/-- Average in the first kernel variable, leaving the exact second-variable operator. -/
theorem sum_first_variable (a b : G) (v : N) :
    (∑ u : N, α (paperCommutator (a * (u : G)) (b * (v : G)))) =
      (((Fintype.card N : k) / (Module.finrank k V : k)) *
        LinearMap.trace k V (ρ v⁻¹ * α b⁻¹)) • (α b * ρ v) := by
  classical
  let T : Module.End k V := α a⁻¹ * (ρ v⁻¹ * α b⁻¹) * α a
  have hexp (u : N) :
      α (paperCommutator (a * (u : G)) (b * (v : G))) =
        (ρ u⁻¹ * T * ρ u) * (α b * ρ v) := by
    simp only [paperCommutator, mul_inv_rev, map_mul, ← Subgroup.coe_inv, hα,
      T, mul_assoc]
  have ht : LinearMap.trace k V T = LinearMap.trace k V (ρ v⁻¹ * α b⁻¹) := by
    dsimp only [T]
    rw [LinearMap.trace_mul_cycle, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simp_rw [hexp]
  rw [← Finset.sum_mul, sum_inverse_conjugates, ht]
  rw [smul_mul_assoc, one_mul]

include hα in
/-- The raw double-commutator matrix sum; no normality or finiteness of the ambient group
is needed once a genuine extension of the irreducible kernel representation is given. -/
theorem sum_paperCommutator (a b : G) :
    (∑ u : N, ∑ v : N,
      α (paperCommutator (a * (u : G)) (b * (v : G)))) =
        (((Fintype.card N : k) / (Module.finrank k V : k)) ^ 2) •
          (1 : Module.End k V) := by
  classical
  let c : k := (Fintype.card N : k) / (Module.finrank k V : k)
  rw [Finset.sum_comm]
  simp_rw [sum_first_variable N ρ α hα]
  change (∑ v : N, (c * LinearMap.trace k V (ρ v⁻¹ * α b⁻¹)) •
    (α b * ρ v)) = c ^ 2 • (1 : Module.End k V)
  calc
    (∑ v : N, (c * LinearMap.trace k V (ρ v⁻¹ * α b⁻¹)) • (α b * ρ v)) =
        c • (α b * (∑ v : N, LinearMap.trace k V (ρ v⁻¹ * α b⁻¹) • ρ v)) := by
      simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
    _ = c • (α b * (c • α b⁻¹)) := by
      rw [IrreducibleMatrixAveraging.sum_trace_mul_inverse ρ]
    _ = c ^ 2 • (1 : Module.End k V) := by
      rw [mul_smul_comm, ← map_mul, mul_inv_cancel, map_one, smul_smul, pow_two]

include hα in
/-- Left shifting the actual sum and taking trace gives the relative character sum. -/
theorem sum_character_inv_mul_paperCommutator (a b t : G) :
    (∑ u : N, ∑ v : N,
      α.character (t⁻¹ * paperCommutator (a * (u : G)) (b * (v : G)))) =
        (((Fintype.card N : k) / (Module.finrank k V : k)) ^ 2) *
          α.character t⁻¹ := by
  classical
  calc
    (∑ u : N, ∑ v : N,
        α.character (t⁻¹ * paperCommutator (a * (u : G)) (b * (v : G)))) =
        LinearMap.trace k V (α t⁻¹ *
          (∑ u : N, ∑ v : N,
            α (paperCommutator (a * (u : G)) (b * (v : G))))) := by
      simp only [Representation.character, map_mul, Finset.mul_sum, map_sum]
    _ = _ := by
      rw [sum_paperCommutator N ρ α hα, mul_smul_comm, mul_one, map_smul,
        smul_eq_mul]
      rfl

end Kourovka2135.RelativeCommutatorMatrix
