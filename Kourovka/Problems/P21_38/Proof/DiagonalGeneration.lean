import Kourovka.Problems.P21_38.Proof.CompanionConstruction
import Kourovka.Problems.P21_38.Proof.CorePerfect
import Kourovka.Problems.P21_38.Proof.CommutatorExtraction
import Kourovka.Problems.P21_38.Proof.SubgroupGeneration

/-!
# Generation of the diagonal subgroup

Containing the compact core reduces ordinary generation to the endpoint
characters. An element with both endpoint exponents one generates the common
integer character of the diagonal subgroup. Local interpolation supplies the
required core containment by the proved perfectness of the core.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- An element with endpoint exponents `(1,1)` realizes every diagonal
endpoint character by an integer power. -/
theorem endpointCharacter_zpow_of_exponents_one (g : F)
    (hg0 : leftExponent g = 1) (hg1 : rightExponent g = 1) (n : ℤ) :
    endpointCharacter (g ^ n) = Multiplicative.ofAdd (n, n) := by
  rw [map_zpow, endpointCharacter_apply, hg0, hg1, ← ofAdd_zsmul]
  simp

/-- A subgroup of the diagonal that contains the endpoint kernel and an
element of common endpoint exponent one is the whole diagonal subgroup. -/
theorem eq_diagonalSubgroup_of_ker_le {H : Subgroup F}
    (hH : H ≤ diagonalSubgroup) (hker : endpointCharacter.ker ≤ H)
    {g : F} (hg : g ∈ H) (hg0 : leftExponent g = 1)
    (hg1 : rightExponent g = 1) : H = diagonalSubgroup := by
  apply le_antisymm hH
  intro z hz
  have hchar : endpointCharacter z = endpointCharacter (g ^ leftExponent z) := by
    rw [endpointCharacter_zpow_of_exponents_one g hg0 hg1, endpointCharacter_apply]
    exact congrArg Multiplicative.ofAdd (Prod.ext rfl ((mem_diagonalSubgroup z).mp hz).symm)
  have hres : z * (g ^ leftExponent z)⁻¹ ∈ endpointCharacter.ker := by
    change endpointCharacter (z * (g ^ leftExponent z)⁻¹) = 1
    rw [map_mul, map_inv, hchar, mul_inv_cancel]
  have hmem := H.mul_mem (hker hres) (H.zpow_mem hg (leftExponent z))
  simpa only [inv_mul_cancel_right] using hmem

/-- The closure of a pair in `F` maps to its ordinary closure in rational
permutations. -/
theorem map_pair_closure (f g : F) :
    (Subgroup.closure ({f, g} : Set F)).map (compactF 0 1).subtype =
      ambientPair f g := by
  rw [MonoidHom.map_closure]
  simp [ambientPair]

/-- Containment of the ambient compact core is exactly containment of the
endpoint kernel in the closure taken inside `F`. -/
theorem ker_le_pair_closure_iff (f g : F) :
    endpointCharacter.ker ≤ Subgroup.closure ({f, g} : Set F) ↔
      compactCore 0 ≤ ambientPair f g := by
  rw [← map_endpointCharacter_ker, ← map_pair_closure]
  exact (Subgroup.map_le_map_iff_of_injective (Subtype.val_injective)).symm

/-- Core containment and a companion of common endpoint exponent one imply
ordinary generation of the actual diagonal subgroup. -/
theorem generatesPair_diagonal_of_core_le (f g : diagonalSubgroup)
    (hg0 : leftExponent (g : F) = 1)
    (hg1 : rightExponent (g : F) = 1)
    (hcore : compactCore 0 ≤ ambientPair (f : F) (g : F)) :
    GeneratesPair f g := by
  apply (generatesPair_subgroup_iff diagonalSubgroup f g).mpr
  apply eq_diagonalSubgroup_of_ker_le (g := (g : F))
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact f.property
    · exact (Set.mem_singleton_iff.mp hz) ▸ g.property
  · exact (ker_le_pair_closure_iff (f : F) (g : F)).mpr hcore
  · exact Subgroup.subset_closure (by simp)
  · exact hg0
  · exact hg1

/-- Local interpolation implies containment of the compact core because its
commutator subgroup has already been proved equal to the core. -/
theorem compactCore_le_of_local_interpolation
    {H : Subgroup (Equiv.Perm ℚ)} (hlocal : CoreLocalInterpolation 0 H) :
    compactCore 0 ≤ H := by
  rw [← compactCore_commutator_eq]
  exact commutator_compactCore_le_of_local_interpolation hlocal

/-- Local interpolation for the ordinary two-generated subgroup completes
the generation argument once the companion has endpoint exponents one. -/
theorem generatesPair_diagonal_of_local_interpolation (f g : diagonalSubgroup)
    (hg0 : leftExponent (g : F) = 1)
    (hg1 : rightExponent (g : F) = 1)
    (hlocal : CoreLocalInterpolation 0 (ambientPair (f : F) (g : F))) :
    GeneratesPair f g :=
  generatesPair_diagonal_of_core_le f g hg0 hg1
    (compactCore_le_of_local_interpolation hlocal)

#audit_axioms generatesPair_diagonal_of_core_le
#audit_axioms generatesPair_diagonal_of_local_interpolation

end Kourovka.P21_38
