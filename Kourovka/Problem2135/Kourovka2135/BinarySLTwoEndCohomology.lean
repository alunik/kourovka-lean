import Kourovka2135.RepresentationDensityBaseChange
import Kourovka2135.BinarySLTwoIrreducibleCohomology
import Kourovka2135.GroupCohomologyFieldExtension
import Kourovka2135.GroupCohomologyScalarRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Low-degree cohomology over the actual commuting field.

For a finite irreducible module, its actual intertwining endomorphisms form
E. Density makes the concrete scalar extension to AlgebraicClosure E
irreducible. A finite binary parameter field embeds into that closure over
ZMod 2, even when it does not embed into E. The actual cochain dimension
comparisons then return the tensor-family bounds to the original field.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySLTwoEndCohomology

open MinimalEndMovingRank RepresentationDensityBaseChange
open scoped TensorProduct

section General
variable {K : Type u} [Field K] {F : Type u} [Field F]
variable {V : Type u} [AddCommGroup V] [Module K V] [Finite V]
variable (ρ : Representation K (SLTwo.SL2 F) V) [ρ.IsIrreducible]

/-- The chosen scalar extension is the algebraic closure of the actual endomorphism field. -/
abbrev ClosedField := AlgebraicClosure (EndField ρ)

/-- The underlying module of the actual scalar-extended commuting-field representation. -/
abbrev ExtendedCarrier := ClosedField ρ ⊗[EndField ρ] V

/-- Extend the actual unchanged over-End action, rather than selecting a model representation. -/
def extended : Representation (ClosedField ρ) (SLTwo.SL2 F) (ExtendedCarrier ρ) :=
  baseChange (ClosedField ρ) (overEnd ρ)

/-- This irreducibility is a consequence of density, not an absolute-simplicity premise. -/
instance extended_isIrreducible : (extended ρ).IsIrreducible :=
  overEnd_baseChange_isIrreducible ρ (ClosedField ρ)

omit [ρ.IsIrreducible] in
/-- The commuting algebra has finite degree over the original field. -/
theorem finiteDimensional_endField : FiniteDimensional K (EndField ρ) := by
  infer_instance

/-- The original finite carrier is finite-dimensional over the actual commuting field. -/
theorem finiteDimensional_endCoefficient : FiniteDimensional (EndField ρ) V := by
  infer_instance

/-- Extending scalars preserves the coefficient dimension over its commuting field. -/
theorem finrank_extended_coefficient :
    Module.finrank (ClosedField ρ) (ExtendedCarrier ρ) = Module.finrank (EndField ρ) V :=
  Module.finrank_baseChange

/-- The original coefficient dimension factors through its actual commuting field. -/
theorem finrank_coefficient_eq_endDegree_mul :
    Module.finrank K V = Module.finrank K (EndField ρ) * Module.finrank (EndField ρ) V :=
  (Module.finrank_mul_finrank K (EndField ρ) V).symm

/-- Restricting the actual over-End action recovers the original representation exactly. -/
theorem restrict_overEnd : GroupCohomologyScalarRestriction.restrict K (overEnd ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  exact overEnd_restrictScalars ρ g

variable [Fintype F]

omit [ρ.IsIrreducible] in
/-- Positive-degree ordinary cohomology is genuinely finite-dimensional. -/
theorem finiteDimensional_cohomology (n : ℕ) :
    FiniteDimensional K (groupCohomology (Rep.of ρ) (n + 1)) :=
  GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρ n

/-- The unchanged actual action satisfies the coefficient-field tower law in cohomology. -/
theorem finrank_cohomology_eq_end (n : ℕ) :
    Module.finrank K (groupCohomology (Rep.of ρ) (n + 1)) =
      Module.finrank K (EndField ρ) *
        Module.finrank (EndField ρ) (groupCohomology (Rep.of (overEnd ρ)) (n + 1)) := by
  have : FiniteDimensional K (EndField ρ) := finiteDimensional_endField ρ
  have : FiniteDimensional (EndField ρ) V := finiteDimensional_endCoefficient ρ
  have h := GroupCohomologyScalarRestriction.finrank_groupCohomology_restrict K (overEnd ρ) n
  rw [restrict_overEnd ρ] at h
  exact h

/-- Exact descent identity through the actual commuting field and its chosen closure. -/
theorem finrank_cohomology_eq_closed (n : ℕ) :
    Module.finrank K (groupCohomology (Rep.of ρ) (n + 1)) =
      Module.finrank K (EndField ρ) *
        Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) (n + 1)) := by
  have : FiniteDimensional (EndField ρ) V := finiteDimensional_endCoefficient ρ
  have h := GroupCohomologyFieldExtension.finrank_groupCohomology_baseChange
    (L := ClosedField ρ) (overEnd ρ) n
  change Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) (n + 1)) =
    Module.finrank (EndField ρ) (groupCohomology (Rep.of (overEnd ρ)) (n + 1)) at h
  rw [finrank_cohomology_eq_end, ← h]

/-- Numerical nonvanishing over the original field survives the actual scalar extension. -/
theorem finrank_closed_H1_ne_zero
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank (ClosedField ρ) (groupCohomology (Rep.of (extended ρ)) 1) ≠ 0 := by
  intro hc
  apply hH
  rw [finrank_cohomology_eq_closed ρ 0, hc, mul_zero]

omit [ρ.IsIrreducible] in
/-- Nontrivial ordinary H1 has positive dimension because finite-dimensionality was proved. -/
theorem finrank_H1_ne_zero_of_nontrivial [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0 := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) := finiteDimensional_cohomology ρ 0
  exact (Module.finrank_pos (R := K) (M := groupCohomology (Rep.of ρ) 1)).ne'

end General

section Binary
variable {K : Type u} [Field K] [CharP K 2]
variable {F : Type u} [Field F] [CharP F 2] [Fintype F]
variable {V : Type u} [AddCommGroup V] [Module K V] [Finite V]
variable (ρ : Representation K (SLTwo.SL2 F) V) [ρ.IsIrreducible]

/-- Embed the finite parameter field in the closure of E over the prime field.
No inclusion of F in the actual commuting field E is assumed. -/
def parameterEmbedding : F →+* ClosedField ρ := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  letI : Algebra (ZMod 2) (ClosedField ρ) := ZMod.algebra (ClosedField ρ) 2
  exact (IsAlgClosed.lift : F →ₐ[ZMod 2] ClosedField ρ).toRingHom

/-- Actual H1 over the original field is bounded by the actual endomorphism-field degree. -/
theorem finrank_H1_le_endDegree (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) ≤ Module.finrank K (EndField ρ) := by
  rw [finrank_cohomology_eq_closed ρ 0]
  have h := BinarySLTwoIrreducibleCohomology.finrank_H1_le
    (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) f hcard hf
  simpa only [mul_one] using Nat.mul_le_mul_left (Module.finrank K (EndField ρ)) h

/-- Numerical nonzero H1 forces coefficient dimension two over its actual endomorphism field. -/
theorem finrank_endCoefficient_eq_two_of_finrank_H1_ne_zero
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank (EndField ρ) V = 2 := by
  have h := BinarySLTwoIrreducibleCohomology.finrank_coefficient_eq_two_of_finrank_H1_ne_zero
    (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) f hcard hf
    (finrank_closed_H1_ne_zero ρ hH)
  rw [finrank_extended_coefficient] at h
  exact h

/-- Actual nontrivial H1 gives the same commuting-field dimension conclusion. -/
theorem finrank_endCoefficient_eq_two_of_H1_nontrivial
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank (EndField ρ) V = 2 :=
  finrank_endCoefficient_eq_two_of_finrank_H1_ne_zero ρ f hcard hf
    (finrank_H1_ne_zero_of_nontrivial ρ)

/-- Nonzero H1 determines the original coefficient dimension using only the End-field degree. -/
theorem finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K V = 2 * Module.finrank K (EndField ρ) := by
  rw [finrank_coefficient_eq_endDegree_mul ρ,
    finrank_endCoefficient_eq_two_of_finrank_H1_ne_zero ρ f hcard hf hH]
  exact Nat.mul_comm _ _

/-- Actual nontriviality gives the same numerical dichotomy over the original field. -/
theorem finrank_coefficient_eq_two_mul_endDegree_of_H1_nontrivial
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K V = 2 * Module.finrank K (EndField ρ) :=
  finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero ρ f hcard hf
    (finrank_H1_ne_zero_of_nontrivial ρ)

/-- A mismatch in the original-field dimension forces numerical H1 vanishing. -/
theorem finrank_H1_eq_zero_of_coefficient_ne_two_mul_endDegree
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank K V ≠ 2 * Module.finrank K (EndField ρ)) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) = 0 := by
  by_contra hH
  exact hdim (finrank_coefficient_eq_two_mul_endDegree_of_finrank_H1_ne_zero ρ f hcard hf hH)

/-- Original-field dimension mismatch gives genuine H1 vanishing. -/
theorem subsingleton_H1_of_coefficient_ne_two_mul_endDegree
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank K V ≠ 2 * Module.finrank K (EndField ρ)) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) := finiteDimensional_cohomology ρ 0
  exact (Module.finrank_zero_iff (R := K)).mp
    (finrank_H1_eq_zero_of_coefficient_ne_two_mul_endDegree ρ f hcard hf hdim)

/-- Numerical H1 vanishes outside commuting-field coefficient dimension two. -/
theorem finrank_H1_eq_zero_of_endCoefficient_ne_two
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank (EndField ρ) V ≠ 2) :
    Module.finrank K (groupCohomology (Rep.of ρ) 1) = 0 := by
  by_contra hH
  exact hdim (finrank_endCoefficient_eq_two_of_finrank_H1_ne_zero ρ f hcard hf hH)

/-- This is genuine vanishing of the original ordinary H1, not merely a finrank convention. -/
theorem subsingleton_H1_of_endCoefficient_ne_two
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hdim : Module.finrank (EndField ρ) V ≠ 2) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 1) := finiteDimensional_cohomology ρ 0
  exact (Module.finrank_zero_iff (R := K)).mp
    (finrank_H1_eq_zero_of_endCoefficient_ne_two ρ f hcard hf hdim)

/-- In the nonzero-H1 case, actual H2 has the same endomorphism-degree bound for f ≥ 3. -/
theorem finrank_H2_le_endDegree_of_finrank_H1_ne_zero
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) ≤ Module.finrank K (EndField ρ) := by
  rw [finrank_cohomology_eq_closed ρ 1]
  have h := BinarySLTwoIrreducibleCohomology.finrank_H2_le_of_finrank_H1_ne_zero
    (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) f hcard hf
    (finrank_closed_H1_ne_zero ρ hH)
  simpa only [mul_one] using Nat.mul_le_mul_left (Module.finrank K (EndField ρ)) h

/-- The H2 degree bound also accepts actual nontriviality of original H1. -/
theorem finrank_H2_le_endDegree_of_H1_nontrivial
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) ≤ Module.finrank K (EndField ρ) :=
  finrank_H2_le_endDegree_of_finrank_H1_ne_zero ρ f hcard hf
    (finrank_H1_ne_zero_of_nontrivial ρ)

/-- Over four parameters, nonzero original H1 forces zero original H2 dimension. -/
theorem finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two
    (hcard : Fintype.card F = 2 ^ 2)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank K (groupCohomology (Rep.of ρ) 2) = 0 := by
  rw [finrank_cohomology_eq_closed ρ 1]
  have h := BinarySLTwoIrreducibleCohomology.finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two
    (ClosedField ρ) (parameterEmbedding ρ) (extended ρ) hcard
    (finrank_closed_H1_ne_zero ρ hH)
  rw [h, mul_zero]

/-- Genuine original H2 vanishing at f=2 under numerical H1 nonvanishing. -/
theorem subsingleton_H2_of_finrank_H1_ne_zero_at_two
    (hcard : Fintype.card F = 2 ^ 2)
    (hH : Module.finrank K (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  have : FiniteDimensional K (groupCohomology (Rep.of ρ) 2) := finiteDimensional_cohomology ρ 1
  exact (Module.finrank_zero_iff (R := K)).mp
    (finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two ρ hcard hH)

/-- Genuine original H2 vanishing at f=2 under actual H1 nontriviality. -/
theorem subsingleton_H2_of_H1_nontrivial_at_two
    (hcard : Fintype.card F = 2 ^ 2) [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Subsingleton (groupCohomology (Rep.of ρ) 2) :=
  subsingleton_H2_of_finrank_H1_ne_zero_at_two ρ hcard (finrank_H1_ne_zero_of_nontrivial ρ)

end Binary
end Kourovka2135.BinarySLTwoEndCohomology
