import Kourovka2135.BinarySLTwoIrreducibleClassification
import Kourovka2135.BinaryTensorSLTwoCohomology

/-! Low-degree cohomology for arbitrary irreducible binary SL2 representations.

The actual classification equivalence induces an actual ordinary group
cohomology isomorphism. Coefficient and cohomology finite-dimensionality
are consequences, not hypotheses. These bounds are over a coefficient
field containing the finite parameter field; no descent statement is made.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySLTwoIrreducibleCohomology

open CategoryTheory
open BinaryTensorSLTwoRestriction

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type u} [Field F] (σ : F →+* k)
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V)

/-- The actual representation equivalence induces ordinary group cohomology isomorphisms. -/
def cohomologyIso {f : ℕ} (I : Finset (Fin f))
    (e : ρ.Equiv (BinaryTensorSLTwo.representation k σ I)) (n : ℕ) :
    groupCohomology (Rep.of ρ) n ≅ groupCohomology (ambient k I σ) n :=
  groupCohomology.mapIso (MulEquiv.refl (SLTwo.SL2 F)) e.toLinearEquiv
    (fun g => e.isIntertwining' g) n

/-- Exact transport of cohomology dimension, without finiteness assumptions. -/
theorem finrank_eq_tensor {f : ℕ} (I : Finset (Fin f))
    (e : ρ.Equiv (BinaryTensorSLTwo.representation k σ I)) (n : ℕ) :
    Module.finrank k (groupCohomology (Rep.of ρ) n) =
      Module.finrank k (groupCohomology (ambient k I σ) n) :=
  (cohomologyIso k σ ρ I e n).toLinearEquiv.finrank_eq

variable [Fintype F] [ρ.IsIrreducible]

include σ ρ

/-- Arbitrary irreducible coefficients are finite-dimensional as a proved consequence. -/
theorem finiteDimensional_coefficient (f : ℕ) (hcard : Fintype.card F = 2 ^ f) :
    FiniteDimensional k V := by
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ f hcard
  let : FiniteDimensional k (BinaryTensorCoefficient.Carrier k I) :=
    Module.Finite.of_basis (BinaryTensorCoefficient.basis k I)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- All positive-degree ordinary cohomology groups are finite-dimensional. -/
theorem finiteDimensional_cohomology (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (n : ℕ) :
    FiniteDimensional k (groupCohomology (Rep.of ρ) (n + 1)) := by
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ f hcard
  have := BinaryTensorSLTwoCohomology.finiteDimensional_ambient k I σ hcard n
  exact FiniteDimensional.of_injective (cohomologyIso k σ ρ I e (n + 1)).hom.hom
    (cohomologyIso k σ ρ I e (n + 1)).toLinearEquiv.injective

/-- Every irreducible coefficient has first cohomology of dimension at most one for f ≥ 2. -/
theorem finrank_H1_le (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ 1 := by
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ f hcard
  rw [finrank_eq_tensor k σ ρ I e 1]
  exact BinaryTensorSLTwoCohomology.finrank_H1_le k I σ hcard hf

/-- Nontrivial actual H1 forces an actual equivalence to one natural Frobenius factor. -/
theorem exists_singleton_equiv_of_H1_nontrivial (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    ∃ i : Fin f, Nonempty (ρ.Equiv (BinaryTensorSLTwo.representation k σ {i})) := by
  classical
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ f hcard
  by_cases hI : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
    exact ⟨i, ⟨e⟩⟩
  · let : Subsingleton (groupCohomology (ambient k I σ) 1) :=
      BinaryTensorSLTwoCohomology.subsingleton_H1 k I σ hcard hf hI
    let : Subsingleton (groupCohomology (Rep.of ρ) 1) :=
      (cohomologyIso k σ ρ I e 1).toLinearEquiv.injective.subsingleton
    exact False.elim (false_of_nontrivial_of_subsingleton
      (groupCohomology (Rep.of ρ) 1))

/-- The dimension-based nonvanishing formulation also returns an actual singleton equivalence. -/
theorem exists_singleton_equiv_of_finrank_H1_ne_zero (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank k (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    ∃ i : Fin f, Nonempty (ρ.Equiv (BinaryTensorSLTwo.representation k σ {i})) := by
  classical
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ f hcard
  have hI : I.card = 1 := by
    by_contra hI
    apply hH
    rw [finrank_eq_tensor k σ ρ I e 1]
    exact BinaryTensorSLTwoCohomology.finrank_H1_eq_zero k I σ hcard hf hI
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨i, ⟨e⟩⟩

/-- Actual nonzero H1 forces the coefficient itself to have dimension two. -/
theorem finrank_coefficient_eq_two_of_H1_nontrivial (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] : Module.finrank k V = 2 := by
  classical
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_H1_nontrivial k σ ρ f hcard hf
  rw [e.toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (BinaryTensorCoefficient.basis k {i}),
    Fintype.card_finset, Fintype.card_coe, Finset.card_singleton, pow_one]

/-- The same coefficient-dimension conclusion follows from numerical H1 nonvanishing. -/
theorem finrank_coefficient_eq_two_of_finrank_H1_ne_zero (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hH : Module.finrank k (groupCohomology (Rep.of ρ) 1) ≠ 0) : Module.finrank k V = 2 := by
  classical
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_finrank_H1_ne_zero k σ ρ f hcard hf hH
  rw [e.toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (BinaryTensorCoefficient.basis k {i}),
    Fintype.card_finset, Fintype.card_coe, Finset.card_singleton, pow_one]

/-- Every irreducible coefficient of dimension other than two has genuinely vanishing H1. -/
theorem subsingleton_H1_of_finrank_ne_two (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) (hdim : Module.finrank k V ≠ 2) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  rcases subsingleton_or_nontrivial (groupCohomology (Rep.of ρ) 1) with hs | hn
  · exact hs
  · let : Nontrivial (groupCohomology (Rep.of ρ) 1) := hn
    exact False.elim (hdim (finrank_coefficient_eq_two_of_H1_nontrivial k σ ρ f hcard hf))

/-- Numerical vanishing outside coefficient dimension two. -/
theorem finrank_H1_eq_zero_of_finrank_ne_two (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) (hdim : Module.finrank k V ≠ 2) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) = 0 := by
  by_contra hH
  exact hdim (finrank_coefficient_eq_two_of_finrank_H1_ne_zero k σ ρ f hcard hf hH)

/-- In the nonzero-H1 case, H2 has dimension at most one for f ≥ 3. -/
theorem finrank_H2_le_of_H1_nontrivial (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank k (groupCohomology (Rep.of ρ) 2) ≤ 1 := by
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_H1_nontrivial k σ ρ f hcard (by omega)
  rw [finrank_eq_tensor k σ ρ {i} e 2]
  exact BinaryTensorSLTwoCohomology.finrank_H2_singleton_le k σ hcard hf i

/-- Numerical H1 nonvanishing gives the same H2 bound without a Nontrivial instance. -/
theorem finrank_H2_le_of_finrank_H1_ne_zero (f : ℕ)
    (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (hH : Module.finrank k (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank k (groupCohomology (Rep.of ρ) 2) ≤ 1 := by
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_finrank_H1_ne_zero k σ ρ f hcard (by omega) hH
  rw [finrank_eq_tensor k σ ρ {i} e 2]
  exact BinaryTensorSLTwoCohomology.finrank_H2_singleton_le k σ hcard hf i

/-- Over four parameters, actual H2 vanishes whenever actual H1 is nontrivial. -/
theorem subsingleton_H2_of_H1_nontrivial_at_two
    (hcard : Fintype.card F = 2 ^ 2) [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_H1_nontrivial k σ ρ 2 hcard (le_refl 2)
  let : Subsingleton (groupCohomology (ambient k {i} σ) 2) :=
    BinaryTensorSLTwoCohomology.subsingleton_H2_singleton_at_two k σ hcard i
  exact (cohomologyIso k σ ρ {i} e 2).toLinearEquiv.injective.subsingleton

/-- The exceptional four-parameter statement in dimension form. -/
theorem finrank_H2_eq_zero_of_H1_nontrivial_at_two
    (hcard : Fintype.card F = 2 ^ 2) [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    Module.finrank k (groupCohomology (Rep.of ρ) 2) = 0 := by
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_H1_nontrivial k σ ρ 2 hcard (le_refl 2)
  rw [finrank_eq_tensor k σ ρ {i} e 2]
  exact BinaryTensorSLTwoCohomology.finrank_H2_singleton_at_two_eq_zero k σ hcard i

/-- Numerical H1 nonvanishing also forces zero H2 dimension over four parameters. -/
theorem finrank_H2_eq_zero_of_finrank_H1_ne_zero_at_two
    (hcard : Fintype.card F = 2 ^ 2)
    (hH : Module.finrank k (groupCohomology (Rep.of ρ) 1) ≠ 0) :
    Module.finrank k (groupCohomology (Rep.of ρ) 2) = 0 := by
  obtain ⟨i, ⟨e⟩⟩ := exists_singleton_equiv_of_finrank_H1_ne_zero k σ ρ 2 hcard (le_refl 2) hH
  rw [finrank_eq_tensor k σ ρ {i} e 2]
  exact BinaryTensorSLTwoCohomology.finrank_H2_singleton_at_two_eq_zero k σ hcard i

end Kourovka2135.BinarySLTwoIrreducibleCohomology
