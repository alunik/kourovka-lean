import Kourovka2135.BinarySteinbergCohomology
import Kourovka2135.BinarySLTwoIrreducibleCohomology

/-! For SL2 over four elements, every irreducible coefficient of dimension
other than one has zero second cohomology. The two singleton tensors and
the full-support tensor are handled by proved coordinate calculations. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.BinaryFourIrreducibleCohomology

open BinaryTensorSLTwoRestriction

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V) [ρ.IsIrreducible]

include σ in
/-- The empty support is the only tensor case not covered by H2 vanishing. -/
theorem subsingleton_H2 (hcard : Fintype.card F = 2 ^ 2)
    (hdim : Module.finrank k V ≠ 1) :
    Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  classical
  obtain ⟨I, ⟨e⟩⟩ := BinarySLTwoIrreducibleClassification.exists_tensor_equiv k σ ρ 2 hcard
  have hI : I ≠ ∅ := by
    intro h
    apply hdim
    rw [e.toLinearEquiv.finrank_eq,
      Module.finrank_eq_card_basis (BinaryTensorCoefficient.basis k I),
      Fintype.card_finset, Fintype.card_coe, h, Finset.card_empty, pow_zero]
  have hs : Subsingleton (groupCohomology (ambient k I σ) 2) := by
    by_cases hsingle : I.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hsingle
      exact BinaryTensorSLTwoCohomology.subsingleton_H2_singleton_at_two k σ hcard i
    · have hle : I.card ≤ 2 := by simpa using Finset.card_le_univ I
      have hpos : 0 < I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
      have hcardI : I.card = 2 := by omega
      have heq : I = Finset.univ := Finset.eq_univ_of_card I (by simpa using hcardI)
      rw [heq]
      exact BinarySteinbergCohomology.subsingleton_ambient k σ hcard 1
  let : Subsingleton (groupCohomology (ambient k I σ) 2) := hs
  exact (BinarySLTwoIrreducibleCohomology.cohomologyIso k σ ρ I e 2).toLinearEquiv.injective.subsingleton

end Kourovka2135.BinaryFourIrreducibleCohomology
