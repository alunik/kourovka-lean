import Kourovka2135.BinarySLTwoPrimeFieldH2

/-! The actual scalar-trivial second cohomology of SL2 over a field of four
 elements has dimension at most one over F2. The unique possible degree-two
 torus-fixed coordinate is the mixed monomial. The proof uses the checked
 ordinary-cohomology restriction and diagonal coordinate maps, then the
 actual empty-tensor equivalence and scalar-extension dimension comparison.
 No Schur-multiplier or group-extension premise is used. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryFourTrivialH2

open BinarySurvivorWeights BinarySurvivorDegree BinaryCochainGraded
open BinaryTorusFixedCoordinates DiagonalFixedCoordinates

/-- Every empty-support degree-two zero-weight exponent in extension degree
 two is the mixed monomial. The weights used by the checked torus action
 are 2 and 4, whose sum is zero modulo 3. -/
theorem zeroWeight_exponent_eq
    (a : ZeroWeightIndex (∅ : Finset (Fin 2)) 2) :
    a.val.val.val = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 := by
  obtain ⟨i, j, _, _, he⟩ := survivor_two_exists ∅ a.val
  have hw := a.property
  rw [he, map_add, generatorWeight_single, generatorWeight_single] at hw
  fin_cases i <;> fin_cases j
  · norm_num [Nat.ModEq] at hw
  · exact he
  · exact he.trans (add_comm _ _)
  · norm_num [Nat.ModEq] at hw

/-- There is at most one degree-two zero-weight coordinate. -/
theorem subsingleton_zeroWeightIndex :
    Subsingleton (ZeroWeightIndex (∅ : Finset (Fin 2)) 2) := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (zeroWeight_exponent_eq a).trans (zeroWeight_exponent_eq b).symm

section Coordinates
variable (k : Type*) [Field k]

/-- A primitive torus element has at most one fixed degree-two coordinate
 for the empty coefficient support. -/
theorem subsingleton_fixedIndex (r : kˣ) (hr : orderOf r = 2 ^ 2 - 1) :
    Subsingleton (FixedIndex (character k (∅ : Finset (Fin 2)) r 2)) := by
  let := subsingleton_zeroWeightIndex
  exact (fixedIndexEquiv k ∅ r hr 2).injective.subsingleton

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Any actual injective equivariant coordinate map gives the fixed-space
 bound of one. -/
theorem finrank_fixed_le_one (r : kˣ) (hr : orderOf r = 2 ^ 2 - 1)
    (T : V →ₗ[k] V) (q : V →ₗ[k] (SurvivorIndex (∅ : Finset (Fin 2)) 2 → k))
    (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k ∅ r 2 a * q v a) :
    Module.finrank k (T - LinearMap.id).ker ≤ 1 := by
  let := subsingleton_fixedIndex k r hr
  exact (finrank_fixed_le T q (character k ∅ r 2) hq hdiag).trans
    (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)

end Coordinates

section ContainingField
variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ 2)

/-- The actual ordinary additive-group H2 fixed by a primitive torus element
 has dimension at most one for the empty tensor. -/
theorem finrank_additive_fixed_H2_le_one (r : Fˣ)
    (hr : orderOf (Units.map σ.toMonoidHom r) = 2 ^ 2 - 1) :
    Module.finrank k
      ((BinaryAdditiveTorusAction.cohomologyMap k (∅ : Finset (Fin 2)) σ hcard r 2).hom -
        LinearMap.id).ker ≤ 1 :=
  finrank_fixed_le_one k (Units.map σ.toMonoidHom r) hr
    (BinaryAdditiveTorusAction.cohomologyMap k ∅ σ hcard r 2).hom
    (BinaryAdditiveTorusBounds.coordinate k ∅ σ hcard 1)
    (BinaryAdditiveTorusBounds.coordinate_injective k ∅ σ hcard 1)
    (BinaryAdditiveTorusBounds.coordinate_cohomologyMap k ∅ σ hcard r 1)

include hcard in
/-- Actual ordinary H2 of SL2 with the empty tensor has dimension at most one. -/
theorem finrank_empty_H2_le_one :
    Module.finrank k
      (groupCohomology (BinaryTensorSLTwoRestriction.ambient k (∅ : Finset (Fin 2)) σ) 2)
      ≤ 1 := by
  obtain ⟨r, hr⟩ := BinaryAdditiveTorusBounds.exists_primitive k σ hcard
  exact (BinaryTensorSLTwoCohomology.finrank_le_fixed k ∅ σ hcard r 1 (Or.inr rfl)).trans
    (finrank_additive_fixed_H2_le_one k σ hcard r hr)

include σ hcard in
/-- Actual scalar-trivial H2 over any characteristic-two containing field
 has dimension at most one for SL2 over a field of four elements. -/
theorem finrank_trivial_H2_le_one :
    Module.finrank k
      (groupCohomology (Rep.of (Representation.trivial k (SLTwo.SL2 F) k)) 2) ≤ 1 := by
  rw [← (BinarySLTwoTrivialCohomology.emptyTrivialCohomologyIso k σ 2 2).toLinearEquiv.finrank_eq]
  exact finrank_empty_H2_le_one k σ hcard

end ContainingField

section PrimeField
variable (F : Type) [Field F] [Fintype F] [CharP F 2]

/-- The actual scalar-trivial ordinary second cohomology of SL2 over a field
 of four elements has dimension at most one over F2. -/
theorem finrank_H2_le_one (hcard : Fintype.card F = 4) :
    Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2))) 2)
      ≤ 1 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rw [← BinarySLTwoPrimeFieldH2.finrank_trivial_H2_fieldExtension (ZMod 2) F (SLTwo.SL2 F)]
  exact finrank_trivial_H2_le_one F (RingHom.id F) (by simpa using hcard)

end PrimeField
end Kourovka2135.BinaryFourTrivialH2
