import Kourovka2135.SuzukiTensorPrincipalSeriesMap
import Kourovka2135.BinaryExteriorGroupAlgebra

/-! Exact exponent coverage for the natural Frobenius tensor models.
The finite-field power map with exponent `1 + 2^m` has trivial kernel by
the actual Suzuki torus calculation, hence is bijective. A primitive unit
then turns its surjectivity into a congruence of natural exponents. The
checked binary-subset equivalence realizes the resulting exponent.
This includes `m = 0`, when the multiplicative group has order one. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiTensorWeightArithmetic

open SuzukiTorusMovingRank SuzukiTensorPrincipalSeriesMap

variable (m : ℕ)

/-- The relevant power map is an actual automorphism of the finite group
of field units; its bijectivity is proved, not a weight-list premise. -/
theorem power_bijective :
    Function.Bijective (powMonoidHom (1 + 2 ^ m) : (K m)ˣ →* (K m)ˣ) := by
  have hi : Function.Injective (powMonoidHom (1 + 2 ^ m) : (K m)ˣ →* (K m)ˣ) := by
    apply (injective_iff_map_eq_one _).mpr
    intro u hu
    by_contra hne
    apply outer_ne_one m u hne
    exact congrArg Units.val hu
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Every residue has a bounded preimage under multiplication by the
highest-weight factor. The strict bound is still valid for the field of
two elements. -/
theorem exists_reduced_preimage (n : ℕ) :
    ∃ s : ℕ, s < Nat.card (K m) - 1 ∧
      Nat.ModEq (Nat.card (K m) - 1) ((1 + 2 ^ m) * s) n := by
  classical
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := (K m)ˣ)
  have hord : orderOf r = Nat.card (K m) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_units]
  obtain ⟨u, hu⟩ := (power_bijective m).surjective (r ^ n)
  obtain ⟨s, hs, hsu⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (hr u))
  refine ⟨s, ?_, ?_⟩
  · simpa only [hord] using Finset.mem_range.mp hs
  · have he : r ^ ((1 + 2 ^ m) * s) = r ^ n := by
      calc
        r ^ ((1 + 2 ^ m) * s) = (r ^ s) ^ (1 + 2 ^ m) := by
          rw [← pow_mul, Nat.mul_comm (1 + 2 ^ m) s]
        _ = u ^ (1 + 2 ^ m) := congrArg (fun x : (K m)ˣ => x ^ (1 + 2 ^ m)) hsu
        _ = r ^ n := hu
    simpa only [hord] using (pow_eq_pow_iff_modEq.mp he)

/-- The subtype sum in the tensor weight is exactly the previously
verified finite binary-subset exponent. -/
theorem highestWeight_eq_subsetWeight (I : Finset (Fin (2 * m + 1))) :
    highestWeight m I = (1 + 2 ^ m) *
      BinaryExteriorGroupAlgebra.subsetWeight (2 * m + 1) I := by
  unfold highestWeight BinaryExteriorGroupAlgebra.subsetWeight
  exact congrArg (fun s : ℕ => (1 + 2 ^ m) * s)
    (Finset.sum_coe_sort I (fun i : Fin (2 * m + 1) => 2 ^ i.val))

/-- All reduced principal-series characters are attained by genuine
natural Frobenius tensor subsets. No field embedding or representation
classification is used in this arithmetic statement. -/
theorem exists_subset_weight (n : ℕ) :
    ∃ I : Finset (Fin (2 * m + 1)),
      Nat.ModEq (Nat.card (K m) - 1) (highestWeight m I) n := by
  obtain ⟨s, hs, he⟩ := exists_reduced_preimage m n
  have hsq : s < 2 ^ (2 * m + 1) := by
    rw [card_field m] at hs
    omega
  let I := (BinaryExteriorGroupAlgebra.subsetExponentEquiv (2 * m + 1)).symm ⟨s, hsq⟩
  have hI : BinaryExteriorGroupAlgebra.subsetWeight (2 * m + 1) I = s :=
    BinaryExteriorGroupAlgebra.subsetWeight_equiv_symm (2 * m + 1) ⟨s, hsq⟩
  refine ⟨I, ?_⟩
  rw [highestWeight_eq_subsetWeight, hI]
  exact he

end Kourovka2135.SuzukiTensorWeightArithmetic
