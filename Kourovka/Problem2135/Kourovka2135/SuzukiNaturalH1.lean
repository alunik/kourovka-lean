import Kourovka2135.SuzukiBorelWeightH1
import Kourovka2135.RepresentationCohomologyAlternative

/-! The actual natural Suzuki representation has first cohomology dimension
at most one when q≥32. The proof uses its concrete Borel flag and injective
odd-index restriction. There is no assumed irreducible-module classification,
cohomological support theorem, or assertion for q=8.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiNaturalH1

open CategoryTheory SuzukiGeometry SuzukiNaturalBorelFiltration

/-- Genuine finite dimensionality of the ambient cohomology. -/
theorem finiteDimensional_H1 (m : ℕ) :
    FiniteDimensional (K m)
      (groupCohomology (Rep.of (SuzukiTorusMovingRank.natural m)) 1) :=
  CohomologyH1FiltrationBound.finiteDimensional_H1
    (Rep.of (SuzukiTorusMovingRank.natural m))

theorem zero_layer_H1 (m : ℕ) :
    Module.finrank (K m) (groupCohomology (Rep.of (layer m 0)) 1) = 0 := by
  let : Subsingleton (flag m 0) := flag_zero_subsingleton m
  let : Subsingleton (groupCohomology (Rep.of (layer m 0)) 1) :=
    ((ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (groupCohomology.H1π (Rep.of (layer m 0))))).subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- Four actual short exact sequences bound the Borel H1 by its sole surviving
scalar weight. -/
theorem finrank_borel_H1_le_one (m : ℕ) (hm : 2 ≤ m) :
    Module.finrank (K m) (groupCohomology (Rep.of (representation m)) 1) ≤ 1 := by
  have h0 := finrank_H1_step_le m (0 : Fin 4)
  have h1 := finrank_H1_step_le m (1 : Fin 4)
  have h2 := finrank_H1_step_le m (2 : Fin 4)
  have h3 := finrank_H1_step_le m (3 : Fin 4)
  have z0 := SuzukiBorelWeightH1.finrank_H1_eq_zero m hm 0 (by decide)
  have z2 := SuzukiBorelWeightH1.finrank_H1_eq_zero m hm 2 (by decide)
  have z3 := SuzukiBorelWeightH1.finrank_H1_eq_zero m hm 3 (by decide)
  have b1 := SuzukiBorelWeightH1.finrank_H1_le_one m 1
  have zz := zero_layer_H1 m
  have ht := RepresentationCohomologyAlternative.finrank_cohomology_eq
    (layer m 4) (representation m) (topEquiv m) 1
  change Module.finrank (K m) (groupCohomology (Rep.of (layer m 1)) 1) ≤
    Module.finrank (K m) (groupCohomology (Rep.of (layer m 0)) 1) +
      Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m 0)) 1) at h0
  change Module.finrank (K m) (groupCohomology (Rep.of (layer m 2)) 1) ≤
    Module.finrank (K m) (groupCohomology (Rep.of (layer m 1)) 1) +
      Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m 1)) 1) at h1
  change Module.finrank (K m) (groupCohomology (Rep.of (layer m 3)) 1) ≤
    Module.finrank (K m) (groupCohomology (Rep.of (layer m 2)) 1) +
      Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m 2)) 1) at h2
  change Module.finrank (K m) (groupCohomology (Rep.of (layer m 4)) 1) ≤
    Module.finrank (K m) (groupCohomology (Rep.of (layer m 3)) 1) +
      Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m 3)) 1) at h3
  omega

/-- The defining natural Suzuki representation, with its actual ambient
matrix-group action, has H1 of dimension at most one for q≥32. -/
theorem finrank_H1_le_one (m : ℕ) (hm : 2 ≤ m) :
    Module.finrank (K m)
      (groupCohomology (Rep.of (SuzukiTorusMovingRank.natural m)) 1) ≤ 1 := by
  let : FiniteDimensional (K m)
      (groupCohomology (Rep.res (borel m).subtype
        (Rep.of (SuzukiTorusMovingRank.natural m))) 1) :=
    CohomologyH1FiltrationBound.finiteDimensional_H1
      (Rep.res (borel m).subtype (Rep.of (SuzukiTorusMovingRank.natural m)))
  have hinj := GroupCohomology.restriction_injective_of_odd_index
    (borel m) (Rep.of (SuzukiTorusMovingRank.natural m)) 1 (odd_borel_index m)
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (finrank_borel_H1_le_one m hm)

end Kourovka2135.SuzukiNaturalH1
