import Kourovka2135.SuzukiTensorBorelFiltration
import Kourovka2135.SuzukiBorelWeightH1
import Kourovka2135.ScalarWeightFrobeniusSupport
import Kourovka2135.GroupCohomologyFieldExtension

/-! The actual tensor module has H1 bounded by the number of its Borel
diagonal weights that are Frobenius characters, counting pure-basis tuples
with multiplicity. Scalar support follows from normalized additive maps;
the ambient bound uses actual odd-index Borel restriction. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorBorelCohomology

open SuzukiTorusMovingRank SuzukiTensorBorelFiltration
open SuzukiBorelWeightH1 (S rootCoordinate rootCoordinate_mul torusAction
  torusAction_coe torusAction_root odd_root_index rootCoordinate_surjective)
open SuzukiNaturalBorelFiltration (B torusInBorel rootInBorel)

variable (m : ℕ) (I : Finset (Fin (2 * m + 1)))

/-- The actual full torus character is a Frobenius power. -/
def Supported (a : Index m I) : Prop :=
  ∃ j : Fin (2 * m + 1), ∀ u : (K m)ˣ,
    (torusCharacter m I a u : K m) = (u : K m) ^ (2 ^ j.val)

/-- Multiplicities are pure-basis tuples, including coincident characters. -/
def supportCount : ℕ := by
  classical
  exact (Finset.univ.filter (Supported m I)).card

/-- Actual character support gives the precise exponent congruence used in counting. -/
theorem supported_residue (a : Index m I) (ha : Supported m I a) :
    ∃ j : Fin (2 * m + 1),
      (tensorExponent m I a : ZMod (2 ^ (2 * m + 1) - 1)) = 2 ^ j.val := by
  obtain ⟨j, hj⟩ := ha
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (K m)ˣ)
  have he : u ^ tensorExponent m I a = u ^ ((2 ^ j.val : ℕ) : ℤ) := by
    rw [← torusCharacter_exponent, zpow_natCast]
    apply Units.ext
    simpa using hj u
  have hc := zpow_eq_zpow_iff_modEq.mp he
  rw [hu, Nat.card_units, card_field] at hc
  refine ⟨j, ?_⟩
  exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).mpr hc

instance scalar_root_trivial (a : Index m I) :
    (Rep.res (S m).subtype (Rep.of (scalar m I a))).ρ.IsTrivial where
  out x := by
    apply LinearMap.ext
    intro v
    change scalar m I a (x : B m) v = v
    rw [scalar_apply, ← SuzukiBorelWeightH1.rootInBorel_rootEquivalence m x,
      tensorCharacter_root]
    simp

theorem scalar_torus (a : Index m I) (u : (K m)ˣ) (v : K m) :
    scalar m I a (torusInBorel m u) v = (torusCharacter m I a u : K m) * v := rfl

/-- Actual root restriction and the first coordinate, into additive weight maps. -/
def weightRestriction (a : Index m I) :
    groupCohomology (Rep.of (scalar m I a)) 1 →ₗ[K m]
      ScalarWeightAdditiveMaps.weightSpace (torusCharacter m I a) :=
  TitsRootH1WeightBound.weightRestriction (S m) (scalar m I a)
    (SuzukiGeometry.tits m) (tits_sq m) (rootCoordinate m)
    (rootCoordinate_mul m) (torusCharacter m I a) (torusAction m) (torusInBorel m)
    (torusAction_coe m) (torusAction_root m) (scalar_torus m I a)

theorem weightRestriction_injective (a : Index m I) :
    Function.Injective (weightRestriction m I a) :=
  TitsRootH1WeightBound.weightRestriction_injective (S m) (scalar m I a)
    (SuzukiGeometry.tits m) (tits_sq m) (rootCoordinate m)
    (rootCoordinate_mul m) (torusCharacter m I a) (torusAction m) (torusInBorel m)
    (torusAction_coe m) (torusAction_root m) (scalar_torus m I a)
    (odd_root_index m) (rootCoordinate_surjective m)

theorem scalar_finrank_H1_le_one (a : Index m I) :
    Module.finrank (K m) (groupCohomology (Rep.of (scalar m I a)) 1) ≤ 1 :=
  TitsRootH1WeightBound.finrank_H1_le_one (S m) (scalar m I a)
    (SuzukiGeometry.tits m) (tits_sq m) (rootCoordinate m)
    (rootCoordinate_mul m) (torusCharacter m I a) (torusAction m) (torusInBorel m)
    (torusAction_coe m) (torusAction_root m) (scalar_torus m I a)
    (odd_root_index m) (rootCoordinate_surjective m)

theorem scalar_H1_subsingleton (a : Index m I) (ha : ¬ Supported m I a) :
    Subsingleton (groupCohomology (Rep.of (scalar m I a)) 1) := by
  have hf : Module.finrank (ZMod 2) (K m) = 2 * m + 1 :=
    GaloisField.finrank 2 (by omega)
  let : Subsingleton (ScalarWeightAdditiveMaps.weightSpace (torusCharacter m I a)) :=
    ScalarWeightFrobeniusSupport.weightSpace_subsingleton (torusCharacter m I a) (by
      rw [hf]
      exact ha)
  exact (weightRestriction_injective m I a).subsingleton

theorem scalar_finrank_H1_eq_zero (a : Index m I) (ha : ¬ Supported m I a) :
    Module.finrank (K m) (groupCohomology (Rep.of (scalar m I a)) 1) = 0 := by
  let := scalar_H1_subsingleton m I a ha
  exact Module.finrank_zero_of_subsingleton

/-- The full actual Borel tensor flag, with proved scalar support and multiplicity. -/
theorem finrank_borel_H1_le_count :
    Module.finrank (K m) (groupCohomology (Rep.of (representation m I)) 1) ≤
      supportCount m I := by
  classical
  apply (SuzukiTensorBorelFiltration.finrank_H1_le_sum m I).trans
  calc
    _ ≤ ∑ a : Index m I, if Supported m I a then 1 else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : Supported m I a
      · simpa [ha] using scalar_finrank_H1_le_one m I a
      · simp [ha, scalar_finrank_H1_eq_zero m I a ha]
    _ = supportCount m I := by rw [supportCount, Finset.card_filter]

/-- The actual Suzuki tensor representation, using its odd-index Borel. -/
theorem finrank_H1_le_count :
    Module.finrank (K m) (groupCohomology
      (Rep.of (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m)))) 1) ≤
      supportCount m I := by
  let : FiniteDimensional (K m)
      (groupCohomology (Rep.res (SuzukiGeometry.borel m).subtype
        (Rep.of (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m))))) 1) :=
    CohomologyH1FiltrationBound.finiteDimensional_H1 _
  have hinj := GroupCohomology.restriction_injective_of_odd_index
    (SuzukiGeometry.borel m)
    (Rep.of (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m)))) 1
    (SuzukiGeometry.odd_borel_index m)
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (finrank_borel_H1_le_count m I)

/-- The same bound survives every coefficient field extension. -/
theorem finrank_H1_baseChange_le_count (k : Type) [Field k] [Algebra (K m) k] :
    Module.finrank k (groupCohomology
      (Rep.of (RepresentationDensityBaseChange.baseChange k
        (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m))))) 1) ≤
      supportCount m I := by
  rw [GroupCohomologyFieldExtension.finrank_H1_baseChange]
  exact finrank_H1_le_count m I

end Kourovka2135.SuzukiTensorBorelCohomology
