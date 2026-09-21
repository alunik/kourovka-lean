import Kourovka2135.SuzukiNaturalBorelFiltration
import Kourovka2135.TitsRootH1WeightBound
import Kourovka2135.ScalarPowerAdditivity
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The actual scalar factors of the natural Suzuki Borel flag satisfy the
checked Tits-root cohomology bounds. Exhaustive coordinates, root-triviality,
odd index and forward torus conjugation are all derived from the concrete
matrix group. The three vanishing weights require m ≥ 2; q = 8 is left explicit.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiBorelWeightH1

open CategoryTheory BenderSuzuki.MatrixGroups SuzukiGeometry
open SuzukiNaturalBorelFiltration
open scoped Matrix MatrixGroups

/-- The actual root subgroup inside the actual Borel. -/
def S (m : ℕ) : Subgroup (B m) := (root m).comap (borel m).subtype

theorem root_le_borel (m : ℕ) : root m ≤ borel m :=
  Subgroup.comap_mono (show rootGL m ≤ borelGL m from le_sup_left)

def rootEquivalence (m : ℕ) : S m ≃* root m :=
  Subgroup.subgroupOfEquivOfLe (root_le_borel m)

@[simp] theorem rootInBorel_rootEquivalence (m : ℕ) (x : S m) :
    rootInBorel m (rootEquivalence m x) = (x : B m) := rfl

def rootElement (m : ℕ) (a b : K m) : root m :=
  ⟨⟨SuzukiRootGL m a b, rootGL_le_group m
    (Subgroup.subset_closure ⟨a, b, rfl⟩)⟩,
    Subgroup.subset_closure ⟨a, b, rfl⟩⟩

def rootCoordinate (m : ℕ) (a b : K m) : S m :=
  (rootEquivalence m).symm (rootElement m a b)

theorem rootCoordinate_mul (m : ℕ) (a b c d : K m) :
    rootCoordinate m a b * rootCoordinate m c d =
      rootCoordinate m (a + c) (b + d + a * tits m c) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact suzukiRootGL_mul m (tits m) (SuzukiTorusMovingRank.tits_sq m)
    (SuzukiTorusMovingRank.tits_apply m) a b c d

theorem rootCoordinate_surjective (m : ℕ) (x : S m) :
    ∃ a b : K m, x = rootCoordinate m a b := by
  obtain ⟨a, b, hab⟩ := (suzukiRootGL_mem_closure_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    (((x : B m) : G m) : GL (Fin 4) (K m))).mp x.property
  refine ⟨a, b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hab

theorem card_root_subgroup (m : ℕ) : Nat.card (S m) = (q m) ^ 2 := by
  rw [Nat.card_congr (rootEquivalence m).toEquiv, card_root]

theorem root_index (m : ℕ) : (S m).index = q m - 1 := by
  have hpos : 0 < (q m) ^ 2 := pow_pos (lt_trans Nat.zero_lt_one (one_lt_q m)) _
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    (q m) ^ 2 * (S m).index = Nat.card (B m) := by
      rw [← card_root_subgroup]
      exact (S m).card_mul_index
    _ = (q m) ^ 2 * (q m - 1) := card_borel m

theorem odd_root_index (m : ℕ) : Odd (S m).index := by
  rw [root_index]
  have he := Nat.even_iff.mp (even_q m)
  have hq := one_lt_q m
  exact Nat.odd_iff.mpr (by omega)

instance weight_root_trivial (m : ℕ) (i : Fin 4) :
    (Rep.res (S m).subtype (Rep.of (weightRepresentation m i))).ρ.IsTrivial where
  out x := by
    apply LinearMap.ext
    intro v
    change weightRepresentation m i (x : B m) v = v
    rw [weightRepresentation_apply,
      ← rootInBorel_rootEquivalence m x, diagonalCharacter_root]
    simp

theorem torus_mem_normalizer (m : ℕ) (u : (K m)ˣ) :
    torusInBorel m u ∈ Subgroup.normalizer (S m : Set (B m)) := by
  intro x
  exact (torusGL_le_normalizer_rootGL m
    (Subgroup.subset_closure ⟨u, rfl⟩))
      (((x : B m) : G m) : GL (Fin 4) (K m))

def torusAction (m : ℕ) (u : (K m)ˣ) : MulAut (S m) :=
  (S m).normalizerMonoidHom ⟨torusInBorel m u, torus_mem_normalizer m u⟩

theorem torusAction_coe (m : ℕ) (u : (K m)ˣ) (x : S m) :
    (torusAction m u x : B m) = torusInBorel m u * (x : B m) *
      (torusInBorel m u)⁻¹ := rfl

theorem torusAction_root (m : ℕ) (u : (K m)ˣ) (a b : K m) :
    torusAction m u (rootCoordinate m a b) =
      rootCoordinate m ((u : K m) * a) ((u : K m) * tits m (u : K m) * b) := by
  apply Subtype.ext
  rw [torusAction_coe]
  apply Subtype.ext
  apply Subtype.ext
  exact suzukiTorusGL_conj_root m (tits m) (SuzukiTorusMovingRank.tits_sq m)
    (SuzukiTorusMovingRank.tits_apply m) a b u

def weightCharacter (m : ℕ) (i : Fin 4) : (K m)ˣ →* (K m)ˣ :=
  (diagonalCharacter m i).comp (torusInBorel m)

theorem weight_scalar (m : ℕ) (i : Fin 4) (u : (K m)ˣ) (v : K m) :
    weightRepresentation m i (torusInBorel m u) v = (weightCharacter m i u : K m) * v := rfl

/-- Every actual scalar factor contributes at most one dimension. -/
theorem finrank_H1_le_one (m : ℕ) (i : Fin 4) :
    Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m i)) 1) ≤ 1 := by
  exact TitsRootH1WeightBound.finrank_H1_le_one (S m) (weightRepresentation m i)
    (tits m) (SuzukiTorusMovingRank.tits_sq m) (rootCoordinate m)
    (rootCoordinate_mul m) (weightCharacter m i) (torusAction m) (torusInBorel m)
    (torusAction_coe m) (torusAction_root m) (weight_scalar m i)
    (odd_root_index m) (rootCoordinate_surjective m)

/-- The zero-extended actual diagonal torus weight. -/
def weightFunction (m : ℕ) (i : Fin 4) (x : K m) : K m :=
  ![x ^ (1 + 2 ^ m), x ^ (2 ^ m), (x ^ (2 ^ m))⁻¹,
    (x ^ (1 + 2 ^ m))⁻¹] i

theorem weightFunction_zero (m : ℕ) (i : Fin 4) : weightFunction m i 0 = 0 := by
  fin_cases i <;> simp [weightFunction]

theorem weightFunction_units (m : ℕ) (i : Fin 4) (u : (K m)ˣ) :
    weightFunction m i (u : K m) = (weightCharacter m i u : K m) := by
  change _ = (diagonalCharacter m i (torusInBorel m u) : K m)
  rw [diagonalCharacter_torus]
  rfl

theorem q_power (m : ℕ) : q m = 2 * (2 ^ m) ^ 2 := by
  change 2 ^ (2 * m + 1) = _
  rw [show 2 * m + 1 = m + m + 1 by omega, pow_add, pow_add]
  ring

theorem natural_inverse_weight_card_bound (m : ℕ) (hm : 2 ≤ m) :
    2 * (1 + 2 ^ m) + 2 < Nat.card (K m) := by
  have hp : 4 ≤ 2 ^ m := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hm
    norm_num at h
    exact h
  rw [SuzukiTorusMovingRank.card_field]
  change 2 * (1 + 2 ^ m) + 2 < q m
  rw [q_power]
  nlinarith

/-- For q≥32, only the second diagonal weight can be additive. -/
theorem weightFunction_not_additive (m : ℕ) (hm : 2 ≤ m) (i : Fin 4) (hi : i ≠ 1) :
    ¬ ∀ x y : K m, weightFunction m i (x + y) =
      weightFunction m i x + weightFunction m i y := by
  have hcard := natural_inverse_weight_card_bound m hm
  have hpow : 0 < 2 ^ m := Nat.pow_pos (by decide : 0 < 2)
  fin_cases i
  · simpa [weightFunction, Nat.add_comm] using
      ScalarPowerAdditivity.frobenius_plus_one_not_additive (F := K m) m
        (by omega) (by omega)
  · exact False.elim (hi rfl)
  · simpa [weightFunction] using
      ScalarPowerAdditivity.inverse_power_not_additive (F := K m) (2 ^ m) hpow (by omega)
  · simpa [weightFunction] using
      ScalarPowerAdditivity.inverse_power_not_additive (F := K m) (1 + 2 ^ m)
        (by omega) hcard

/-- Actual H1 vanishing of the three unwanted Borel factors. -/
theorem subsingleton_H1 (m : ℕ) (hm : 2 ≤ m) (i : Fin 4) (hi : i ≠ 1) :
    Subsingleton (groupCohomology (Rep.of (weightRepresentation m i)) 1) := by
  exact TitsRootH1WeightBound.subsingleton_H1_of_not_additive
    (S m) (weightRepresentation m i) (tits m) (SuzukiTorusMovingRank.tits_sq m)
    (rootCoordinate m) (rootCoordinate_mul m) (weightCharacter m i)
    (torusAction m) (torusInBorel m) (torusAction_coe m) (torusAction_root m)
    (weight_scalar m i) (odd_root_index m) (rootCoordinate_surjective m)
    (weightFunction m i) (weightFunction_zero m i) (weightFunction_units m i)
    (weightFunction_not_additive m hm i hi)

theorem finrank_H1_eq_zero (m : ℕ) (hm : 2 ≤ m) (i : Fin 4) (hi : i ≠ 1) :
    Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m i)) 1) = 0 := by
  let := subsingleton_H1 m hm i hi
  exact Module.finrank_zero_of_subsingleton

end Kourovka2135.SuzukiBorelWeightH1
