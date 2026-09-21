import Kourovka2135.CoinducedCharacterFormula
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Coinduction of an actual unit-valued linear character: its dimension,
central scalar action, and trace when the identity right coset is the unique
fixed coset. No irreducibility or character classification is assumed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CoinducedLinearCharacter

open CoinducedCharacterFormula
open scoped BigOperators

variable {k G : Type*} [Field k] [Group G]

/-- The one-dimensional representation of an actual unit-valued homomorphism. -/
def linear (S : Subgroup G) (χ : S →* kˣ) : Representation k S k where
  toFun s := (χ s : k) • (1 : Module.End k k)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, Units.val_mul, mul_smul_comm, mul_one, smul_smul, mul_comm]

@[simp] theorem linear_apply (S : Subgroup G) (χ : S →* kˣ) (s : S) (a : k) :
    linear S χ s a = (χ s : k) * a := rfl

@[simp] theorem linear_character (S : Subgroup G) (χ : S →* kˣ) (s : S) :
    (linear S χ).character s = (χ s : k) := by
  change LinearMap.trace k k ((χ s : k) • (1 : Module.End k k)) = _
  simp only [map_smul, LinearMap.trace_one, Module.finrank_self, Nat.cast_one,
    smul_eq_mul, mul_one]

abbrev Space (S : Subgroup G) (χ : S →* kˣ) :=
  Representation.coindV S.subtype (linear S χ)

def induced (S : Subgroup G) (χ : S →* kˣ) : Representation k G (Space S χ) :=
  Representation.coind S.subtype (linear S χ)

/-- Central elements already in the inducing subgroup act by their given scalar. -/
theorem induced_central (S : Subgroup G) (χ : S →* kˣ) (z : S)
    (hz : (z : G) ∈ Subgroup.center G) :
    induced S χ (z : G) = (χ z : k) • (1 : Module.End k (Space S χ)) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext g
  change v.1 (g * (z : G)) = (χ z : k) * v.1 g
  rw [(Subgroup.mem_center_iff.mp hz g)]
  exact v.2 z g

variable [Finite G]

instance spaceFiniteDimensional (S : Subgroup G) (χ : S →* kˣ) :
    FiniteDimensional k (Space S χ) :=
  FiniteDimensional.of_injective
    (coindVEquivQuotient S (linear S χ)).toLinearMap
    (coindVEquivQuotient S (linear S χ)).injective

/-- The actual induced dimension is the number of right cosets. -/
theorem finrank_space (S : Subgroup G) (χ : S →* kˣ) :
    Module.finrank k (Space S χ) = Nat.card (RightCosets S) := by
  rw [(coindVEquivQuotient S (linear S χ)).finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

omit [Finite G] in
/-- Representatives of the identity right coset belong to the subgroup. -/
theorem out_identity_mem (S : Subgroup G) :
    Quotient.out (Quotient.mk (QuotientGroup.rightRel S) (1 : G)) ∈ S := by
  have h := rightCosetOut_spec S (1 : G)
  simpa only [one_mul, inv_inv, rightCosetOut] using S.inv_mem h

/-- The sole fixed-coset coefficient is the original character at the element.
The chosen representative of the identity coset need not be the identity. -/
theorem character_eq_of_unique_fixed_coset (S : Subgroup G) (χ : S →* kˣ)
    (t : S)
    (hfixed : ∀ q : RightCosets S,
      Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * (t : G)) = q ↔
        q = Quotient.mk (QuotientGroup.rightRel S) (1 : G)) :
    (induced S χ).character (t : G) = (χ t : k) := by
  classical
  rw [induced, coind_character_formula]
  let q₀ : RightCosets S := Quotient.mk (QuotientGroup.rightRel S) (1 : G)
  rw [Finset.sum_eq_single q₀]
  · have hq := (hfixed q₀).mpr rfl
    rw [dite_eq_left hq, linear_character]
    let s : S := ⟨Quotient.out q₀, out_identity_mem S⟩
    have heq : fixedConjugate S q₀ (t : G) hq = s * t * s⁻¹ := by
      apply Subtype.ext
      rfl
    rw [heq, map_mul, map_mul, map_inv]
    simp [mul_comm]
  · intro q _ hq
    exact dite_eq_right (fun h => hq ((hfixed q).mp h))
  · simp

end Kourovka2135.CoinducedLinearCharacter
