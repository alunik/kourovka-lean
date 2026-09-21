import Kourovka2135.MonomialTrace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Subrepresentation

/-! The actual regular representation on functions and its actual constant
line. Its character detects the identity coefficient of any finite weighted
sum, while the constant line records the total weight.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RegularCharacter

open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable (k G : Type*) [Field k] [Group G]

def regular : Representation k G (G → k) where
  toFun g := LinearMap.funLeft k k (fun h : G => h * g)
  map_one' := by ext x h; simp
  map_mul' g h := by ext x t; simp [mul_assoc]

@[simp] theorem regular_apply (g : G) (x : G → k) (h : G) :
    regular k G g x h = x (h * g) := rfl

def constantEmbedding : k →ₗ[k] (G → k) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constantEmbedding_injective : Function.Injective (constantEmbedding k G) := by
  intro a b h
  exact congrFun h (1 : G)

def constants : Subrepresentation (regular k G) where
  toSubmodule := (constantEmbedding k G).range
  apply_mem_toSubmodule g x hx := by
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩

theorem constants_finrank : Module.finrank k (constants k G).toSubmodule = 1 := by
  change Module.finrank k (constantEmbedding k G).range = 1
  rw [LinearMap.finrank_range_of_inj (constantEmbedding_injective k G), Module.finrank_self]

theorem constants_apply (g : G) : (constants k G).toRepresentation g = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, ha⟩ := x.property
  change regular k G g (x : G → k) = (x : G → k)
  rw [← ha]
  rfl

theorem constants_character (g : G) : (constants k G).toRepresentation.character g = 1 := by
  let : FiniteDimensional k (constants k G).toSubmodule :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) (constants_finrank k G)
  change LinearMap.trace k (constants k G).toSubmodule ((constants k G).toRepresentation g) = 1
  rw [constants_apply, LinearMap.trace_one, constants_finrank, Nat.cast_one]

variable [Finite G]

theorem regular_character (g : G) :
    (regular k G).character g = if g = 1 then (Nat.card G : k) else 0 := by
  classical
  change LinearMap.trace k (G → k) (regular k G g) = _
  rw [MonomialTrace.trace_pi_map_perm (Module.Basis.singleton Unit k)
    (fun h : G => h * g) (fun _ : G => (1 : Module.End k k)) (regular k G g)
    (fun _ _ => rfl)]
  by_cases hg : g = 1
  · subst g
    simp [LinearMap.trace_one, Nat.card_eq_fintype_card]
  · simp [hg, mul_eq_left]

theorem weighted_regular_character (f : G → k) :
    ∑ g : G, f g * (regular k G).character g = (Nat.card G : k) * f 1 := by
  classical
  simp [regular_character, mul_comm]

theorem weighted_constants_character (f : G → k) :
    ∑ g : G, f g * (constants k G).toRepresentation.character g = ∑ g : G, f g := by
  simp only [constants_character, mul_one]

end Kourovka2135.RegularCharacter
