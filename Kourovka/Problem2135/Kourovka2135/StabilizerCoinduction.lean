import Kourovka2135.CoinducedLinearCharacter
import Kourovka2135.FinitePermutationAugmentation

/-! Actual coinduction from a point stabilizer is the permutation module
on a transitive set. With mathlib's right-translation convention the
function associated to F is g ↦ F(g⁻¹ • x₀). The proof constructs both
directions on the original carriers; it is not a dimension argument. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.StabilizerCoinduction

variable (k G X : Type u) [Field k] [Group G] [MulAction G X]
variable (x₀ : X)

abbrev Stabilizer := MulAction.stabilizer G x₀
abbrev Space := CoinducedLinearCharacter.Space (Stabilizer G X x₀) (1 : Stabilizer G X x₀ →* kˣ)

def fromFunctions : (X → k) →ₗ[k] Space k G X x₀ where
  toFun f := ⟨fun g => f (g⁻¹ • x₀), by
    intro b g
    have hb : (b : G)⁻¹ • x₀ = x₀ :=
      MulAction.mem_stabilizer_iff.mp ((Stabilizer G X x₀).inv_mem b.property)
    change f (((b : G) * g)⁻¹ • x₀) = (1 : k) * f (g⁻¹ • x₀)
    rw [mul_inv_rev, mul_smul, hb, one_mul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem fromFunctions_apply (f : X → k) (g : G) :
    (fromFunctions k G X x₀ f).val g = f (g⁻¹ • x₀) := rfl

variable (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)

include htrans in
theorem fromFunctions_injective : Function.Injective (fromFunctions k G X x₀) := by
  intro f h he
  funext x
  obtain ⟨g, hg⟩ := htrans x
  have hv := congrArg (fun v : Space k G X x₀ => v.val g⁻¹) he
  simpa only [fromFunctions_apply, inv_inv, hg] using hv

include htrans in
theorem fromFunctions_surjective : Function.Surjective (fromFunctions k G X x₀) := by
  classical
  choose s hs using htrans
  intro v
  refine ⟨fun x => v.val (s x)⁻¹, ?_⟩
  apply Subtype.ext
  funext g
  let x := g⁻¹ • x₀
  let b : Stabilizer G X x₀ := ⟨(s x)⁻¹ * g⁻¹, by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    change (s x)⁻¹ • x = x₀
    simpa only [inv_smul_smul] using
      (congrArg (fun y : X => (s x)⁻¹ • y) (hs x)).symm⟩
  have he := v.property b g
  change v.val (((s x)⁻¹ * g⁻¹) * g) = (1 : k) * v.val g at he
  change v.val (s x)⁻¹ = v.val g
  simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using he

def linearEquiv : (X → k) ≃ₗ[k] Space k G X x₀ :=
  LinearEquiv.ofBijective (fromFunctions k G X x₀)
    ⟨fromFunctions_injective k G X x₀ htrans, fromFunctions_surjective k G X x₀ htrans⟩

theorem fromFunctions_action (g : G) (f : X → k) :
    fromFunctions k G X x₀ (FinitePermutationAugmentation.representation k G X g f) =
      CoinducedLinearCharacter.induced (Stabilizer G X x₀) (1 : Stabilizer G X x₀ →* kˣ)
        g (fromFunctions k G X x₀ f) := by
  apply Subtype.ext
  funext h
  change f (g⁻¹ • (h⁻¹ • x₀)) = f ((h * g)⁻¹ • x₀)
  rw [mul_inv_rev, mul_smul]

def equiv : (FinitePermutationAugmentation.representation k G X).Equiv
    (CoinducedLinearCharacter.induced (Stabilizer G X x₀) (1 : Stabilizer G X x₀ →* kˣ)) :=
  Representation.Equiv.mk (linearEquiv k G X x₀ htrans) (by
    intro g
    apply LinearMap.ext
    intro f
    exact fromFunctions_action k G X x₀ g f)

@[simp] theorem equiv_apply (f : X → k) (g : G) :
    (equiv k G X x₀ htrans f).val g = f (g⁻¹ • x₀) := rfl

end Kourovka2135.StabilizerCoinduction
