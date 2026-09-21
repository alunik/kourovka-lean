import Kourovka2135.NormalizedCocycleSubspace
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The genuine permutation representation and augmentation kernel over an
arbitrary coefficient field. The acted-on set does not carry any field
embedding into the coefficient field, so this also applies across different
characteristics. Delta differences give the canonical normalized cocycle. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.FinitePermutationAugmentation
open groupCohomology

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]

def representation : Representation k G (X → k) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹ • x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext x
    change f ((1 : G)⁻¹ • x) = f x
    simp only [inv_one, one_smul]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

omit [Fintype X] in
@[simp] theorem representation_apply (g : G) (f : X → k) (x : X) :
    representation k G X g f x = f (g⁻¹ • x) := rfl

def augmentation : (X → k) →ₗ[k] k where
  toFun f := ∑ x, f x
  map_add' f h := Finset.sum_add_distrib
  map_smul' c f := by simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

theorem augmentation_action (g : G) (f : X → k) :
    augmentation k X (representation k G X g f) = augmentation k X f :=
  (MulAction.bijective g⁻¹).sum_comp f

def delta (x : X) : X → k := by
  classical
  exact Pi.single x 1

@[simp] theorem augmentation_delta (x : X) : augmentation k X (delta k X x) = 1 := by
  classical
  simp [augmentation, delta]

omit [Fintype X] in
theorem delta_action (g : G) (x : X) :
    representation k G X g (delta k X x) = delta k X (g • x) := by
  classical
  funext y
  by_cases hy : y = g • x
  · subst y
    simp [delta]
  · have hxy : g⁻¹ • y ≠ x := by
      intro he
      apply hy
      simpa only [smul_inv_smul] using congrArg (fun a : X => g • a) he
    simp [delta, hy, hxy]

abbrev Space := LinearMap.ker (augmentation k X)

def action : Representation k G (Space k X) :=
  Representation.subrepresentation (representation k G X) (Space k X) (by
    intro g f hf
    change augmentation k X (representation k G X g f) = 0
    rw [augmentation_action]
    exact hf)

@[simp] theorem action_val (g : G) (f : Space k X) :
    (action k G X g f : X → k) = representation k G X g f := rfl

def difference (x₀ x : X) : Space k X :=
  ⟨delta k X x - delta k X x₀, by
    change augmentation k X (delta k X x - delta k X x₀) = 0
    rw [map_sub, augmentation_delta, augmentation_delta, sub_self]⟩

@[simp] theorem difference_self (x : X) : difference k X x x = 0 := by
  apply Subtype.ext
  exact sub_self _

theorem difference_action (x₀ x : X) (g : G) :
    action k G X g (difference k X x₀ x) =
      difference k X x₀ (g • x) - difference k X x₀ (g • x₀) := by
  apply Subtype.ext
  change representation k G X g (delta k X x - delta k X x₀) =
    (delta k X (g • x) - delta k X x₀) -
      (delta k X (g • x₀) - delta k X x₀)
  rw [map_sub, delta_action, delta_action]
  abel

/-- The delta difference along the base-point orbit is an actual cocycle. -/
def canonicalCocycle (x₀ : X) : cocycles₁ (Rep.of (action k G X)) :=
  ⟨fun g => difference k X x₀ (g • x₀), (mem_cocycles₁_iff _).mpr (by
    intro g h
    rw [difference_action]
    rw [sub_add_cancel, mul_smul])⟩

theorem canonicalCocycle_zero_of_fixed (x₀ : X) (g : G) (hg : g • x₀ = x₀) :
    canonicalCocycle k G X x₀ g = 0 := by
  change difference k X x₀ (g • x₀) = 0
  rw [hg, difference_self]

end Kourovka2135.FinitePermutationAugmentation
