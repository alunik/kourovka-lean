import Kourovka2135.FinitePermutationAugmentation
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual orbit map from a finite permutation representation to a
representation with a stabilizer-fixed vector. Its augmentation restriction
is an isomorphism when the augmentation is irreducible, the dimensions agree,
and the orbit is nonconstant. No character comparison is used. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.FinitePermutationOrbitMap

open FinitePermutationAugmentation

variable {k G X V : Type u} [Field k] [Group G] [MulAction G X]
variable [AddCommGroup V] [Module k V] (ρ : Representation k G V)

section Descent
variable (x₀ : X) (v : V)
variable (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)
variable (hfix : ∀ g : G, g • x₀ = x₀ → ρ g v = v)
include hfix

theorem equal_orbit_values (g h : G) (he : g • x₀ = h • x₀) : ρ g v = ρ h v := by
  have hs : (h⁻¹ * g) • x₀ = x₀ := by
    rw [mul_smul, he, inv_smul_smul]
  calc
    ρ g v = ρ h (ρ (h⁻¹ * g) v) := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    _ = ρ h v := congrArg (ρ h) (hfix _ hs)

def orbitFunction (x : X) : V := ρ (htrans x).choose v

theorem orbitFunction_orbit (g : G) :
    orbitFunction ρ x₀ v htrans (g • x₀) = ρ g v :=
  equal_orbit_values ρ x₀ v hfix _ g (htrans (g • x₀)).choose_spec

theorem orbitFunction_base : orbitFunction ρ x₀ v htrans x₀ = v := by
  simpa using orbitFunction_orbit ρ x₀ v htrans hfix 1

theorem orbitFunction_equivariant (g : G) (x : X) :
    orbitFunction ρ x₀ v htrans (g • x) = ρ g (orbitFunction ρ x₀ v htrans x) := by
  obtain ⟨h, rfl⟩ := htrans x
  rw [← mul_smul, orbitFunction_orbit ρ x₀ v htrans hfix,
    orbitFunction_orbit ρ x₀ v htrans hfix, map_mul]
  rfl
end Descent

section LinearExtension
variable [Fintype X]
variable (φ : X → V) (hφ : ∀ g : G, ∀ x : X, φ (g • x) = ρ g (φ x))
include hφ

def linearExtension : (X → k) →ₗ[k] V where
  toFun f := ∑ x, f x • φ x
  map_add' f h := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [mul_smul, Finset.smul_sum]

theorem linearExtension_equivariant (g : G) (f : X → k) :
    linearExtension φ (representation k G X g f) = ρ g (linearExtension φ f) := by
  change (∑ x, f (g⁻¹ • x) • φ x) = ρ g (∑ x, f x • φ x)
  calc
    _ = ∑ x, f x • φ (g • x) := by
      simpa only [inv_smul_smul] using
        ((MulAction.bijective g).sum_comp (fun x => f (g⁻¹ • x) • φ x)).symm
    _ = _ := by simp only [hφ, map_sum, map_smul]

def orbitMap : (representation k G X).IntertwiningMap ρ where
  toLinearMap := linearExtension φ
  isIntertwining' g := by
    ext f
    exact linearExtension_equivariant ρ φ hφ g f

@[simp] theorem orbitMap_delta (x : X) : orbitMap ρ φ hφ (delta k X x) = φ x := by
  classical
  simp [orbitMap, linearExtension, delta]

def augmentationMap : (action k G X).IntertwiningMap ρ where
  toLinearMap := (linearExtension φ).comp (Space k X).subtype
  isIntertwining' g := by
    ext f
    exact linearExtension_equivariant ρ φ hφ g f.val

@[simp] theorem augmentationMap_difference (x y : X) :
    augmentationMap ρ φ hφ (difference k X x y) = φ y - φ x := by
  change orbitMap ρ φ hφ (delta k X y - delta k X x) = _
  rw [map_sub, orbitMap_delta, orbitMap_delta]

theorem augmentationMap_ne_zero (x y : X) (hxy : φ y ≠ φ x) :
    augmentationMap ρ φ hφ ≠ 0 := by
  intro hz
  have he := congrArg (fun f : (action k G X).IntertwiningMap ρ =>
    f (difference k X x y)) hz
  rw [augmentationMap_difference] at he
  exact hxy (sub_eq_zero.mp he)

theorem augmentationMap_injective [(action k G X).IsIrreducible]
    (x y : X) (hxy : φ y ≠ φ x) : Function.Injective (augmentationMap ρ φ hφ) :=
  (Representation.IsIrreducible.injective_or_eq_zero (augmentationMap ρ φ hφ)).resolve_right
    (augmentationMap_ne_zero ρ φ hφ x y hxy)

def augmentationEquiv [(action k G X).IsIrreducible] [Module.Finite k V]
    (hdim : Module.finrank k (Space k X) = Module.finrank k V)
    (x y : X) (hxy : φ y ≠ φ x) : (action k G X).Equiv ρ :=
  (augmentationMap ρ φ hφ).ofBijective
    ⟨augmentationMap_injective ρ φ hφ x y hxy,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (augmentationMap_injective ρ φ hφ x y hxy)⟩
end LinearExtension

end Kourovka2135.FinitePermutationOrbitMap
