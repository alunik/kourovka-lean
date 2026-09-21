import Kourovka2135.FinitePermutationAugmentation
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.RepresentationTheory.Intertwining

/-! Normalized cocycles are precisely equivariant maps from the actual
augmentation module of a transitive finite permutation action. The explicit
inverse sums cocycle values against coefficients. This construction uses no
semisimplicity, irreducibility, or group-cohomology classification. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PermutationAugmentationCocycles
open groupCohomology FinitePermutationAugmentation NormalizedCocycleSubspace

variable {k G X V : Type u} [Field k] [Group G] [Fintype X] [MulAction G X]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (x₀ : X)

abbrev Normalized := normalized ρ (MulAction.stabilizer G x₀)
abbrev Maps := Representation.IntertwiningMap (action k G X) ρ

/-- Compose an equivariant map with the actual delta-difference cocycle. -/
def fromHom : Maps (X := X) ρ →ₗ[k] Normalized ρ x₀ where
  toFun f := ⟨⟨fun g => f (difference k X x₀ (g • x₀)),
    (mem_cocycles₁_iff _).mpr (by
      intro g h
      have he := (mem_cocycles₁_iff (canonicalCocycle k G X x₀)).mp
        (canonicalCocycle k G X x₀).property g h
      change difference k X x₀ ((g * h) • x₀) =
        action k G X g (difference k X x₀ (h • x₀)) +
          difference k X x₀ (g • x₀) at he
      rw [he, map_add, f.isIntertwining])⟩, by
    intro b
    change f (difference k X x₀ ((b : G) • x₀)) = 0
    rw [b.property, difference_self, map_zero]⟩
  map_add' f h := by
    apply Subtype.ext
    apply cocycles₁_ext
    intro g
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply cocycles₁_ext
    intro g
    rfl

@[simp] theorem fromHom_apply (f : Maps (X := X) ρ) (g : G) :
    (fromHom ρ x₀ f).val g = f (difference k X x₀ (g • x₀)) := rfl

theorem sum_smul_delta (f : X → k) : ∑ x, f x • delta k X x = f := by
  classical
  simpa only [delta, ← Pi.single_smul, smul_eq_mul, mul_one] using
    (Finset.univ_sum_single f)

theorem sum_smul_difference (f : Space k X) :
    ∑ x, (f : X → k) x • difference k X x₀ x = f := by
  apply Subtype.ext
  change (Space k X).subtype (∑ x, (f : X → k) x • difference k X x₀ x) = (f : X → k)
  rw [map_sum]
  simp only [map_smul]
  change ∑ x, (f : X → k) x • (delta k X x - delta k X x₀) = (f : X → k)
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sum_smul_delta, ← Finset.sum_smul]
  have hf : ∑ x, (f : X → k) x = 0 := f.property
  rw [hf, zero_smul, sub_zero]

variable (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)

include htrans in
theorem fromHom_injective : Function.Injective (fromHom ρ x₀) := by
  intro f h he
  have hd : ∀ x : X, f (difference k X x₀ x) = h (difference k X x₀ x) := by
    intro x
    obtain ⟨g, rfl⟩ := htrans x
    exact congrArg (fun z : Normalized ρ x₀ => z.val g) he
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  rw [← sum_smul_difference x₀ a, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, map_smul]
  exact congrArg (fun v : V => (a : X → k) x • v) (hd x)

def representative (x : X) : G := Classical.choose (htrans x)

omit [Fintype X] in
theorem representative_smul (x : X) : representative x₀ htrans x • x₀ = x :=
  Classical.choose_spec (htrans x)

omit [Fintype X] in
theorem cocycle_eq_of_same_point (z : Normalized ρ x₀) (g h : G)
    (he : g • x₀ = h • x₀) : z.val g = z.val h := by
  have hm : h⁻¹ * g ∈ MulAction.stabilizer G x₀ := by
    change (h⁻¹ * g) • x₀ = x₀
    rw [mul_smul, he, inv_smul_smul]
  have hc := (mem_cocycles₁_iff z.val).mp z.val.property h (h⁻¹ * g)
  rw [mul_inv_cancel_left, z.property ⟨_, hm⟩, map_zero, zero_add] at hc
  exact hc

def value (z : Normalized ρ x₀) (x : X) : V := z.val (representative x₀ htrans x)

omit [Fintype X] in
theorem value_orbit (z : Normalized ρ x₀) (g : G) :
    value ρ x₀ htrans z (g • x₀) = z.val g :=
  cocycle_eq_of_same_point ρ x₀ z _ g (representative_smul x₀ htrans _)

omit [Fintype X] in
theorem value_base (z : Normalized ρ x₀) : value ρ x₀ htrans z x₀ = 0 := by
  have he := value_orbit ρ x₀ htrans z (1 : G)
  simpa only [one_smul, cocycles₁_map_one] using he

omit [Fintype X] in
theorem value_action (z : Normalized ρ x₀) (g : G) (x : X) :
    value ρ x₀ htrans z (g • x) = ρ g (value ρ x₀ htrans z x) + z.val g := by
  rw [← representative_smul x₀ htrans x, ← mul_smul, value_orbit, value_orbit]
  exact (mem_cocycles₁_iff z.val).mp z.val.property _ _

def extension (z : Normalized ρ x₀) : (X → k) →ₗ[k] V :=
  Fintype.linearCombination k (value ρ x₀ htrans z)

theorem extension_delta (z : Normalized ρ x₀) (x : X) :
    extension ρ x₀ htrans z (delta k X x) = value ρ x₀ htrans z x := by
  classical
  simp [extension, delta]

theorem extension_action (z : Normalized ρ x₀) (g : G) (f : X → k) :
    extension ρ x₀ htrans z (representation k G X g f) =
      ρ g (extension ρ x₀ htrans z f) + augmentation k X f • z.val g := by
  change (∑ x, f (g⁻¹ • x) • value ρ x₀ htrans z x) =
    ρ g (∑ x, f x • value ρ x₀ htrans z x) + (∑ x, f x) • z.val g
  calc
    _ = ∑ x, f x • value ρ x₀ htrans z (g • x) := by
      simpa only [inv_smul_smul] using
        ((MulAction.bijective g).sum_comp
          (fun x => f (g⁻¹ • x) • value ρ x₀ htrans z x)).symm
    _ = _ := by
      simp_rw [value_action, smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact (map_smul (ρ g) (f x) (value ρ x₀ htrans z x)).symm

def toHom (z : Normalized ρ x₀) : Maps (X := X) ρ :=
  ((extension ρ x₀ htrans z).comp (Space k X).subtype).intertwiningMap_of_isIntertwiningMap
    (action k G X) ρ (by
      intro g f
      change extension ρ x₀ htrans z (representation k G X g f) =
        ρ g (extension ρ x₀ htrans z f)
      rw [extension_action, show augmentation k X f = 0 from f.property, zero_smul, add_zero])

theorem fromHom_toHom (z : Normalized ρ x₀) :
    fromHom ρ x₀ (toHom ρ x₀ htrans z) = z := by
  apply Subtype.ext
  apply cocycles₁_ext
  intro g
  change extension ρ x₀ htrans z (delta k X (g • x₀) - delta k X x₀) = z.val g
  rw [map_sub, extension_delta, extension_delta, value_orbit, value_base, sub_zero]

include htrans in
theorem fromHom_surjective : Function.Surjective (fromHom ρ x₀) :=
  fun z => ⟨toHom ρ x₀ htrans z, fromHom_toHom ρ x₀ htrans z⟩

def normalizedEquiv : Normalized ρ x₀ ≃ₗ[k] Maps (X := X) ρ :=
  (LinearEquiv.ofBijective (fromHom ρ x₀)
    ⟨fromHom_injective ρ x₀ htrans, fromHom_surjective ρ x₀ htrans⟩).symm

end Kourovka2135.PermutationAugmentationCocycles
