import Kourovka2135.ScalarWeightAdditiveMaps
import Mathlib.Algebra.CharP.Two

/-! Additive maps on a group with the actual Tits root multiplication law.
The second coordinate is killed because every such element is a square.
No commutator-subgroup identification or abelianization theorem is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.TitsRootAdditiveMaps

variable {F k H : Type*} [Field F] [CharP F 2] [Field k] [CharP k 2] [Group H]
variable (θ : F ≃+* F) (hθ : ∀ x, θ (θ x) = x ^ 2)
variable (u : F → F → H)
variable (hmul : ∀ a b c d, u a b * u c d = u (a + c) (b + d + a * θ c))

include hmul in
omit [CharP F 2] in
/-- The root coordinate identity is forced by the multiplication law. -/
theorem root_zero : u 0 0 = 1 := by
  have h : u 0 0 * u 0 0 = u 0 0 := by simpa using hmul 0 0 0 0
  exact mul_left_cancel (h.trans (mul_one (u 0 0)).symm)

include hθ hmul in
/-- Every element of the second root coordinate is a square. -/
theorem second_coordinate_square (b : F) : ∃ a, u a 0 * u a 0 = u 0 b := by
  obtain ⟨a, ha⟩ := ScalarWeightAdditiveMaps.titsNorm_surjective θ hθ b
  refine ⟨a, ?_⟩
  rw [hmul]
  simp [CharTwo.add_self_eq_zero, ha]

include hθ hmul in
/-- Any map to an additive characteristic-two group kills the second coordinate. -/
theorem map_second_eq_zero (f : Additive H →+ k) (b : F) :
    f (Additive.ofMul (u 0 b)) = 0 := by
  obtain ⟨a, ha⟩ := second_coordinate_square θ hθ u hmul b
  rw [← ha]
  change f (Additive.ofMul (u a 0) + Additive.ofMul (u a 0)) = 0
  rw [map_add, CharTwo.add_self_eq_zero]

include hθ hmul in
/-- The image of a root element depends only on its first coordinate. -/
theorem map_root_eq_first (f : Additive H →+ k) (a b : F) :
    f (Additive.ofMul (u a b)) = f (Additive.ofMul (u a 0)) := by
  have h : u a 0 * u 0 b = u a b := by simpa using hmul a 0 0 b
  rw [← h]
  change f (Additive.ofMul (u a 0) + Additive.ofMul (u 0 b)) = _
  rw [map_add, map_second_eq_zero θ hθ u hmul, add_zero]

/-- The actual factor map on the first root coordinate. -/
def firstCoordinate (f : Additive H →+ k) : F →+ k where
  toFun a := f (Additive.ofMul (u a 0))
  map_zero' := by
    rw [root_zero θ u hmul]
    exact map_zero f
  map_add' a c := by
    have h := congrArg (fun x : H => f (Additive.ofMul x)) (hmul a 0 c 0)
    change f (Additive.ofMul (u a 0) + Additive.ofMul (u c 0)) =
      f (Additive.ofMul (u (a + c) (0 + 0 + a * θ c))) at h
    simpa only [map_add, map_root_eq_first θ hθ u hmul] using h.symm

/-- Linear restriction to the first coordinate. -/
def firstCoordinateLinear : (Additive H →+ k) →ₗ[k] (F →+ k) where
  toFun := firstCoordinate θ hθ u hmul
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl

/-- Actual exhaustive root coordinates make the factor map injective. -/
theorem firstCoordinateLinear_injective
    (hcover : ∀ x : H, ∃ a b, x = u a b) :
    Function.Injective (firstCoordinateLinear (k := k) θ hθ u hmul) := by
  intro f g h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, b, hx⟩ := hcover x.toMul
  have he := congrArg (fun j : F →+ k => j a) h
  change f (Additive.ofMul (u a 0)) = g (Additive.ofMul (u a 0)) at he
  change f (Additive.ofMul x.toMul) = g (Additive.ofMul x.toMul)
  rw [hx]
  simpa only [map_root_eq_first θ hθ u hmul] using he

/-- Forward torus conjugation gives the forward multiplicative weight on
first-coordinate additive maps. The orientation matches the actual root formula. -/
theorem firstCoordinate_mem_weightSpace
    (χ : Fˣ →* kˣ) (α : Fˣ → MulAut H)
    (hconj : ∀ s a b, α s (u a b) =
      u ((s : F) * a) ((s : F) * θ (s : F) * b))
    (f : Additive H →+ k)
    (hf : ∀ s x, f (Additive.ofMul (α s x)) =
      (χ s : k) * f (Additive.ofMul x)) :
    firstCoordinate θ hθ u hmul f ∈ ScalarWeightAdditiveMaps.weightSpace χ := by
  intro s a
  have h := hf s (u a 0)
  rw [hconj] at h
  simpa [firstCoordinate] using h

end Kourovka2135.TitsRootAdditiveMaps
