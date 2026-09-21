import Kourovka2135.CentralAutomorphismCoordinate

/-! Canonical p-torsion-center coordinates for the actual central automorphism subgroup.

The target is the actual kernel of the pth-power homomorphism of Z(N), not
an elementary-abelian hypothesis on the whole center. Coordinates lift to
this subgroup and give an injective ZMod p-linear map into the actual Hom space.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CentralAutomorphismTorsion

open scoped IsMulCommutative
open CentralAutomorphismCoordinate (centralSubgroup)

variable (N : Type u) [Group N] (p : ℕ)

/-- The actual p-torsion subgroup of the center. -/
def centerTorsion : Subgroup (Subgroup.center N) :=
  (powMonoidHom (α := Subgroup.center N) p).ker

@[simp] theorem mem_centerTorsion (z : Subgroup.center N) :
    z ∈ centerTorsion N p ↔ z ^ p = 1 := Iff.rfl

/-- The canonical target is elementary abelian without any exponent condition on all of Z(N). -/
instance centerTorsion_isElementaryAbelian : IsElementaryAbelian p (centerTorsion N p) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    apply Subtype.ext
    exact z.property

variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]

/-- Each actual coordinate lands in the actual p-torsion center. -/
def coordinate (a : centralSubgroup N) :
    (N ⧸ Subgroup.center N) →* centerTorsion N p where
  toFun q := ⟨CentralAutomorphismCoordinate.coordinate N a q,
    CentralAutomorphismCoordinate.coordinate_pow_eq_one N p a q⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (CentralAutomorphismCoordinate.coordinate N a)
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (CentralAutomorphismCoordinate.coordinate N a) q r

@[simp] theorem coordinate_coe (a : centralSubgroup N) (q : N ⧸ Subgroup.center N) :
    (coordinate N p a q : Subgroup.center N) =
      CentralAutomorphismCoordinate.coordinate N a q := rfl

variable [Fact p.Prime]

/-- The actual coordinate is additive as a function into the ZMod p-linear Hom space. -/
def additiveLinearCoordinate :
    Additive (centralSubgroup N) →+
      (Additive (N ⧸ Subgroup.center N) →ₗ[ZMod p] Additive (centerTorsion N p)) where
  toFun a := (coordinate N p a.toMul).toAdditive.toZModLinearMap p
  map_zero' := by
    apply LinearMap.ext
    intro q
    change coordinate N p 1 q.toMul = 1
    apply Subtype.ext
    exact congrArg (fun c : (N ⧸ Subgroup.center N) →* Subgroup.center N => c q.toMul)
      (map_one (CentralAutomorphismCoordinate.coordinate N))
  map_add' a b := by
    apply LinearMap.ext
    intro q
    change coordinate N p (a.toMul * b.toMul) q.toMul =
      coordinate N p a.toMul q.toMul * coordinate N p b.toMul q.toMul
    apply Subtype.ext
    exact congrArg (fun c : (N ⧸ Subgroup.center N) →* Subgroup.center N => c q.toMul)
      (map_mul (CentralAutomorphismCoordinate.coordinate N) a.toMul b.toMul)

/-- The canonical injective coordinate is linear for the prime-field module structures. -/
def linearCoordinate :
    Additive (centralSubgroup N) →ₗ[ZMod p]
      (Additive (N ⧸ Subgroup.center N) →ₗ[ZMod p] Additive (centerTorsion N p)) :=
  (additiveLinearCoordinate N p).toZModLinearMap p

@[simp] theorem linearCoordinate_apply (a : Additive (centralSubgroup N))
    (q : Additive (N ⧸ Subgroup.center N)) :
    linearCoordinate N p a q = Additive.ofMul (coordinate N p a.toMul q.toMul) := rfl

/-- Injectivity is inherited from the actual automorphism values, not postulated on a module. -/
theorem linearCoordinate_injective : Function.Injective (linearCoordinate N p) := by
  intro a b h
  change a.toMul = b.toMul
  apply CentralAutomorphismCoordinate.coordinate_injective N
  apply MonoidHom.ext
  intro q
  exact congrArg
    (fun l : Additive (N ⧸ Subgroup.center N) →ₗ[ZMod p] Additive (centerTorsion N p) =>
      (l (Additive.ofMul q)).toMul.val) h

end Kourovka2135.CentralAutomorphismTorsion
