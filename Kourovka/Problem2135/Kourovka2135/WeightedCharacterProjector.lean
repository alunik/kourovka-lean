import Kourovka2135.CoprimeInvariantLifting

/-! Weighted averaging onto a one-dimensional character space. The operator
is also the action of one explicit group-algebra element, so every actual
intertwiner commutes with it. Only the subgroup order is averaged. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.WeightedCharacterProjector
open scoped MonoidAlgebra

variable {k U V : Type u} [Field k] [Group U]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k U V) (χ : U →* kˣ)

/-- Twist the coefficient action by the inverse character. -/
def twist : Representation k U V where
  toFun g := (((χ g)⁻¹ : kˣ) : k) • ρ g
  map_one' := by
    apply LinearMap.ext
    intro v
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul, smul_smul]

variable [Fintype U]

def projector : V →ₗ[k] V := CoprimeInvariantLifting.average (twist ρ χ)

theorem projector_apply (v : V) :
    projector ρ χ v = (Fintype.card U : k)⁻¹ •
      ∑ g : U, (((χ g)⁻¹ : kˣ) : k) • ρ g v := by
  exact CoprimeInvariantLifting.average_apply (twist ρ χ) v

/-- Every vector in the operator range has the specified character. -/
theorem action_projector (g : U) (v : V) :
    ρ g (projector ρ χ v) = (χ g : k) • projector ρ χ v := by
  have he := CoprimeInvariantLifting.average_mem_invariants (twist ρ χ) v g
  change (((χ g)⁻¹ : kˣ) : k) • ρ g (projector ρ χ v) = projector ρ χ v at he
  have hs := congrArg (fun w : V => (χ g : k) • w) he
  simpa only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] using hs

/-- On its character space, the averaging operator is the identity. -/
theorem projector_eq_self (hcard : (Fintype.card U : k) ≠ 0) (v : V)
    (hv : ∀ g : U, ρ g v = (χ g : k) • v) : projector ρ χ v = v := by
  apply CoprimeInvariantLifting.average_eq_self (twist ρ χ) hcard
  intro g
  change (((χ g)⁻¹ : kˣ) : k) • ρ g v = v
  rw [hv g, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem projector_ne_zero (hcard : (Fintype.card U : k) ≠ 0) (v : V) (hv : v ≠ 0)
    (heigen : ∀ g : U, ρ g v = (χ g : k) • v) : projector ρ χ ≠ 0 := by
  intro hzero
  have he := projector_eq_self ρ χ hcard v heigen
  rw [hzero, LinearMap.zero_apply] at he
  exact hv he.symm

variable {G : Type u} [Group G]

/-- The same coefficient element acts in every representation of the ambient group. -/
def element (φ : U →* G) : k[G] :=
  (Fintype.card U : k)⁻¹ • ∑ g : U, MonoidAlgebra.single (φ g) (((χ g)⁻¹ : kˣ) : k)

theorem asAlgebraHom_element (σ : Representation k G V) (φ : U →* G) :
    σ.asAlgebraHom (element χ φ) = projector (σ.comp φ) χ := by
  apply LinearMap.ext
  intro v
  simp only [element, map_smul, map_sum, Representation.asAlgebraHom_single,
    LinearMap.smul_apply, LinearMap.sum_apply, projector_apply]
  rfl

end Kourovka2135.WeightedCharacterProjector
