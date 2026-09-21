import Kourovka2135.OddExtensionOperatorUniqueness
import Mathlib.RepresentationTheory.Character

/-! Compare actual extensions on different coefficient spaces. An actual
restriction equivalence transports the candidate action to the original space.
Determinant-one uniqueness at one odd-order element then gives equality of the
actual operators after transport, hence equality of ordinary characters.
No assumed character identity or global determinant condition is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationExtensionComparison

universe u v w w'
variable {k : Type u} [Field k] {H : Type v} [Group H]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type w'} [AddCommGroup W] [Module k W]

/-- Transport the actual candidate representation by the specified linear equivalence. -/
def transport (σ : Representation k H W) (e : W ≃ₗ[k] V) : Representation k H V :=
  e.conjRingEquiv.toMonoidHom.comp σ

@[simp] theorem transport_apply (σ : Representation k H W) (e : W ≃ₗ[k] V) (h : H) :
    transport σ e h = e.conj (σ h) := rfl

/-- The supplied restriction equivalence gives equality with the actual reference action. -/
theorem transport_comp_subtype (N : Subgroup H) (ρ : Representation k N V)
    (σ : Representation k H W) (e : Representation.Equiv (σ.comp N.subtype) ρ) :
    (transport σ e.toLinearEquiv).comp N.subtype = ρ := by
  apply MonoidHom.ext
  intro n
  exact e.conj_apply_self n

/-- Actual conjugation of coefficient operators preserves their determinant. -/
theorem transport_det (σ : Representation k H W) (e : W ≃ₗ[k] V) (h : H) :
    LinearMap.det (transport σ e h) = LinearMap.det (σ h) := by
  exact LinearMap.det_conj (σ h) e

/-- Actual transport preserves the ordinary character, by conjugation invariance of trace. -/
theorem transport_character (σ : Representation k H W) (e : W ≃ₗ[k] V) :
    (transport σ e).character = σ.character := by
  funext h
  exact LinearMap.trace_conj' (σ h) e

variable [IsAlgClosed k] [FiniteDimensional k V]
variable (N : Subgroup H) [N.Normal]
variable (ρ : Representation k N V) [ρ.IsIrreducible]
variable (α : Representation k H V) (hα : α.comp N.subtype = ρ)

include hα in
/-- Equality of actual operators after transport at one odd-order element.
Only the two determinants at that element are required to be one. -/
theorem apply_conjugate_eq_of_odd_orderOf
    (σ : Representation k H W) (e : Representation.Equiv (σ.comp N.subtype) ρ)
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (h : H) (hh : Odd (orderOf h))
    (hdetα : LinearMap.det (α h) = 1) (hdetσ : LinearMap.det (σ h) = 1) :
    α h = e.toLinearEquiv.conj (σ h) := by
  have hβ := transport_comp_subtype N ρ σ e
  have hdetβ : LinearMap.det (transport σ e.toLinearEquiv h) = 1 :=
    (transport_det σ e.toLinearEquiv h).trans hdetσ
  exact OddExtensionOperatorUniqueness.apply_eq_of_odd_orderOf
    N ρ α hα (transport σ e.toLinearEquiv) hβ a hdim h hh hdetα hdetβ

include hα in
/-- The actual extension and candidate have the same ordinary character value
at the specified odd-order element, with determinants assumed only there. -/
theorem character_eq_of_odd_orderOf
    (σ : Representation k H W) (e : Representation.Equiv (σ.comp N.subtype) ρ)
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (h : H) (hh : Odd (orderOf h))
    (hdetα : LinearMap.det (α h) = 1) (hdetσ : LinearMap.det (σ h) = 1) :
    α.character h = σ.character h := by
  have heq := apply_conjugate_eq_of_odd_orderOf N ρ α hα σ e a hdim h hh hdetα hdetσ
  change LinearMap.trace k V (α h) = LinearMap.trace k W (σ h)
  rw [heq]
  exact LinearMap.trace_conj' (σ h) e.toLinearEquiv

end Kourovka2135.RepresentationExtensionComparison
