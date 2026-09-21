import Kourovka2135.RepresentationDensityBaseChange
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A finite, explicitly checked spanning family of actual group operators
certifies full matrix-algebra image, hence absolute irreducibility.
Only the finite linear identities are certificate inputs. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationSpanCertificate
open scoped MonoidAlgebra

variable {k G V I : Type*} [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V] [Fintype I]

/-- An explicitly surjective finite operator sum proves full group-algebra image. -/
theorem asAlgebraHom_surjective
    (ρ : Representation k G V) (elements : I → G)
    (hspan : Function.Surjective (Fintype.linearCombination k (ρ ∘ elements))) :
    Function.Surjective ρ.asAlgebraHom := by
  classical
  intro T
  obtain ⟨c, hc⟩ := hspan T
  refine ⟨∑ i, MonoidAlgebra.single (elements i) (c i), ?_⟩
  simpa only [map_sum, Representation.asAlgebraHom_single,
    Fintype.linearCombination_apply, Function.comp_apply] using hc

/-- A right-inverse certificate for the spanning operator suffices. -/
theorem asAlgebraHom_surjective_of_right_inverse
    (ρ : Representation k G V) (elements : I → G)
    (coordinates : Module.End k V →ₗ[k] (I → k))
    (h : (Fintype.linearCombination k (ρ ∘ elements)).comp coordinates = LinearMap.id) :
    Function.Surjective ρ.asAlgebraHom := by
  apply asAlgebraHom_surjective ρ elements
  intro T
  refine ⟨coordinates T, ?_⟩
  exact congrArg (fun A : Module.End k V →ₗ[k] Module.End k V => A T) h

/-- The certified full operator span proves irreducibility over every extension field. -/
theorem baseChange_isIrreducible (L : Type*) [Field L] [Algebra k L]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) (elements : I → G)
    (hspan : Function.Surjective (Fintype.linearCombination k (ρ ∘ elements))) :
    (RepresentationDensityBaseChange.baseChange L ρ).IsIrreducible :=
  RepresentationDensityBaseChange.baseChange_isIrreducible L ρ
    (asAlgebraHom_surjective ρ elements hspan)

end Kourovka2135.RepresentationSpanCertificate
