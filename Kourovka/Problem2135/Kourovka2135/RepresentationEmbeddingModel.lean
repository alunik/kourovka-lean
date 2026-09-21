import Kourovka2135.GroupCohomologyFieldExtension
import Kourovka2135.RepresentationBaseChangeMovingRank
import Mathlib.RepresentationTheory.Character

/-! Actual models over a splitting field, indexed by coefficient embeddings.
Varying the field embedding constructs Frobenius-conjugate models directly
by scalar extension. Cohomology and moving-rank comparisons are inherited
from the proved actual base-change maps; no semilinear classification is used. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationEmbeddingModel
open scoped TensorProduct
open RepresentationDensityBaseChange

variable {E L G V : Type u} [Field E] [Field L] [Group G]
variable [AddCommGroup V] [Module E V]

/-- The tensor-product carrier uses the specified coefficient embedding. -/
abbrev Carrier (σ : E →+* L) : Type u :=
  letI : Algebra E L := σ.toAlgebra
  L ⊗[E] V

instance carrierAddCommGroup (σ : E →+* L) : AddCommGroup (Carrier (V := V) σ) :=
  letI : Algebra E L := σ.toAlgebra
  inferInstanceAs (AddCommGroup (L ⊗[E] V))

instance carrierModule (σ : E →+* L) : Module L (Carrier (V := V) σ) :=
  letI : Algebra E L := σ.toAlgebra
  inferInstanceAs (Module L (L ⊗[E] V))

/-- The whole group action is the actual scalar-extended action. -/
abbrev model (σ : E →+* L) (ρ : Representation E G V) :
    Representation L G (Carrier (V := V) σ) :=
  letI : Algebra E L := σ.toAlgebra
  baseChange L ρ

variable [FiniteDimensional E V]

instance carrierFiniteDimensional (σ : E →+* L) :
    FiniteDimensional L (Carrier (V := V) σ) := by
  let : Algebra E L := σ.toAlgebra
  exact inferInstanceAs (FiniteDimensional L (L ⊗[E] V))

theorem finrank_carrier (σ : E →+* L) :
    Module.finrank L (Carrier (V := V) σ) = Module.finrank E V := by
  let : Algebra E L := σ.toAlgebra
  exact Module.finrank_baseChange

theorem isIrreducible [Nontrivial V] (σ : E →+* L) (ρ : Representation E G V)
    (hfull : Function.Surjective ρ.asAlgebraHom) : (model σ ρ).IsIrreducible := by
  let : Algebra E L := σ.toAlgebra
  exact RepresentationDensityBaseChange.baseChange_isIrreducible L ρ hfull

/-- Ordinary character values are mapped by exactly the chosen embedding. -/
theorem character (σ : E →+* L) (ρ : Representation E G V) (g : G) :
    (model σ ρ).character g = σ (ρ.character g) := by
  let : Algebra E L := σ.toAlgebra
  change LinearMap.trace L (L ⊗[E] V) ((ρ g).baseChange L) = _
  rw [LinearMap.trace_baseChange]
  rfl

/-- A single unequal trace value separates two embedding-indexed models. -/
theorem not_equiv_of_character_ne (σ τ : E →+* L) (ρ : Representation E G V)
    (g : G) (hne : σ (ρ.character g) ≠ τ (ρ.character g)) :
    ¬ Nonempty ((model σ ρ).Equiv (model τ ρ)) := by
  rintro ⟨e⟩
  have he := congrFun (Representation.char_iso e) g
  rw [character, character] at he
  exact hne he

theorem finrank_moving (σ : E →+* L) (ρ : Representation E G V) (g : G) :
    Module.finrank L (LinearMap.range (model σ ρ g - LinearMap.id)) =
      Module.finrank E (LinearMap.range (ρ g - LinearMap.id)) := by
  let : Algebra E L := σ.toAlgebra
  exact RepresentationBaseChangeMovingRank.finrank_moving_baseChange ρ g

variable [Finite G]

/-- Ordinary positive-degree cohomology is unchanged in dimension under each embedding. -/
theorem finrank_cohomology (σ : E →+* L) (ρ : Representation E G V) (n : ℕ) :
    Module.finrank L (groupCohomology (Rep.of (model σ ρ)) (n + 1)) =
      Module.finrank E (groupCohomology (Rep.of ρ) (n + 1)) := by
  let : Algebra E L := σ.toAlgebra
  exact GroupCohomologyFieldExtension.finrank_groupCohomology_baseChange ρ n

end Kourovka2135.RepresentationEmbeddingModel
