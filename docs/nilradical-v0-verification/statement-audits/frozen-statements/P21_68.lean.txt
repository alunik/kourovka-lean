import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Analysis.Complex.Basic
import Kourovka.External.TauCeti.RepresentationTheory.Induction.FiniteDimensional
import Kourovka.External.TauCeti.RepresentationTheory.LinearCharacter

/-!
# Problem 21.68

M. Kida asks whether every finite semiabelian group is monomial. Semiabelian
means the subgroup-chain definition in the Kourovka Notebook and Definition
2.1 of *On semiabelian groups* (2025). Monomiality is expressed in its standard
representation form: every irreducible complex representation is induced
from a one-dimensional character of a subgroup.
-/

open CategoryTheory

namespace Kourovka.P21_68

/-- An abelian semidirect product with the preceding group maps onto
the next group. The source definition only asks for an abstract quotient. -/
def IsSemiabelianStep (H K : Type) [Group H] [Group K] : Prop :=
  ∃ (A : Type) (_ : CommGroup A)
    (α : H →* MulAut A) (f : A ⋊[α] H →* K), Function.Surjective f

/-- The actual subgroup-chain definition of semiabelianity. -/
def IsSemiabelian (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (C : ℕ → Subgroup G),
    C 0 = ⊥ ∧ C n = ⊤ ∧ Monotone C ∧
    ∀ i < n, IsSemiabelianStep (C i) (C (i + 1))

/-- A representation induced from a linear character of a subgroup. -/
def IsMonomialRepresentation {G : Type} [Group G] [Finite G]
    (V : FDRep ℂ G) : Prop :=
  ∃ (L : Subgroup G) (θ : L →* ℂˣ),
    Nonempty (V ≅ TauCeti.indFDRep (FDRep.ofLinearCharacter θ))

/-- Every irreducible complex representation of the finite group is monomial. -/
def IsMonomial (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V : FDRep ℂ G, Simple V → IsMonomialRepresentation V

/-- Kida's conjecture, Kourovka Notebook problem 21.68. -/
def NotebookStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSemiabelian G → IsMonomial G

end Kourovka.P21_68
