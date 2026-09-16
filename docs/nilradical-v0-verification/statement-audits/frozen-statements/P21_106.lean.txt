import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.ModelTheory.Semantics

/-!
# Problem 21.106

Conte and Petschick ask whether every parameter-free first-order formula with
one free variable is concise in residually finite groups. Conciseness means
that a finite set of values generates a finite subgroup. The question first
appeared as Question 1 of *Conciseness of first-order formulae* (2025), and was
subsequently included in the Kourovka Notebook as Problem 21.106.

The language below has precisely the usual group operations and no parameters.
Formulas and their interpretations use mathlib's first-order syntax and semantics.
-/

namespace Kourovka.P21_106

/-- The function symbols of the ordinary group language, indexed by arity. -/
inductive GroupFunction : ℕ → Type
  | one : GroupFunction 0
  | inv : GroupFunction 1
  | mul : GroupFunction 2

/-- The ordinary language of groups, with equality and no additional relations. -/
def groupLanguage : FirstOrder.Language :=
  ⟨GroupFunction, fun _ => Empty⟩

/-- Interpret the group language by the given group operations. -/
instance groupLanguageStructure (G : Type*) [Group G] : groupLanguage.Structure G where
  funMap := fun f v => match f with
    | GroupFunction.one => 1
    | GroupFunction.inv => (v 0)⁻¹
    | GroupFunction.mul => v 0 * v 1
  RelMap := fun r => nomatch r

/-- Values of a parameter-free group formula with its sole free variable assigned `x`. -/
def FormulaValues (φ : groupLanguage.Formula Unit) (G : Type*) [Group G] : Set G :=
  {x | φ.Realize (fun _ => x)}

/-- A formula is concise in a group if finite values generate a finite subgroup. -/
def IsConciseIn (φ : groupLanguage.Formula Unit) (G : Type*) [Group G] : Prop :=
  (FormulaValues φ G).Finite → Finite (Subgroup.closure (FormulaValues φ G))

/-- The full question in Kourovka Notebook Problem 21.106. -/
def NotebookStatement : Prop :=
  ∀ (G : Type) [Group G] [Group.ResiduallyFinite G]
    (φ : groupLanguage.Formula Unit), IsConciseIn φ G

end Kourovka.P21_106
