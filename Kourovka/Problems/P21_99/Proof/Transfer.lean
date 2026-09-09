import Kourovka.Problems.P21_99.Statement
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Transfer a counterexample action to the notebook's permutation-group formulation. -/

namespace Kourovka.P21_99

/-- A finite transitive action with a complete transporter of elements having
exactly one fixed point disproves the notebook assertion. The action need not
be faithful: its image in the symmetric group has the same point action. -/
theorem not_notebookStatement_of_action
    {A : Type*} {Ω : Type} [Group A] [MulAction A Ω]
    [Finite Ω] [MulAction.IsPretransitive A Ω]
    (a b : Ω) (hab : a ≠ b)
    (hbad : ∀ g : A, g • a = b → ∃! x : Ω, g • x = x) :
    ¬ NotebookStatement := by
  let P : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom A Ω).range
  let f : A →* P := (MulAction.toPermHom A Ω).rangeRestrict
  have hf : Function.Surjective f :=
    (MulAction.toPermHom A Ω).rangeRestrict_surjective
  have htrans : MulAction.IsPretransitive P Ω :=
    MulAction.IsPretransitive.of_smul_eq f (fun {_ _} => rfl)
  intro h
  obtain ⟨g, hgab, hnot⟩ := h Ω P inferInstance htrans a b hab
  obtain ⟨k, rfl⟩ := hf g
  change k • a = b at hgab
  change ¬ ∃! x : Ω, k • x = x at hnot
  exact hnot (hbad k hgab)

end Kourovka.P21_99
