import Kourovka.Problems.P21_68.Statement
import Kourovka.Problems.P21_68.Proof.InertiaRep
import Kourovka.Problems.P21_68.Proof.ScalarInduction
import Kourovka.Problems.P21_68.Proof.NonmonomialInduction

/-!
# A negative answer to Kourovka problem 21.68

The semiabelian group `G` has order 2592. Its explicitly constructed
degree-eight irreducible complex representation cannot be induced from a
linear character of any subgroup.
-/

open CategoryTheory

namespace Kourovka.P21_68

noncomputable def witnessRepresentation : FDRep ℂ G := TauCeti.indFDRep inertiaRep

private theorem inertia_scalar (n : N) (v : inertiaRep) :
    inertiaRep.ρ (Subgroup.inclusion N_le_I n) v = (nWeight n : ℂ) • v := by
  rw [inertiaRep_N]
  rfl

/-- The counterexample representation is irreducible. -/
instance simple_witnessRepresentation : Simple witnessRepresentation :=
  simple_ind_of_scalar N I N_le_I nWeight inertiaRep inertia_scalar nWeight_inertia

/-- Its degree is eight. -/
theorem finrank_witnessRepresentation : Module.finrank ℂ witnessRepresentation = 8 := by
  rw [witnessRepresentation, TauCeti.finrank_indFDRep, finrank_inertiaRep, I_index]

/-- The representation cannot be induced from a linear character of a subgroup. -/
theorem witness_not_monomial : ¬ IsMonomialRepresentation witnessRepresentation := by
  apply not_isMonomial_ind_of_scalar N I N_le_I nWeight inertiaRep finrank_inertiaRep
    inertia_scalar nWeight_inertia iProjection iProjection_surjective
    (le_of_eq iProjection_ker)
  · rw [card_N, I_index]
    decide +kernel
  · exact Hsub_no_index_two

/-- The constructed finite semiabelian group is not monomial. -/
theorem G_not_monomial : ¬ IsMonomial G := fun h =>
  witness_not_monomial (h witnessRepresentation inferInstance)

/-- Kida's conjecture in Kourovka problem 21.68 is false. -/
theorem not_notebookStatement : ¬ NotebookStatement := fun h =>
  G_not_monomial (h G G_semiabelian)

end Kourovka.P21_68
