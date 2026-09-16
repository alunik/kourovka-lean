import Kourovka.Problems.P21_38.Proof.StandardGenerators
import Mathlib.GroupTheory.IsPerfect

/-!
# The compact core is the perfect derived subgroup

The standard-generator calculation identifies the endpoint kernel with the
derived subgroup in the concrete interval group. Transporting along its
inclusion into rational permutations identifies the ambient compact core.
The imported comparison of the two commutator subgroups then proves that this
core is perfect.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- The image of the endpoint kernel in rational permutations is the compact core. -/
theorem map_endpointCharacter_ker :
    endpointCharacter.ker.map (compactF 0 1).subtype = compactCore 0 := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_endpointCharacter_ker_iff g).mp hg
  · intro hf
    refine ⟨⟨f, compactCore_le hf⟩, ?_, rfl⟩
    exact (mem_endpointCharacter_ker_iff _).mpr hf

/-- The compact core is the derived subgroup of the interval group,
viewed in the ambient permutation group. -/
theorem compactCore_eq_ambient_commutator :
    compactCore 0 = ⁅compactF 0 1, compactF 0 1⁆ := by
  rw [← map_endpointCharacter_ker, endpointCharacter_ker_eq_commutator]
  exact (compactF 0 1).map_subtype_commutator

/-- The dyadic compact core equals its own commutator subgroup. -/
theorem compactCore_commutator_eq : ⁅compactCore 0, compactCore 0⁆ = compactCore 0 :=
  (commutator_compactF_eq (m := 0)).symm.trans compactCore_eq_ambient_commutator.symm

theorem compactCore_isPerfect : Group.IsPerfect (compactCore 0) :=
  Subgroup.isPerfect_iff.mpr compactCore_commutator_eq

/-- The already proved simplicity of the core's commutator now applies to the
core itself, because its perfectness has been established. -/
theorem compactCore_isSimpleGroup : IsSimpleGroup (compactCore 0) := by
  have h := isSimpleGroup_commutator_compactCore (m := 0)
  rw [compactCore_commutator_eq] at h
  exact h

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.compactCore_eq_ambient_commutator
#audit_axioms Kourovka.P21_38.compactCore_isPerfect
#audit_axioms Kourovka.P21_38.compactCore_isSimpleGroup
