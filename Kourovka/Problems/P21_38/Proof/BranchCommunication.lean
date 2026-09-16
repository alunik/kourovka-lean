import Kourovka.Problems.P21_38.Proof.BinaryBranches

/-!
# Communicating descendants of binary branches

If a branch interval is equivalent to both of its children, it is equivalent
to every descendant. These statements concern the branch relation of an actual
subgroup of rational permutations; each use of transitivity composes subgroup
elements witnessing the branches.
-/

namespace Kourovka.P21_38.BranchRelated

variable {H : Subgroup (Equiv.Perm ℚ)} {u v w : List Bool}

/-- Equivalence with both children implies equivalence with every descendant. -/
theorem descendant_to_self
    (hzero : BranchRelated H v (v ++ [false]))
    (hone : BranchRelated H v (v ++ [true])) (s : List Bool) :
    BranchRelated H (v ++ s) v := by
  induction s with
  | nil => simpa using refl H v
  | cons b s ih =>
    cases b
    · simpa only [List.append_assoc, List.singleton_append] using
        (hzero.symm.append s).trans ih
    · simpa only [List.append_assoc, List.singleton_append] using
        (hone.symm.append s).trans ih

/-- Descendants of any branch equivalent to `v` are again equivalent to `v`. -/
theorem descendant_to_related (huv : BranchRelated H u v)
    (hzero : BranchRelated H v (v ++ [false]))
    (hone : BranchRelated H v (v ++ [true])) (s : List Bool) :
    BranchRelated H (u ++ s) v :=
  (huv.append s).trans (descendant_to_self hzero hone s)

/-- The descendant conclusion transfers to any other branch equivalent to `v`. -/
theorem descendant_to_common_related
    (huv : BranchRelated H u v) (hwv : BranchRelated H w v)
    (hzero : BranchRelated H v (v ++ [false]))
    (hone : BranchRelated H v (v ++ [true])) (s : List Bool) :
    BranchRelated H (u ++ s) w :=
  (huv.descendant_to_related hzero hone s).trans hwv.symm

/-- Any two descendants of branches equivalent to `v` are equivalent. -/
theorem descendants_related
    (huv : BranchRelated H u v) (hwv : BranchRelated H w v)
    (hzero : BranchRelated H v (v ++ [false]))
    (hone : BranchRelated H v (v ++ [true])) (s t : List Bool) :
    BranchRelated H (u ++ s) (w ++ t) :=
  (huv.descendant_to_related hzero hone s).trans
    (hwv.descendant_to_related hzero hone t).symm

/-- A word extending one of finitely many related leaves is equivalent to `v`. -/
theorem of_extends_related_leaf
    (hzero : BranchRelated H v (v ++ [false]))
    (hone : BranchRelated H v (v ++ [true]))
    (leaves : List (List Bool))
    (hleaves : ∀ leaf ∈ leaves, BranchRelated H leaf v)
    {x : List Bool} (hx : ∃ leaf ∈ leaves, leaf <+: x) :
    BranchRelated H x v := by
  obtain ⟨leaf, hleaf, s, rfl⟩ := hx
  exact (hleaves leaf hleaf).descendant_to_related hzero hone s

end Kourovka.P21_38.BranchRelated
