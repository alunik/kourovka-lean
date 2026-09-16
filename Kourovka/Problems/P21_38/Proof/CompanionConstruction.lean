import Kourovka.Problems.P21_38.Proof.CompanionCommunication
import Kourovka.Problems.P21_38.Proof.CompanionPartition
import Kourovka.Problems.P21_38.Proof.FirstMovingBranches

/-!
# The prescribed companion for every nonidentity element

This combines the first moving piece, a finite full binary partition, and
Golan-Polak's positive-exponent companion. The communication conclusion is
about elements of the actual two-generated subgroup.
-/

namespace Kourovka.P21_38

open BinaryWord

def ambientPair (f g : F) : Subgroup (Equiv.Perm ℚ) :=
  Subgroup.closure ({f.1, g.1} : Set (Equiv.Perm ℚ))

theorem left_mem_ambientPair (f g : F) : f.1 ∈ ambientPair f g :=
  Subgroup.subset_closure (by simp)

theorem right_mem_ambientPair (f g : F) : g.1 ∈ ambientPair f g :=
  Subgroup.subset_closure (by simp)

theorem ambientPair_le (f g : F) : ambientPair f g ≤
    GroupApproximation.HigmanThompson.compactF 0 1 := by
  apply (Subgroup.closure_le _).mpr
  intro h hh
  rcases Set.mem_insert_iff.mp hh with rfl | hh
  · exact f.property
  · exact (Set.mem_singleton_iff.mp hh) ▸ g.property

private theorem chart_replicate_true_one (n : ℕ) : chart (List.replicate n true) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- The companion has both endpoint exponents one, a one-sided local slope
shift, and uniform deep branch communication with the input element. -/
theorem exists_companion_with_communication (f : F) (hf : f ≠ 1) :
    ∃ g : F, leftExponent g = 1 ∧ rightExponent g = 1 ∧ ∃ w : List Bool,
      HasBranch g.1 (w ++ [true, false, false]) (w ++ [true, false, false]) ∧
      HasBranch g.1 (w ++ [true, false, true, false, false]) (w ++ [true, false, true, false]) ∧
      ∃ K : ℕ, ∀ p s : List Bool, false ∈ p → true ∈ p → K ≤ s.length →
        BranchRelated (ambientPair f g) (p ++ s) w := by
  obtain ⟨f', hf', u, v, w, hfu, hfv, hu0, huv, hvw, hw1, _⟩ :=
    exists_three_successive_branches f hf
  obtain ⟨na, nz, hna, hnz, L, R, hR, hu, hv0, hv1, hpart⟩ :=
    exists_companion_source_partition hu0 huv hvw hw1
  have hbase : WordPartition 0 1
      (CompanionTrees.baseWords (List.replicate na false) w (List.replicate nz true) L R) := by
    simpa only [CompanionTrees.baseWords, List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using hpart
  obtain ⟨g, hcomp, hg0, hg1, _⟩ := CompanionTrees.exists_companion hbase
    (by simp [chart_replicate_false]) (chart_replicate_true_one nz)
  have hf'mem : f'.1 ∈ ambientPair f g := by
    rcases hf' with hff | hff
    · rw [hff]
      exact left_mem_ambientPair f g
    · rw [hff]
      exact (ambientPair f g).inv_mem (left_mem_ambientPair f g)
  have hruv : BranchRelated (ambientPair f g) u v := ⟨f'.1, hf'mem, hfu⟩
  have hrvw : BranchRelated (ambientPair f g) v w := ⟨f'.1, hf'mem, hfv⟩
  obtain ⟨hc0, hc1, hinterior, hleft, hright⟩ := companion_leaf_communication
    (right_mem_ambientPair f g) hcomp hu hv0 hv1 hruv hrvw
  obtain ⟨K, hK⟩ := deep_related_of_leaf_communication hbase hc0 hc1 hinterior hleft hright
  obtain ⟨hfix, hshift⟩ := CompanionTrees.middle_branches hcomp
  exact ⟨g, hg0, hg1, w, hfix, hshift, K, hK⟩

#audit_axioms exists_companion_with_communication

end Kourovka.P21_38
