import Kourovka.Problems.P21_38.Proof.GenerationData
import Kourovka.Problems.P21_38.Proof.IntervalCompression
import Kourovka.Problems.P21_38.Proof.RefinedCoreBranches
import Kourovka.Problems.P21_38.Proof.DiagonalGeneration

/-!
# Ordinary generation with a prescribed companion

The required positive-exponent case of Golan-Polak's generation theorem is
proved here from the finite branch construction. Exact local interpolation
gives commutators, perfectness gives the full endpoint kernel, and the
companion's endpoint vector fills the diagonal quotient.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord

/-- Every interpolation hypothesis is discharged by the constructed companion. -/
theorem GenerationData.coreLocalInterpolation {f g : F} (hd : GenerationData f g) :
    CoreLocalInterpolation 0 (ambientPair f g) := by
  obtain ⟨u, v, hu0, hu1, hv0, hvu, hshift, hfix⟩ := hd.local_shift
  have hH := ambientPair_le f g
  have hcuts := wordFixer_noInvariantRealCut_of_deep_branches hH hd.deep hd.nontrivial_core u
  have hut : true ∈ u := (mixed_of_interior hu0 hu1).2
  have hv1 : chart v 1 < 1 := by
    rw [hvu]
    exact (chart_zero_lt_one u).trans hu1
  have hα : chart v 0 < chart u 0 := (chart_zero_lt_one v).trans_eq hvu
  intro k hk a b _ _ ha hab hb
  let kF : F := ⟨k, compactCore_le hk⟩
  obtain ⟨A, B, hA, hAa, hbB, hB, hkA, _, us, vs, hus, hvs, hlen, hbranches, hzus, hzvs⟩ :=
    exists_refined_core_branch_partitions hd.deep hut kF hk ha hab hb
  obtain ⟨q, hq, hqmap⟩ := exists_interval_compression_to_binary
    hH hd.deep hd.nontrivial_core hA hB v hv0 hv1
  have hcompress : ∃ q ∈ ambientPair f g,
      Set.MapsTo q (Set.Icc A B) (Set.Icc (chart v 0) (chart u 0)) := by
    exact ⟨q, hq, by simpa only [hvu] using hqmap⟩
  obtain ⟨h, hh, hhcore, hhf⟩ := exists_core_interpolant_of_wordPartitions
    hH (right_mem_ambientPair f g) hshift hα hfix hcuts kF
    hA hkA hus hvs hlen hbranches hzus hzvs hcompress
  exact ⟨h, hh, hhcore, fun t ht => hhf ⟨hAa.trans ht.1, ht.2.trans hbB⟩⟩

/-- Every nonidentity element of the actual diagonal subgroup has a generating mate. -/
theorem exists_generating_companion (f : diagonalSubgroup) (hf : f ≠ 1) :
    ∃ g : diagonalSubgroup, GeneratesPair f g := by
  have hfF : (f : F) ≠ 1 := fun h => hf (Subtype.ext h)
  obtain ⟨g, hd⟩ := exists_generationData (f : F) hfF
  have hg : g ∈ diagonalSubgroup := hd.left_exponent.trans hd.right_exponent.symm
  let gD : diagonalSubgroup := ⟨g, hg⟩
  exact ⟨gD, generatesPair_diagonal_of_local_interpolation f gD
    hd.left_exponent hd.right_exponent hd.coreLocalInterpolation⟩

/-- The generation half of spread exactly one. -/
theorem diagonal_hasSpreadAtLeast_one : HasSpreadAtLeast diagonalSubgroup 1 :=
  hasSpreadAtLeast_one_iff.mpr exists_generating_companion

#audit_axioms GenerationData.coreLocalInterpolation
#audit_axioms exists_generating_companion
#audit_axioms diagonal_hasSpreadAtLeast_one

end Kourovka.P21_38
