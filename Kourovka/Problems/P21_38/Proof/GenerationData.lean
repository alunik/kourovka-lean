import Kourovka.Problems.P21_38.Proof.CompanionConstruction
import Kourovka.Problems.P21_38.Proof.LocalInterpolation
import Kourovka.Problems.P21_38.Proof.NontrivialCore

/-!
# Verified inputs to local generation

All fields below are obtained from the actual companion construction. They
include a nontrivial compactly supported element of the two-generated group;
no generation or interpolation claim is assumed.
-/

namespace Kourovka.P21_38

open BinaryWord GroupApproximation.HigmanThompson

structure GenerationData (f g : F) : Prop where
  left_exponent : leftExponent g = 1
  right_exponent : rightExponent g = 1
  deep : DeepBranchCommunication (ambientPair f g)
  transitive : DyadicTransitive (ambientPair f g)
  nontrivial_core : ∃ h ∈ ambientPair f g, h ∈ compactCore 0 ∧ h ≠ 1
  local_shift : ∃ u v : List Bool,
    0 < chart u 0 ∧ chart u 1 < 1 ∧ 0 < chart v 0 ∧ chart v 1 = chart u 0 ∧
    HasBranch g.1 (u ++ [false]) u ∧ Set.EqOn g.1 id (Set.Icc (chart v 0) (chart u 0))

theorem exists_generationData (f : F) (hf : f ≠ 1) : ∃ g : F, GenerationData f g := by
  obtain ⟨g, hg0, hg1, w, hfix, hshift, K, hK⟩ := exists_companion_with_communication f hf
  have hdeep : DeepBranchCommunication (ambientPair f g) := by
    intro u v hu hv
    exact ⟨K, fun s t hs ht => (hK u s hu.1 hu.2 hs).trans (hK v t hv.1 hv.2 ht).symm⟩
  have htrans : DyadicTransitive (ambientPair f g) :=
    dyadicTransitive_of_deep_branches (fun u v hu0 hu1 hv0 hv1 => hdeep u v ⟨hu0, hu1⟩ ⟨hv0, hv1⟩)
  let u := w ++ [true, false, true, false]
  let v := w ++ [true, false, false]
  have hu0 : 0 < chart u 0 := by
    have hbase := (chart_mem_unit w (show (0 : ℚ) ∈ Set.Icc 0 1 by norm_num)).1
    have h := chart_strictMono w (show (0 : ℚ) < 5 / 8 by norm_num)
    dsimp [u]
    norm_num [chart_append, chart]
    linarith
  have hu1 : chart u 1 < 1 := by
    have hbase := (chart_mem_unit w (show (1 : ℚ) ∈ Set.Icc 0 1 by norm_num)).2
    have h := chart_strictMono w (show (11 / 16 : ℚ) < 1 by norm_num)
    dsimp [u]
    norm_num [chart_append, chart]
    linarith
  have hv0 : 0 < chart v 0 := by
    have hbase := (chart_mem_unit w (show (0 : ℚ) ∈ Set.Icc 0 1 by norm_num)).1
    have h := chart_strictMono w (show (0 : ℚ) < 1 / 2 by norm_num)
    dsimp [v]
    norm_num [chart_append, chart]
    linarith
  have hvu : chart v 1 = chart u 0 := by norm_num [v, u, chart_append, chart]
  have hs : HasBranch g.1 (u ++ [false]) u := by
    simpa only [u, List.append_assoc, List.cons_append, List.nil_append] using hshift
  have hidentity : Set.EqOn g.1 id (Set.Icc (chart v 0) (chart u 0)) := by
    rw [← hvu]
    exact fun x hx => hfix.identity_on_interval hx.1 hx.2
  obtain ⟨h, hh, hhcore, hhne⟩ := exists_nontrivial_core_of_shift
    (ambientPair_le f g) htrans (right_mem_ambientPair f g) hu0 hu1 hs
  exact ⟨g, hg0, hg1, hdeep, htrans, ⟨h, hh, hhcore, hhne⟩,
    ⟨u, v, hu0, hu1, hv0, hvu, hs, hidentity⟩⟩

#audit_axioms exists_generationData

end Kourovka.P21_38
