import Kourovka.Problem2153.BorelQuotient
import Kourovka.Problem2153.RootCollection
import Kourovka.Problem2153.RankOne
import Kourovka.Problem2153.Structure.RankOneBruhat
import Kourovka.Problem2153.External.TitsSystem.Coverage

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem.BNPair

open RankOne
open scoped Pointwise

private theorem r_factor
    (hf : ∀ u ∈ U, ∃ a ∈ Rr, ∃ v ∈ Vr, u = a * v) :
    ∀ b ∈ B, ∃ a ∈ Rr, ∃ c : G, b = a * c ∧ r⁻¹ * c * r ∈ B := by
  apply ReeStructural.simple_factor_of_radical U H Rr Vr r H_le_normalizer_U hf
  · intro v hv
    exact (show U ≤ B from le_sup_left) (Vr_le_U (rightConj_mem_Vr hv))
  · intro h hh
    exact (show H ≤ B from le_sup_right) (rightConj_mem_H_r hh)

private theorem s_factor
    (hf : ∀ u ∈ U, ∃ a ∈ Rs, ∃ v ∈ Vs, u = a * v) :
    ∀ b ∈ B, ∃ a ∈ Rs, ∃ c : G, b = a * c ∧ s⁻¹ * c * s ∈ B := by
  apply ReeStructural.simple_factor_of_radical U H Rs Vs s H_le_normalizer_U hf
  · intro v hv
    exact (show U ≤ B from le_sup_left) (Vs_le_U (rightConj_mem_Vs hv))
  · intro h hh
    exact (show H ≤ B from le_sup_right) (rightConj_mem_H_s hh)

private theorem r_rank : ∀ a ∈ Rr, a ≠ 1 → ∃ a' ∈ Rr, ∃ b ∈ B,
    r⁻¹ * a * r = a' * r⁻¹ * b := by
  apply ReeStructural.rankOne_absorb_torus B H Rr r
    (Rr_le_U.trans le_sup_left)
  · intro h hh
    simpa only [rightConj, r_inv] using (show H ≤ B from le_sup_right) (rightConj_mem_H_r hh)
  · exact r_rankOne_of_coverage (fun _ hg => RootCollection.Rr_coverage hg)

private theorem s_rank : ∀ a ∈ Rs, a ≠ 1 → ∃ a' ∈ Rs, ∃ b ∈ B,
    s⁻¹ * a * s = a' * s⁻¹ * b := by
  apply ReeStructural.rankOne_absorb_torus B H Rs s
    (Rs_le_U.trans le_sup_left)
  · intro h hh
    simpa only [rightConj, s_inv] using (show H ≤ B from le_sup_right) (rightConj_mem_H_s hh)
  · exact s_rankOne_of_coverage (fun _ hg => RootCollection.Rs_coverage hg)

private theorem r_orientation {n : G} (hn : n ∈ N) :
    (∀ a ∈ Rr, n * a * n⁻¹ ∈ B) ∨
    (∀ a ∈ Rr, (n * r) * a * (n * r)⁻¹ ∈ B) := by
  obtain ⟨h,hh,i,rfl⟩ := N_factor hn
  exact ReeStructural.orientation_torus_left B Rr r (Weyl.rep i) h
    ((show H ≤ B from le_sup_right) hh) (orientation_r_B i)

private theorem s_orientation {n : G} (hn : n ∈ N) :
    (∀ a ∈ Rs, n * a * n⁻¹ ∈ B) ∨
    (∀ a ∈ Rs, (n * s) * a * (n * s)⁻¹ ∈ B) := by
  obtain ⟨h,hh,i,rfl⟩ := N_factor hn
  exact ReeStructural.orientation_torus_left B Rs s (Weyl.rep i) h
    ((show H ≤ B from le_sup_right) hh) (orientation_s_B i)

theorem r_left_step
    (hf : ∀ u ∈ U, ∃ a ∈ Rr, ∃ v ∈ Vr, u = a * v) (n : N) :
    DoubleCoset.doubleCoset r B B * DoubleCoset.doubleCoset (n : G) B B ⊆
      DoubleCoset.doubleCoset (r * n) B B ∪ DoubleCoset.doubleCoset (n : G) B B := by
  apply ReeStructural.left_doubleCoset_mul_subset_of_right
  rw [r_inv]
  exact ReeStructural.rankOne_doubleCoset_mul_subset B Rr r (n : G)⁻¹
    (r_factor hf) r_rank (r_orientation (N.inv_mem n.property))

theorem s_left_step
    (hf : ∀ u ∈ U, ∃ a ∈ Rs, ∃ v ∈ Vs, u = a * v) (n : N) :
    DoubleCoset.doubleCoset s B B * DoubleCoset.doubleCoset (n : G) B B ⊆
      DoubleCoset.doubleCoset (s * n) B B ∪ DoubleCoset.doubleCoset (n : G) B B := by
  apply ReeStructural.left_doubleCoset_mul_subset_of_right
  rw [s_inv]
  exact ReeStructural.rankOne_doubleCoset_mul_subset B Rs s (n : G)⁻¹
    (s_factor hf) s_rank (s_orientation (N.inv_mem n.property))

/-- The concrete Tits system, with only the two unipotent factorizations supplied
as parameters here. The public construction discharges these separately. -/
def of_factorizations
    (hfr : ∀ u ∈ U, ∃ a ∈ Rr, ∃ v ∈ Vr, u = a * v)
    (hfs : ∀ u ∈ U, ∃ a ∈ Rs, ∃ v ∈ Vs, u = a * v) : TauCeti.TitsSystem G where
  subgroupB := B
  subgroupN := N
  closure_subgroupB_union_subgroupN := closure_B_union_N
  intersection_normal := B_subgroupOf_N_normal
  simple := simpleImages
  closure_simple := closure_simpleImages
  exists_simpleRep_sq_mem := by
    intro q hq
    rcases hq with rfl | rfl
    · refine ⟨rN,rfl,?_⟩
      change r * r ∈ B
      rw [r_square]
      exact B.one_mem
    · refine ⟨sN,rfl,?_⟩
      change s * s ∈ B
      rw [s_square]
      exact B.one_mem
  mul_doubleCoset_subset := by
    intro q hq
    rcases hq with rfl | rfl
    · exact ⟨rN,rfl,r_left_step hfr⟩
    · exact ⟨sN,rfl,s_left_step hfs⟩
  exists_conj_not_mem := by
    intro q hq
    rcases hq with rfl | rfl
    · obtain ⟨b,hb,hnot⟩ := r_nondegenerate
      exact ⟨rN,rfl,⟨b,hb⟩,hnot⟩
    · obtain ⟨b,hb,hnot⟩ := s_nondegenerate
      exact ⟨sN,rfl,⟨b,hb⟩,hnot⟩

theorem uhwu_of_factorizations
    (hfr : ∀ u ∈ U, ∃ a ∈ Rr, ∃ v ∈ Vr, u = a * v)
    (hfs : ∀ u ∈ U, ∃ a ∈ Rs, ∃ v ∈ Vs, u = a * v) :
    BruhatCoverage (fun u : U => (u : G)) (fun h : H => (h : G)) Weyl.rep := by
  apply bruhatCoverage_of_titsSystem (of_factorizations hfr hfs) U H Weyl.rep
  · exact fun _ hb => B_factor_right hb
  · exact fun _ hb => B_factor_left hb
  · exact fun _ hn => N_factor hn
  · intro k h hh
    have hn := W_le_normalizer_H (W.inv_mem (Weyl.rep_mem_W k))
    have he := (Subgroup.mem_normalizer_iff''.mp hn h).mp hh
    simpa only [inv_inv] using he

end Kourovka.Problem2153.RootSystem.BNPair
