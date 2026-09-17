import Kourovka.Problem2153.TorusAction
import Kourovka.Problem2153.Triangular
import Kourovka.Problem2153.Weyl
import Kourovka.Problem2153.Structure.BNBridge

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem

theorem root_one (i : Fin 12) : root i 1 = rootBase i := by
  have hi : sectionParameters i 1 = (0,0) := by fin_cases i <;> rfl
  simp only [root, show (1 : Fin 8) ≠ 0 by decide, ite_false, hi,
    torus_zero_zero, rightConj, inv_one, one_mul, mul_one]

theorem t_mem_U : t ∈ U := by simpa [root_one, rootBase] using root_mem_U 0 1
theorem x_mem_U : x ∈ U := by simpa [root_one, rootBase] using root_mem_U 1 1

/-- A subgroup containing the displayed generators contains the actual ambient group. -/
theorem eq_top_of_generators (Q : Subgroup G) (ht : t ∈ Q) (hx : x ∈ Q)
    (hr : r ∈ Q) (hs : s ∈ Q) (hh : ∀ a b, torus a b ∈ Q) : Q = ⊤ := by
  apply top_le_iff.mp
  rintro ⟨g,hg⟩ _
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | ⟨⟨a,b⟩,rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ht
      · exact hx
      · exact hr
      · exact hs
    · exact hh a b
  | one => exact Q.one_mem
  | mul a b _ _ ha hb => exact Q.mul_mem (ha (Subgroup.mem_top _)) (hb (Subgroup.mem_top _))
  | inv a _ ha => exact Q.inv_mem (ha (Subgroup.mem_top _))

theorem B_factor_right {b : G} (hb : b ∈ B) : ∃ u ∈ U, ∃ h ∈ H, b = u * h :=
  ReeStructural.sup_factor_right U H H_le_normalizer_U hb

theorem B_factor_left {b : G} (hb : b ∈ B) : ∃ h ∈ H, ∃ u ∈ U, b = h * u :=
  ReeStructural.sup_factor_left U H H_le_normalizer_U hb

theorem N_factor {n : G} (hn : n ∈ N) : ∃ h ∈ H, ∃ k : Fin 16, n = h * Weyl.rep k := by
  obtain ⟨h, hh, w, hw, rfl⟩ := ReeStructural.sup_factor_right H W W_le_normalizer_H hn
  obtain ⟨k,rfl⟩ := Weyl.exists_rep_of_mem_W hw
  exact ⟨h,hh,k,rfl⟩

theorem B_inf_N : B ⊓ N = H := by
  apply ReeStructural.intersection_eq_of_weyl_tests B N H Weyl.rep
    (show H ≤ B from le_sup_right) (show H ≤ N from le_sup_left)
  · exact fun _ hn => N_factor hn
  · intro k hk
    have he : Weyl.rep k = 1 :=
      Weyl.eq_one_of_mem_W_lowerTriangular (Weyl.rep_mem_W k) (B_le_lower hk)
    rw [he]
    exact H.one_mem

theorem B_sup_N : B ⊔ N = ⊤ := by
  apply eq_top_of_generators
  · exact (show B ≤ B ⊔ N from le_sup_left) ((show U ≤ B from le_sup_left) t_mem_U)
  · exact (show B ≤ B ⊔ N from le_sup_left) ((show U ≤ B from le_sup_left) x_mem_U)
  · exact (show N ≤ B ⊔ N from le_sup_right) ((show W ≤ N from le_sup_right) r_mem_W)
  · exact (show N ≤ B ⊔ N from le_sup_right) ((show W ≤ N from le_sup_right) s_mem_W)
  · intro a b
    exact (show B ≤ B ⊔ N from le_sup_left) ((show H ≤ B from le_sup_right) (torus_mem_H a b))

theorem closure_B_union_N : Subgroup.closure ((B : Set G) ∪ N) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  exact B_sup_N

end Kourovka.Problem2153.RootSystem
