import Kourovka.Problem2153.Parabolic
import Kourovka.Problem2153.Simplicity
import Kourovka.Problem2153.NormalGeneration.W0SL2

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem

 theorem longest_reflection_word : t * rightConj t Weyl.w0 * t = s := by
  have h := NormalGeneration.W0SL2_checked
  simpa [RankOne.wordGroup, RankOne.atomGroup, root_one, rootBase,
    Weyl.w0_eq, rightConj, pow_succ, mul_inv_rev, r_inv, s_inv, mul_assoc] using h

 theorem closure_B_union_rs : Subgroup.closure ((B : Set G) ∪ {r, s}) = ⊤ := by
  let Q := Subgroup.closure ((B : Set G) ∪ {r, s})
  have hB : B ≤ Q := fun _ hb => Subgroup.subset_closure (Or.inl hb)
  apply eq_top_of_generators
  · exact hB ((show U ≤ B from le_sup_left) t_mem_U)
  · exact hB ((show U ≤ B from le_sup_left) x_mem_U)
  · exact Subgroup.subset_closure (Or.inr (by simp))
  · exact Subgroup.subset_closure (Or.inr (by simp))
  · exact fun a b => hB ((show H ≤ B from le_sup_right) (torus_mem_H a b))

/-- Every hypothesis except whole-group Bruhat coverage is discharged in the actual
Wilson matrix model. The eventual BN-pair theorem supplies the single explicit premise. -/
theorem P_isCoatom_of_coverage
    (hCover : ∀ g : G, ∃ b₁ ∈ B, ∃ k : Fin 16, ∃ b₂ ∈ B,
      g = b₁ * Weyl.rep k * b₂) : IsCoatom P := by
  have hr : r ∈ P := (show Subgroup.closure ({r} : Set G) ≤ P from le_sup_right)
    (Subgroup.subset_closure (by simp))
  exact isCoatom_of_bruhat_weyl_closure_tests B P Weyl.rep r s t Weyl.w0
    P_ne_top le_sup_left hr ((show U ≤ B from le_sup_left) t_mem_U) hCover
    (fun k hk => Weyl.w0_mem_closure_of_not_mem P hr k hk)
    longest_reflection_word closure_B_union_rs

#print axioms longest_reflection_word
#print axioms P_isCoatom_of_coverage
end Kourovka.Problem2153.RootSystem
