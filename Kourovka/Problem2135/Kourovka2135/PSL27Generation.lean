import Kourovka2135.PSL27BinaryHeartCoordinates

/-! The two actual projective matrices used for the binary PSL2(7) heart
really generate PSL2(7). The proof uses elementary transvection generation
inside SL2, followed by the actual central quotient. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PSL27Generation
open scoped Matrix MatrixGroups

section Elementary
variable {K : Type*} [Field K]

def lower (t : K) : SLTwo.SL2 K := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

/-- A subgroup containing both root groups contains every actual SL2 matrix. -/
theorem eq_top_of_roots (H : Subgroup (SLTwo.SL2 K))
    (hu : ∀ t : K, SLTwo.uni t ∈ H) (hl : ∀ t : K, lower t ∈ H) : H = ⊤ := by
  apply top_le_iff.mp
  intro g _
  apply Matrix.SL2.transvection_induction (fun A : SLTwo.SL2 K => A ∈ H)
    (fun i j hij c => ?_) (fun _ _ ha hb => H.mul_mem ha hb) g
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · convert hu c using 1
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, SLTwo.uni]
  · convert hl c using 1
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, lower]
  · exact (hij rfl).elim
end Elementary

open PSL27BinaryHeartCoordinates OddPSLTwoProjectiveChart

private theorem upper_power : ∀ t : F, SLTwo.uni t = (SLTwo.uni (1 : F)) ^ t.val := by
  decide +kernel

private theorem lower_conjugate : ∀ t : F,
    lower t = weyl * SLTwo.uni (-t) * weyl⁻¹ := by
  decide +kernel

/-- The precise two generators used by the actual heart coordinate matrices. -/
theorem closure_U_W : Subgroup.closure ({U, W} : Set G) = ⊤ := by
  let H := Subgroup.closure ({U, W} : Set G)
  have hu : U ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hw : W ∈ H := Subgroup.subset_closure
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hr : (H.comap (quotient F)) = ⊤ := by
    apply eq_top_of_roots
    · intro t
      change quotient F (SLTwo.uni t) ∈ H
      rw [upper_power, map_pow]
      exact H.pow_mem hu _
    · intro t
      change quotient F (lower t) ∈ H
      rw [lower_conjugate, map_mul, map_mul, map_inv]
      apply H.mul_mem (H.mul_mem hw ?_) (H.inv_mem hw)
      rw [upper_power, map_pow]
      exact H.pow_mem hu _
  apply top_le_iff.mp
  intro g _
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SLTwo.SL2 F)) g
  exact show s ∈ H.comap (quotient F) from hr ▸ Subgroup.mem_top s

end Kourovka2135.PSL27Generation
