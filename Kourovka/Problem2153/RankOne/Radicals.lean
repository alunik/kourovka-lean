import Kourovka.Problem2153.RankOne.SimpleWeyl

set_option autoImplicit false
set_option Elab.async false

namespace Kourovka.Problem2153.RootSystem.RankOne

theorem rightConj_mem_Vr {g : G} (hg : g ∈ Vr) : rightConj g r ∈ Vr := by
  apply Collection.rightConj_mem_closure_of_generators _ Vr r ?_ hg
  rintro _ ⟨i, hi1, hi3, a, rfl⟩
  change rightConj (root i a) r ∈ Vr
  rw [root_conj_r i hi1 hi3]
  exact root_mem_Vr _ (rIndex_valid i hi1 hi3).1 (rIndex_valid i hi1 hi3).2 a

theorem rightConj_mem_Vs {g : G} (hg : g ∈ Vs) : rightConj g s ∈ Vs := by
  apply Collection.rightConj_mem_closure_of_generators _ Vs s ?_ hg
  rintro _ ⟨i, hi, a, rfl⟩
  change rightConj (root i a) s ∈ Vs
  rw [root_conj_s i hi]
  exact root_mem_Vs _ (sIndex_valid i hi) a

theorem rightConj_mem_Vr_torus {g : G} (hg : g ∈ Vr) (c d : Fin 7) :
    rightConj g (torus c d) ∈ Vr := by
  apply Collection.rightConj_mem_closure_of_generators _ Vr (torus c d) ?_ hg
  rintro _ ⟨i, hi1, hi3, a, rfl⟩
  change rightConj (root i a) (torus c d) ∈ Vr
  rw [root_conj_torus]
  exact root_mem_Vr i hi1 hi3 _

theorem rightConj_mem_Vs_torus {g : G} (hg : g ∈ Vs) (c d : Fin 7) :
    rightConj g (torus c d) ∈ Vs := by
  apply Collection.rightConj_mem_closure_of_generators _ Vs (torus c d) ?_ hg
  rintro _ ⟨i, hi, a, rfl⟩
  change rightConj (root i a) (torus c d) ∈ Vs
  rw [root_conj_torus]
  exact root_mem_Vs i hi _

theorem H_le_normalizer_Vr : H ≤ Subgroup.normalizer (Vr : Set G) := by
  intro h hh
  obtain ⟨c, d, rfl⟩ := exists_torus_of_mem_H hh
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · exact fun hg => rightConj_mem_Vr_torus hg c d
  · intro hg
    have hi := rightConj_mem_Vr_torus hg (indexInv c) (indexInv d)
    change rightConj (rightConj g (torus c d)) (torus (indexInv c) (indexInv d)) ∈ Vr at hi
    rwa [← torus_inv, rightConj_inv_cancel] at hi

theorem H_le_normalizer_Vs : H ≤ Subgroup.normalizer (Vs : Set G) := by
  intro h hh
  obtain ⟨c, d, rfl⟩ := exists_torus_of_mem_H hh
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · exact fun hg => rightConj_mem_Vs_torus hg c d
  · intro hg
    have hi := rightConj_mem_Vs_torus hg (indexInv c) (indexInv d)
    change rightConj (rightConj g (torus c d)) (torus (indexInv c) (indexInv d)) ∈ Vs at hi
    rwa [← torus_inv, rightConj_inv_cancel] at hi

end Kourovka.Problem2153.RootSystem.RankOne
