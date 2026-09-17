import Kourovka.Problem2153.Borel
import Kourovka.Problem2153.Simplicity

set_option autoImplicit false
namespace Kourovka.Problem2153.RootSystem.NormalGeneration

 theorem rightConj_mem_normal (Q : Subgroup G) [Q.Normal] {a : G} (ha : a ∈ Q) (g : G) :
    rightConj a g ∈ Q := by
  simpa only [rightConj, inv_inv] using (inferInstance : Q.Normal).conj_mem a ha g⁻¹

 theorem root_mem_normal_of_base (Q : Subgroup G) [Q.Normal]
    (i : Fin 12) (hb : rootBase i ∈ Q) (a : Fin 8) : root i a ∈ Q := by
  by_cases ha : a = 0
  · subst a; exact Q.one_mem
  · simp only [root, if_neg ha]
    exact rightConj_mem_normal Q hb _

 theorem rootBase_mem_normal_of_root (Q : Subgroup G) [Q.Normal]
    (i : Fin 12) {a : Fin 8} (ha : a ≠ 0) (h : root i a ∈ Q) : rootBase i ∈ Q := by
  simp only [root, if_neg ha] at h
  have hc := rightConj_mem_normal Q h (torus (sectionParameters i a).1 (sectionParameters i a).2)⁻¹
  simpa only [rightConj_inv_cancel] using hc

 theorem rootBase_three (Q : Subgroup G) [Q.Normal] (h : rootBase 11 ∈ Q) :
    rootBase 3 ∈ Q := by
  change rightConj (x ^ 2) (s * r * s) ∈ Q at h
  have hc := rightConj_mem_normal Q h (s * r * s)⁻¹
  change x ^ 2 ∈ Q
  simpa only [rightConj_inv_cancel] using hc

 def suzukiGenerator : Fin 3 → G :=
   ![root 3 1, root 3 6, rightConj (root 3 1) r]

 def suzukiWord (w : List (Fin 3)) : G := (w.map suzukiGenerator).prod

 theorem suzukiWord_mem (Q : Subgroup G) [Q.Normal] (h : rootBase 3 ∈ Q)
    (w : List (Fin 3)) : suzukiWord w ∈ Q := by
  apply Q.list_prod_mem
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  fin_cases i
  · exact root_mem_normal_of_base Q 3 h 1
  · exact root_mem_normal_of_base Q 3 h 6
  · exact rightConj_mem_normal Q (root_mem_normal_of_base Q 3 h 1) r

end Kourovka.Problem2153.RootSystem.NormalGeneration
