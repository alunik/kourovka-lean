import Kourovka.Problem2153.Triangular
import Kourovka.Problem2153.Torus

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.RankOne

open WilsonModel

theorem r_negative_entry : RootData.matrixHom (r * root 1 1 * r⁻¹) 1 2 ≠ 0 := by
  have hr : RootData.matrixHom r = rho := rfl
  have hx : RootData.matrixHom (root 1 1) = RootData.rootMatrix 1 1 :=
    RootData.root_alignment 1 1
  have hm : RootData.matrixHom (r * root 1 1 * r⁻¹) =
      rho * RootData.rootMatrix 1 1 * rho := by
    rw [r_inv, map_mul, map_mul, hr, hx]
  rw [hm]
  decide +kernel

theorem s_negative_entry : RootData.matrixHom (s * root 0 1 * s⁻¹) 0 1 ≠ 0 := by
  have hs : RootData.matrixHom s = sigma := rfl
  have ht : RootData.matrixHom (root 0 1) = RootData.rootMatrix 0 1 :=
    RootData.root_alignment 0 1
  have hm : RootData.matrixHom (s * root 0 1 * s⁻¹) =
      sigma * RootData.rootMatrix 0 1 * sigma := by
    rw [s_inv, map_mul, map_mul, hs, ht]
  rw [hm]
  decide +kernel

theorem r_conjugate_not_mem_B : r * root 1 1 * r⁻¹ ∉ B := by
  intro h
  exact r_negative_entry (B_le_lower h 1 2 (by decide))

theorem s_conjugate_not_mem_B : s * root 0 1 * s⁻¹ ∉ B := by
  intro h
  exact s_negative_entry (B_le_lower h 0 1 (by decide))

theorem r_nondegenerate : ∃ b ∈ B, r * b * r⁻¹ ∉ B :=
  ⟨root 1 1, (show U ≤ B from le_sup_left) (root_mem_U _ _), r_conjugate_not_mem_B⟩

theorem s_nondegenerate : ∃ b ∈ B, s * b * s⁻¹ ∉ B :=
  ⟨root 0 1, (show U ≤ B from le_sup_left) (root_mem_U _ _), s_conjugate_not_mem_B⟩

end Kourovka.Problem2153.RootSystem.RankOne
