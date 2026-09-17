import Kourovka.Problem2153.RankOne.Cells
import Kourovka.Problem2153.RankOne.CellMetadata
import Kourovka.Problem2153.Torus

set_option autoImplicit false
set_option Elab.async false

namespace Kourovka.Problem2153.RootSystem.RankOne

theorem r_cell (k : Fin 63) :
    r⁻¹ * rRoot (rInput k) * r =
      rRoot (rLeft k) * torus (rTorus k).1 (rTorus k).2 * r⁻¹ * rRoot (rRight k) := by
  have h := r_cell_checked k
  rw [r_lhs_spec, r_rhs_spec] at h
  simpa only [r_inv, wordGroup_cons, wordGroup_nil, atomGroup, mul_one, rRoot,
    mul_assoc] using h

theorem s_cell (k : Fin 7) :
    s⁻¹ * sRoot (sInput k) * s =
      sRoot (sLeft k) * torus (sTorus k).1 (sTorus k).2 * s⁻¹ * sRoot (sRight k) := by
  have h := s_cell_checked k
  rw [s_lhs_spec, s_rhs_spec] at h
  simpa only [s_inv, wordGroup_cons, wordGroup_nil, atomGroup, mul_one, sRoot,
    mul_assoc] using h

theorem r_rankOne (p : Fin 8 × Fin 8) (hp : rRoot p ≠ 1) :
    ∃ u' ∈ Rr, ∃ h ∈ H, ∃ u'' ∈ Rr,
      r⁻¹ * rRoot p * r = u' * h * r⁻¹ * u'' := by
  have hp0 : p ≠ (0, 0) := by
    rintro rfl
    exact hp rRoot_zero
  obtain ⟨k, rfl⟩ := r_input_coverage p hp0
  exact ⟨rRoot (rLeft k), rRoot_mem_Rr _, torus (rTorus k).1 (rTorus k).2,
    torus_mem_H _ _, rRoot (rRight k), rRoot_mem_Rr _, r_cell k⟩

theorem s_rankOne (a : Fin 8) (ha : sRoot a ≠ 1) :
    ∃ u' ∈ Rs, ∃ h ∈ H, ∃ u'' ∈ Rs,
      s⁻¹ * sRoot a * s = u' * h * s⁻¹ * u'' := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha sRoot_zero
  obtain ⟨k, rfl⟩ := s_input_coverage a ha0
  exact ⟨sRoot (sLeft k), sRoot_mem_Rs _, torus (sTorus k).1 (sTorus k).2,
    torus_mem_H _ _, sRoot (sRight k), sRoot_mem_Rs _, s_cell k⟩

/-- Once collection supplies the finite family coverage, these are the precise
rank-one subgroup hypotheses of `ReeStructural.rankOne_absorb_torus`. -/
theorem r_rankOne_of_coverage
    (cover : ∀ u ∈ Rr, ∃ p, u = rRoot p) :
    ∀ u ∈ Rr, u ≠ 1 → ∃ u' ∈ Rr, ∃ h ∈ H, ∃ u'' ∈ Rr,
      r⁻¹ * u * r = u' * h * r⁻¹ * u'' := by
  intro u hu hne
  obtain ⟨p, rfl⟩ := cover u hu
  exact r_rankOne p hne

theorem s_rankOne_of_coverage
    (cover : ∀ u ∈ Rs, ∃ a, u = sRoot a) :
    ∀ u ∈ Rs, u ≠ 1 → ∃ u' ∈ Rs, ∃ h ∈ H, ∃ u'' ∈ Rs,
      s⁻¹ * u * s = u' * h * s⁻¹ * u'' := by
  intro u hu hne
  obtain ⟨a, rfl⟩ := cover u hu
  exact s_rankOne a hne

end Kourovka.Problem2153.RootSystem.RankOne
