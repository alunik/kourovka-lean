import Kourovka.Problem2153.External.TitsSystem.Bruhat
import Kourovka.Problem2153.BruhatReduction

set_option autoImplicit false

namespace Kourovka.Problem2153

universe u v

/-- Tau Ceti's proved abstract BN-pair theorem supplies exact U H W U coverage once the
concrete B/N factorizations and Weyl normalization are established.

The Tits-system axioms and each factorization are explicit hypotheses, not claims about
an unconstructed Ree group. -/
theorem bruhatCoverage_of_titsSystem {G : Type u} [Group G] {K : Type v}
    (T : TauCeti.TitsSystem G) (U H : Subgroup G) (W : K → G)
    (hBLeft : ∀ b ∈ T.subgroupB, ∃ u ∈ U, ∃ h ∈ H, b = u * h)
    (hBRight : ∀ b ∈ T.subgroupB, ∃ h ∈ H, ∃ u ∈ U, b = h * u)
    (hN : ∀ n ∈ T.subgroupN, ∃ h ∈ H, ∃ k, n = h * W k)
    (hNormalize : ∀ k h, h ∈ H → W k * h * (W k)⁻¹ ∈ H) :
    BruhatCoverage (fun u : U => (u : G)) (fun h : H => (h : G)) W := by
  intro g
  obtain ⟨n, hn⟩ := T.exists_mem_doubleCoset g
  obtain ⟨b₁, hb₁, b₂, hb₂, hg⟩ := DoubleCoset.mem_doubleCoset.mp hn
  obtain ⟨u, hu, h₁, hh₁, hb₁'⟩ := hBLeft b₁ hb₁
  obtain ⟨h₃, hh₃, v, hv, hb₂'⟩ := hBRight b₂ hb₂
  obtain ⟨h₂, hh₂, k, hn'⟩ := hN n n.property
  refine ⟨⟨u, hu⟩,
    ⟨h₁ * h₂ * (W k * h₃ * (W k)⁻¹), H.mul_mem (H.mul_mem hh₁ hh₂)
      (hNormalize k h₃ hh₃)⟩, k, ⟨v, hv⟩, ?_⟩
  simp only
  rw [hg, hb₁', hb₂', hn']
  simp [mul_assoc]

#print axioms bruhatCoverage_of_titsSystem

end Kourovka.Problem2153
