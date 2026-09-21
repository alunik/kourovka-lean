import Kourovka2135.ClassTwoBinomial
import Kourovka2135.MinimalKernelStructure

/-!
In a perfect ambient group, a minimal normal noncentral p-subgroup has exponent
p when p is odd. This does not assert that the subgroup is abelian or split.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped commutatorElement
variable {G : Type u} [Group G]

def centralCommutatorPrimePowerHom {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hD : commutator G ≤ Subgroup.center G)
    (hE : IsElementaryAbelian p (commutator G)) : G →* G where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := by
    let : IsElementaryAbelian p (commutator G) := hE
    have hc : paperCommutator y x ∈ commutator G := by
      change paperCommutator y x ∈ ⁅(⊤ : Subgroup G), ⊤⁆
      simpa only [paperCommutator, commutatorElement_def, inv_inv] using
        Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := ⊤)
          (g₁ := y⁻¹) (g₂ := x⁻¹) (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact mul_pow_prime_of_central_commutator hp hodd x y (hD hc)
      (elemPow_eq_one_of_isElementaryAbelian _ hc)

theorem minimal_noncentral_pow_prime_eq_one [Finite G] [Group.IsPerfect G]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (x : N) : x ^ p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p N) := ⟨hN⟩
  rcases subsingleton_or_nontrivial N with htriv | htriv
  · let := htriv
    exact Subsingleton.elim _ _
  let := htriv
  have hΦne : frattini N ≠ ⊤ := by
    intro heq
    have hbot : (⊥ : Subgroup N) = ⊤ := frattini_nongenerating (by simp [heq])
    exact bot_ne_top hbot
  have hΦmap := characteristic_map_le_center_of_minimal_noncentral N hmin (frattini N) hΦne
  have hpcenter (a : N) : (a : G) ^ p ∈ Subgroup.center G := by
    exact hΦmap (Subgroup.mem_map_of_mem N.subtype
      (pth_power_mem_frattini_of_isPGroup (p := p) a))
  have hD : commutator N ≤ Subgroup.center N :=
    (commutator_le_frattini_of_isPGroup (R := N) (p := p)).trans
      (minimal_noncentral_frattini_le_center N hmin)
  let f : N →* N := centralCommutatorPrimePowerHom hp hodd hD
    (minimal_noncentral_commutator_isElementaryAbelian hp N hN hmin)
  have hkill : ⁅N, (⊤ : Subgroup G)⁆ ≤ f.ker.map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    let u : N := ⟨a, ha⟩
    refine ⟨u * MulAut.conjNormal g u⁻¹, ?_, ?_⟩
    · change f (u * MulAut.conjNormal g u⁻¹) = 1
      rw [map_mul]
      change u ^ p * (MulAut.conjNormal g u⁻¹) ^ p = 1
      rw [← map_pow, inv_pow]
      apply Subtype.ext
      change a ^ p * (g * (a ^ p)⁻¹ * g⁻¹) = 1
      have hcomm : Commute (a ^ p) g :=
        (show Commute g (a ^ p) from Subgroup.mem_center_iff.mp (hpcenter u) g).symm
      rw [← hcomm.inv_left.eq]
      group
    · change a * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      group
  rw [commutator_eq_self_of_minimal_noncentral N hnoncentral hmin] at hkill
  obtain ⟨y, hy, heq⟩ := hkill x.property
  have hyx : y = x := Subtype.ext heq
  exact hyx ▸ hy

end Kourovka2135
