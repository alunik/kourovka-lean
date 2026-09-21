import Kourovka2135.MinimalKernelStructure
import Mathlib.GroupTheory.Abelianization.Defs

/-!
The abelianization of a minimal noncentral normal p-subgroup of a finite
perfect group has exponent p, including p = 2. Consequently its binary
nonabelian kernels have exponent at most four.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]

theorem minimal_noncentral_prime_power_mem_commutator
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (x : N) : x ^ p ∈ commutator N := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p N) := ⟨hN⟩
  have hΦne : frattini N ≠ ⊤ := by
    intro heq
    have hbot : (⊥ : Subgroup N) = ⊤ := frattini_nongenerating (by simp [heq])
    have hNbot : N = ⊥ := by
      apply bot_unique
      intro a ha
      have : (⟨a, ha⟩ : N) ∈ (⊥ : Subgroup N) := hbot ▸ Subgroup.mem_top _
      exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
    exact hnoncentral (hNbot ▸ bot_le)
  have hΦmap := characteristic_map_le_center_of_minimal_noncentral N hmin (frattini N) hΦne
  have hpcenter (a : N) : (a : G) ^ p ∈ Subgroup.center G :=
    hΦmap (Subgroup.mem_map_of_mem N.subtype
      (pth_power_mem_frattini_of_isPGroup (p := p) a))
  let q : N →* Abelianization N := Abelianization.of
  let f : N →* Abelianization N := {
    toFun := fun a => q a ^ p
    map_one' := by simp
    map_mul' := fun a b => by simp only [map_mul, mul_pow] }
  have hkill : ⁅N, (⊤ : Subgroup G)⁆ ≤ f.ker.map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    let u : N := ⟨a, ha⟩
    have hconj : MulAut.conjNormal g (u ^ p) = u ^ p := by
      apply Subtype.ext
      change g * a ^ p * g⁻¹ = a ^ p
      rw [Subgroup.mem_center_iff.mp (hpcenter u) g]
      simp only [mul_assoc, mul_inv_cancel, mul_one, u]
    have heq : (MulAut.conjNormal g u⁻¹) ^ p = (u ^ p)⁻¹ := by
      rw [← map_pow, inv_pow, map_inv, hconj]
    refine ⟨u * MulAut.conjNormal g u⁻¹, ?_, ?_⟩
    · change f (u * MulAut.conjNormal g u⁻¹) = 1
      rw [map_mul]
      change q u ^ p * q (MulAut.conjNormal g u⁻¹) ^ p = 1
      rw [← map_pow, ← map_pow, heq, map_inv, mul_inv_cancel]
    · change a * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      simp only [mul_assoc]
  rw [commutator_eq_self_of_minimal_noncentral N hnoncentral hmin] at hkill
  obtain ⟨y, hy, heq⟩ := hkill x.property
  have hyx : y = x := Subtype.ext heq
  have hx : f x = 1 := hyx ▸ hy
  change q x ^ p = 1 at hx
  rw [← map_pow] at hx
  exact (QuotientGroup.eq_one_iff _).mp hx

theorem minimal_noncentral_abelianization_isElementaryAbelian
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    IsElementaryAbelian p (Abelianization N) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x
  change QuotientGroup.mk' (commutator N) (a ^ p) = 1
  exact (QuotientGroup.eq_one_iff _).mpr
    (minimal_noncentral_prime_power_mem_commutator hp N hN hnoncentral hmin a)

theorem minimal_noncentral_frattini_eq_commutator
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    frattini N = commutator N := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p N) := ⟨hN⟩
  apply le_antisymm
  · rw [frattini_eq_closure_commutator_union_powers (p := p)]
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · exact minimal_noncentral_prime_power_mem_commutator hp N hN hnoncentral hmin y
  · exact commutator_le_frattini_of_isPGroup (p := p)

theorem minimal_noncentral_binary_pow_four_eq_one
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (x : N) : x ^ 4 = 1 := by
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  have hx := minimal_noncentral_prime_power_mem_commutator Nat.prime_two N hN hnoncentral hmin x
  have hh : (x ^ 2) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hx
  simpa only [← pow_mul] using hh

end Kourovka2135
