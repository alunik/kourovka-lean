import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.PGroup

/-! A normal p-subgroup acts trivially on an irreducible finite representation
whose vector set has cardinality divisible by p. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} [Group G]
variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [Finite V]

theorem normal_pSubgroup_acts_trivially_of_invariant_submodules
    {p : ℕ} (hp : p.Prime) (ρ : Representation k G V)
    (hirr : ∀ W : Submodule k V,
      (∀ g x, x ∈ W → ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcard : p ∣ Nat.card V) (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
    (r : R) (x : V) : ρ (r : G) x = x := by
  let : Fact p.Prime := ⟨hp⟩
  let W : Submodule k V := {
    carrier := {x | ∀ r : R, ρ (r : G) x = x}
    zero_mem' := fun _ => map_zero _
    add_mem' := fun ha hb r => by rw [map_add, ha r, hb r]
    smul_mem' := fun a x hx r => by rw [map_smul, hx r] }
  have hW : ∀ g x, x ∈ W → ρ g x ∈ W := by
    intro g x hx r
    have hr : g⁻¹ * (r : G) * g ∈ R := by
      simpa only [inv_inv] using (inferInstance : R.Normal).conj_mem r r.property g⁻¹
    change ρ (r : G) (ρ g x) = ρ g x
    rw [← Module.End.mul_apply, ← map_mul,
      show (r : G) * g = g * (g⁻¹ * (r : G) * g) by group,
      map_mul, Module.End.mul_apply, hx ⟨_, hr⟩]
  let : MulAction R V := {
    smul := fun r x => ρ (r : G) x
    one_smul := fun x => by change ρ 1 x = x; rw [map_one]; rfl
    mul_smul := fun a b x => by
      change ρ ((a : G) * (b : G)) x = ρ (a : G) (ρ (b : G) x)
      rw [map_mul]
      rfl }
  have hzero : (0 : V) ∈ MulAction.fixedPoints R V := by
    intro r
    exact map_zero (ρ (r : G))
  obtain ⟨b, hb, h0b⟩ :=
    hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero
  have hbW : b ∈ W := hb
  have hWtop : W = ⊤ := by
    rcases hirr W hW with hbot | htop
    · have hb0 : b = 0 := by
        have : b ∈ (⊥ : Submodule k V) := hbot ▸ hbW
        exact this
      exact (h0b hb0.symm).elim
    · exact htop
  have hx : x ∈ W := by rw [hWtop]; trivial
  exact hx r

end Kourovka2135
