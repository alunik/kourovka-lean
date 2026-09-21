import Kourovka2135.MinimalAbelianizationAction
import Mathlib.RepresentationTheory.Invariants

/-! Quotient-group representations and the vanishing of invariant linear
functionals on a minimal kernel's abelianization. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

def quotientRepresentation {k : Type*} [Semiring k]
    {M : Type v} [AddCommMonoid M] [Module k M]
    (ρ : Representation k G M) (R : Subgroup G) [R.Normal]
    (hR : ∀ (r : R) x, ρ (r : G) x = x) : Representation k (G ⧸ R) M :=
  QuotientGroup.lift R ρ (by
    intro r hr
    apply LinearMap.ext
    exact hR ⟨r, hr⟩)

@[simp] theorem quotientRepresentation_apply_mk {k : Type*} [Semiring k]
    {M : Type v} [AddCommMonoid M] [Module k M]
    (ρ : Representation k G M) (R : Subgroup G) [R.Normal]
    (hR : ∀ (r : R) x, ρ (r : G) x = x) (g : G) (x : M) :
    quotientRepresentation ρ R hR (QuotientGroup.mk' R g) x = ρ g x := rfl

theorem invariant_functional_eq_zero_of_moving_kernel
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ K)]
    (ell : Module.Dual (ZMod p) (Additive (N ⧸ K)))
    (hell : ∀ g x, ell (normalQuotientRepresentation N K p g x) = ell x) : ell = 0 := by
  let q := QuotientGroup.mk' K
  let f : N →* Multiplicative (ZMod p) := {
    toFun := fun a => Multiplicative.ofAdd (ell (Additive.ofMul (q a)))
    map_one' := by
      change ell (Additive.ofMul (q 1)) = 0
      rw [map_one]
      exact map_zero ell
    map_mul' := fun a b => by
      change ell (Additive.ofMul (q (a * b))) =
        ell (Additive.ofMul (q a)) + ell (Additive.ofMul (q b))
      rw [map_mul, ofMul_mul, map_add] }
  have hf (g : G) (a : N) : f (MulAut.conjNormal g a) = f a := by
    exact hell g (Additive.ofMul (q a))
  have hkill : ⁅N, (⊤ : Subgroup G)⁆ ≤ f.ker.map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    let b : N := ⟨a, ha⟩
    refine ⟨b * MulAut.conjNormal g b⁻¹, ?_, ?_⟩
    · change f (b * MulAut.conjNormal g b⁻¹) = 1
      rw [map_mul, hf, map_inv, mul_inv_cancel]
    · change a * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      simp only [mul_assoc]
  rw [hmove] at hkill
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K x.toMul
  obtain ⟨b, hb, hba⟩ := hkill a.property
  have hba' : b = a := Subtype.ext hba
  subst b
  change ell (Additive.ofMul (q a)) = 0 at hb
  change q a = x.toMul at ha
  change ell (Additive.ofMul x.toMul) = 0
  rw [← ha]
  exact hb

theorem normal_quotient_dual_invariants_eq_bot
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ K)] :
    (normalQuotientRepresentation N K p).dual.invariants = ⊥ := by
  apply bot_unique
  intro ell hell
  apply invariant_functional_eq_zero_of_moving_kernel N K hmove p ell
  intro g x
  have hh := congrArg (fun f : Module.Dual (ZMod p) (Additive (N ⧸ K)) => f x)
    (hell g⁻¹)
  change ell (normalQuotientRepresentation N K p g⁻¹⁻¹ x) = ell x at hh
  simpa only [inv_inv] using hh

theorem quotientRepresentation_dual_invariants_eq_bot {k : Type*} [CommRing k]
    {M : Type v} [AddCommGroup M] [Module k M]
    (ρ : Representation k G M) (R : Subgroup G) [R.Normal]
    (hR : ∀ (r : R) x, ρ (r : G) x = x) (hρ : ρ.dual.invariants = ⊥) :
    (quotientRepresentation ρ R hR).dual.invariants = ⊥ := by
  apply bot_unique
  intro ell hell
  apply hρ.le
  intro g
  have hh := hell (QuotientGroup.mk' R g)
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f : Module.Dual k M => f x) hh
  change ell (quotientRepresentation ρ R hR ((QuotientGroup.mk' R g)⁻¹) x) = ell x at hx
  rw [← map_inv, quotientRepresentation_apply_mk] at hx
  exact hx

end Kourovka2135
