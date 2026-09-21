import Kourovka2135.CentralClassTwoAbelianPairing
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Ring.Parity

/-! Odd-order averaging of the actual derived-group commutator pairing.
The norm is a finite sum of the actual induced automorphisms. Vanishing of
invariant biadditive forms forces every fixed derived element to be trivial.
No semisimplicity or representation decomposition is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Kourovka2135.CentralClassTwoOddAverage

open scoped IsMulCommutative BigOperators
open CentralClassTwoAbelianPairing

section Norm
variable {T : Type u} {D : Type v} [Group T] [Fintype T] [CommGroup D]

def norm (rho : T →* MulAut D) : Additive D →+ Additive D :=
  ∑ t : T, (rho t).toAdditive.toAddMonoidHom

theorem norm_apply (rho : T →* MulAut D) (d : Additive D) :
    norm rho d = ∑ t : T, Additive.ofMul (rho t d.toMul) := by
  simp [norm]

/-- Right translation permutes the summands of the actual norm. -/
theorem norm_action (rho : T →* MulAut D) (s : T) (d : Additive D) :
    norm rho (Additive.ofMul (rho s d.toMul)) = norm rho d := by
  calc
    norm rho (Additive.ofMul (rho s d.toMul)) =
        ∑ t : T, Additive.ofMul (rho (t * s) d.toMul) := by
      rw [norm_apply]
      apply Finset.sum_congr rfl
      intro t _
      change Additive.ofMul (rho t (rho s d.toMul)) = Additive.ofMul (rho (t * s) d.toMul)
      rw [map_mul]
      rfl
    _ = ∑ t : T, Additive.ofMul (rho t d.toMul) :=
      Equiv.sum_comp (Equiv.mulRight s) (fun t => Additive.ofMul (rho t d.toMul))
    _ = norm rho d := (norm_apply rho d).symm

theorem norm_fixed [IsElementaryAbelian 2 D] (rho : T →* MulAut D)
    (hodd : Odd (Nat.card T)) (d : Additive D)
    (hfix : ∀ t : T, rho t d.toMul = d.toMul) : norm rho d = d := by
  rw [norm_apply]
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card T • d = d
  have htwo : 2 • d = 0 := by
    exact toMul_eq_one.mp (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 D) d.toMul)
  have hmod : Fintype.card T % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  rw [nsmul_eq_mod_nsmul (Fintype.card T) htwo, hmod, one_nsmul]

end Norm

variable {G : Type u} {Q : Type v} {T : Type w}
variable [Group G] [CommGroup Q] [Group T]
variable (psi : G →* Q) (hpsi : Function.Surjective psi)
variable (hker : psi.ker ≤ Subgroup.center G) (hD : commutator G ≤ Subgroup.center G)
variable (alpha : T →* MulAut G) (beta : T →* MulAut Q)

def derivedAction : T →* MulAut (commutator G) :=
  (MulAut.characteristic (commutator G)).comp alpha

@[simp] theorem derivedAction_coe (t : T) (d : commutator G) :
    (derivedAction alpha t d : G) = alpha t d.val := rfl

variable [Fintype T] [IsElementaryAbelian 2 (commutator G)]

def averagedPairing : Additive Q →+ (Additive Q →+ Additive (commutator G)) where
  toFun q := (norm (derivedAction alpha)).comp (biadditive psi hpsi hker hD q)
  map_zero' := by ext r; simp
  map_add' q r := by ext s; simp

@[simp] theorem averagedPairing_apply (q r : Additive Q) :
    averagedPairing psi hpsi hker hD alpha q r =
      norm (derivedAction alpha) (biadditive psi hpsi hker hD q r) := rfl

theorem averagedPairing_invariant
    (hcompat : ∀ t x, psi (alpha t x) = beta t (psi x))
    (t : T) (q r : Additive Q) :
    averagedPairing psi hpsi hker hD alpha ((beta t).toAdditive q) ((beta t).toAdditive r) =
      averagedPairing psi hpsi hker hD alpha q r := by
  rw [averagedPairing_apply, averagedPairing_apply,
    biadditive_equivariant psi hpsi hker hD (alpha t) (beta t) (hcompat t)]
  exact norm_action (derivedAction alpha) t (biadditive psi hpsi hker hD q r)

include hpsi hker hD in
theorem norm_eq_zero_of_invariant_forms
    (hcompat : ∀ t x, psi (alpha t x) = beta t (psi x))
    (hvanish : ∀ B : Additive Q →+ (Additive Q →+ Additive (commutator G)),
      (∀ t q r, B ((beta t).toAdditive q) ((beta t).toAdditive r) = B q r) → B = 0) :
    norm (derivedAction alpha) = 0 := by
  have hzero := hvanish (averagedPairing psi hpsi hker hD alpha)
    (averagedPairing_invariant psi hpsi hker hD alpha beta hcompat)
  apply addHom_eq_zero_of_pairing psi hpsi hker hD
  intro q r
  have h := congrArg (fun B : Additive Q →+ (Additive Q →+ Additive (commutator G)) => B q r) hzero
  exact h

include hpsi hker hD in
/-- Odd multiplicity is the identity on exponent-two elements; the zero
norm therefore annihilates every actual torus-fixed derived element. -/
theorem fixed_derived_eq_one
    (hcompat : ∀ t x, psi (alpha t x) = beta t (psi x))
    (hodd : Odd (Nat.card T))
    (hvanish : ∀ B : Additive Q →+ (Additive Q →+ Additive (commutator G)),
      (∀ t q r, B ((beta t).toAdditive q) ((beta t).toAdditive r) = B q r) → B = 0)
    (d : commutator G) (hfix : ∀ t : T, derivedAction alpha t d = d) : d = 1 := by
  have hzero : norm (derivedAction alpha) (Additive.ofMul d) = 0 := by
    rw [norm_eq_zero_of_invariant_forms psi hpsi hker hD alpha beta hcompat hvanish]
    rfl
  have hsame := norm_fixed (derivedAction alpha) hodd (Additive.ofMul d) hfix
  exact congrArg Additive.toMul (hsame.symm.trans hzero)

include hpsi hker hD in
theorem fixed_mem_commutator_eq_one
    (hcompat : ∀ t x, psi (alpha t x) = beta t (psi x))
    (hodd : Odd (Nat.card T))
    (hvanish : ∀ B : Additive Q →+ (Additive Q →+ Additive (commutator G)),
      (∀ t q r, B ((beta t).toAdditive q) ((beta t).toAdditive r) = B q r) → B = 0)
    (d : G) (hd : d ∈ commutator G) (hfix : ∀ t : T, alpha t d = d) : d = 1 := by
  have h := fixed_derived_eq_one psi hpsi hker hD alpha beta hcompat hodd hvanish
    ⟨d, hd⟩ (fun t => Subtype.ext (hfix t))
  exact congrArg Subtype.val h

end Kourovka2135.CentralClassTwoOddAverage
