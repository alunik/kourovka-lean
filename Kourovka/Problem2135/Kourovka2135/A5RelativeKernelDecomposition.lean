import Kourovka2135.A5RelativeModuleCertificate
import Kourovka2135.MinimalAbelianKernelAction
import Kourovka2135.MinimalQuotientModules

/-! The universal A5 module certificate on actual normal binary subgroups.
The action is constructed from ambient conjugation and the supplied quotient
map; no abstract representation or module decomposition is assumed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.A5RelativeKernelDecomposition

open scoped IsMulCommutative commutatorElement
open MinimalAbelianKernelAction

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
variable (pi : G →* A5RelativeModuleCertificate.A5) (hpi : Function.Surjective pi)

include hpi

/-- The actual conjugation action descends through the actual A5 quotient. -/
theorem exists_difference_fixed [IsElementaryAbelian 2 N]
    (hcentral : ∀ (r : pi.ker) (x : N), (MulAut.conjNormal (r : G) : MulAut N) x = x)
    (u c : G) (hu : pi u = A5RelativeModuleCertificate.u)
    (hc : pi c = A5RelativeModuleCertificate.w) (n : N) :
    ∃ x z : N, n = (MulAut.conjNormal c x * x⁻¹) * z ∧
      (MulAut.conjNormal u : MulAut N) z = z := by
  let ρ := conjugationRepresentation N 2
  have htriv : ∀ (r : pi.ker) (x : Additive N), ρ (r : G) x = x := by
    intro r x
    exact congrArg Additive.ofMul (hcentral r x.toMul)
  let σ := quotientRepresentation ρ pi.ker htriv
  let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  let τ := σ.comp e.symm.toMonoidHom
  have he (g : G) : e.symm (pi g) = QuotientGroup.mk' pi.ker g := by
    change e.symm (e (QuotientGroup.mk' pi.ker g)) = _
    exact e.symm_apply_apply _
  have hτ (g : G) (x : Additive N) : τ (pi g) x = ρ g x := by
    change σ (e.symm (pi g)) x = _
    rw [he]
    rfl
  obtain ⟨x, z, hn, hz⟩ := A5RelativeModuleCertificate.exists_decomposition τ (Additive.ofMul n)
  rw [← hc, hτ] at hn
  rw [← hu, hτ] at hz
  refine ⟨x.toMul, z.toMul, ?_, ?_⟩
  · have h := congrArg Additive.toMul hn
    simp only [toMul_add, toMul_sub, toMul_ofMul, div_eq_mul_inv] at h
    change n = (MulAut.conjNormal c x.toMul * x.toMul⁻¹) * z.toMul at h
    exact h
  · exact congrArg Additive.toMul hz

/-- One relative commutator factor and one centralizing factor suffice for every kernel element. -/
theorem exists_commutator_fixed [IsElementaryAbelian 2 N]
    (hcentral : ∀ (r : pi.ker) (x : N), (MulAut.conjNormal (r : G) : MulAut N) x = x)
    (u b c : G) (hu : pi u = A5RelativeModuleCertificate.u)
    (hc : pi c = A5RelativeModuleCertificate.w) (n : N) :
    ∃ d z : N, n = d * z ∧
      (d : G) ∈ ⁅N, Subgroup.closure ({b, c} : Set G)⁆ ∧ Commute u (z : G) := by
  obtain ⟨x, z, hn, hz⟩ := exists_difference_fixed N pi hpi hcentral u c hu hc n
  refine ⟨MulAut.conjNormal c x * x⁻¹, z, hn, ?_, ?_⟩
  · rw [Subgroup.commutator_comm]
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure (Set.mem_insert_of_mem b (Set.mem_singleton c))) x.property
    exact h
  · have h := congrArg Subtype.val hz
    change u * (z : G) * u⁻¹ = z at h
    exact (mul_inv_eq_iff_eq_mul).mp h

/-- Minimal noncentrality and the Frattini condition discharge the action-kernel premise. -/
theorem exists_commutator_fixed_of_minimal
    [Finite G] [Group.IsPerfect G] [IsMulCommutative N]
    (hN : IsPGroup 2 N) (hnc : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G)
    (u b c : G) (hu : pi u = A5RelativeModuleCertificate.u)
    (hc : pi c = A5RelativeModuleCertificate.w) (n : N) :
    ∃ d z : N, n = d * z ∧
      (d : G) ∈ ⁅N, Subgroup.closure ({b, c} : Set G)⁆ ∧ Commute u (z : G) := by
  let : IsElementaryAbelian 2 N :=
    isElementaryAbelian_of_minimal_noncentral Nat.prime_two N hN hnc hmin
  exact exists_commutator_fixed N pi hpi
    (frattini_pSubgroup_centralizes Nat.prime_two N hN hnc hmin pi.ker hR hF)
    u b c hu hc n

end Kourovka2135.A5RelativeKernelDecomposition
