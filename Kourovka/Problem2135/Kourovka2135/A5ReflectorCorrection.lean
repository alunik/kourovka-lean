import Kourovka2135.A5RelativeKernelDecomposition
import Kourovka2135.RelativeAbelianCommutatorFiber

/-! A normalizer-preserving correction step for the A5 reflector induction.
An actual kernel decomposition makes the commutator fiber meet a coset of
the centralizer of the chosen order-three element. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.A5ReflectorCorrection

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Multiplying an inverter by an element centralizing u preserves inversion. -/
theorem inverts_mul_right (a z u : G) (ha : a⁻¹ * u * a = u⁻¹)
    (hz : Commute u z) : (a * z)⁻¹ * u * (a * z) = u⁻¹ := by
  calc
    _ = z⁻¹ * (a⁻¹ * u * a) * z := by group
    _ = z⁻¹ * (u⁻¹ * z) := by rw [ha, mul_assoc]
    _ = z⁻¹ * (z * u⁻¹) := by rw [hz.inv_left.eq]
    _ = u⁻¹ := inv_mul_cancel_left _ _

/-- Correct both commutator inputs inside N while retaining the actual inversion action. -/
theorem exists_corrections_inverting
    [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hN : IsPGroup 2 N) (hnc : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (pi : G →* A5RelativeModuleCertificate.A5) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G)
    (u b c a : G) (hu : pi u = A5RelativeModuleCertificate.u)
    (hc : pi c = A5RelativeModuleCertificate.w)
    (ha : a⁻¹ * u * a = u⁻¹)
    (hcoset : (paperCommutator b c)⁻¹ * a ∈ N) :
    ∃ x y : N,
      (paperCommutator (b * x) (c * y))⁻¹ * u *
        paperCommutator (b * x) (c * y) = u⁻¹ := by
  let n : N := ⟨(paperCommutator b c)⁻¹ * a, hcoset⟩
  obtain ⟨d, z, hn, hd, hz⟩ :=
    A5RelativeKernelDecomposition.exists_commutator_fixed_of_minimal N pi hpi
      hN hnc hmin hR hF u b c hu hc n
  obtain ⟨x, y, hxy⟩ :=
    RelativeAbelianCommutatorFiber.exists_paperCommutator_mul_eq_of_mem_commutator N b c d hd
  have hprod : paperCommutator b c * (d : G) = a * (z : G)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    have h := congrArg Subtype.val hn
    change (paperCommutator b c)⁻¹ * a = (d : G) * (z : G) at h
    rw [mul_assoc, ← h, mul_inv_cancel_left]
  refine ⟨x, y, ?_⟩
  rw [hxy, hprod]
  exact inverts_mul_right a (z : G)⁻¹ u ha hz.inv_right

end Kourovka2135.A5ReflectorCorrection
