import Kourovka2135.CentralAutomorphismTorsion

/-! Normality and actual conjugation equivariance of central-automorphism coordinates.

The actual subgroup is normal in all automorphisms. On automorphisms fixing
the center pointwise, conjugation becomes inverse precomposition by the
actual quotient action. This is the action of linHom with trivial target.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CentralAutomorphismEquivariance

open scoped IsMulCommutative
open CentralAutomorphismCoordinate (fixesCenterSubgroup centralSubgroup)

variable (N : Type u) [Group N]

/-- Pointwise fixing the characteristic center is preserved by all automorphism conjugations. -/
instance fixesCenterSubgroup_normal : (fixesCenterSubgroup N).Normal where
  conj_mem t ht a := by
    intro z
    change a (t (a.symm (z : N))) = z
    have hz := ht (Subgroup.centerCongr a.symm z)
    change t (a.symm (z : N)) = a.symm (z : N) at hz
    rw [hz, MulEquiv.apply_symm_apply]

/-- Both defining conditions of the actual central subgroup are normal conditions. -/
instance centralSubgroup_normal : (centralSubgroup N).Normal := by
  change (fixesCenterSubgroup N ⊓ (characteristicQuotientAut (Subgroup.center N)).ker).Normal
  infer_instance

/-- The actual normal-subgroup conjugation action of all automorphisms. -/
def conjugation : MulAut N →* MulAut (centralSubgroup N) := MulAut.conjNormal

@[simp] theorem conjugation_coe (a : MulAut N) (t : centralSubgroup N) :
    (conjugation N a t : MulAut N) = a * (t : MulAut N) * a⁻¹ := rfl

/-- On actual representatives, center-fixed conjugation is inverse precomposition. -/
theorem coordinate_conjugation_mk (a : fixesCenterSubgroup N)
    (t : centralSubgroup N) (n : N) :
    CentralAutomorphismCoordinate.coordinate N (conjugation N (a : MulAut N) t)
        (QuotientGroup.mk' (Subgroup.center N) n) =
      CentralAutomorphismCoordinate.coordinate N t
        (characteristicQuotientAut (Subgroup.center N) (a : MulAut N)⁻¹
          (QuotientGroup.mk' (Subgroup.center N) n)) := by
  apply Subtype.ext
  change (a : MulAut N) ((t : MulAut N) ((a : MulAut N).symm n)) * n⁻¹ =
    (t : MulAut N) ((a : MulAut N).symm n) * ((a : MulAut N).symm n)⁻¹
  have h := a.property
    (CentralAutomorphismCoordinate.pointCoordinate t ((a : MulAut N).symm n))
  change (a : MulAut N)
      ((t : MulAut N) ((a : MulAut N).symm n) * ((a : MulAut N).symm n)⁻¹) =
    (t : MulAut N) ((a : MulAut N).symm n) * ((a : MulAut N).symm n)⁻¹ at h
  rw [map_mul, map_inv, MulEquiv.apply_symm_apply] at h
  exact h

/-- The exact actual quotient formula has the inverse-precomposition direction of linHom. -/
theorem coordinate_conjugation (a : fixesCenterSubgroup N)
    (t : centralSubgroup N) (q : N ⧸ Subgroup.center N) :
    CentralAutomorphismCoordinate.coordinate N (conjugation N (a : MulAut N) t) q =
      CentralAutomorphismCoordinate.coordinate N t
        (characteristicQuotientAut (Subgroup.center N) (a : MulAut N)⁻¹ q) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) q
  exact coordinate_conjugation_mk N a t n

variable (p : ℕ)
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]

/-- The actual Ω_p-center coordinates satisfy the same conjugation identity. -/
theorem torsionCoordinate_conjugation (a : fixesCenterSubgroup N)
    (t : centralSubgroup N) (q : N ⧸ Subgroup.center N) :
    CentralAutomorphismTorsion.coordinate N p (conjugation N (a : MulAut N) t) q =
      CentralAutomorphismTorsion.coordinate N p t
        (characteristicQuotientAut (Subgroup.center N) (a : MulAut N)⁻¹ q) := by
  apply Subtype.ext
  exact coordinate_conjugation N a t q

variable [Fact p.Prime]

/-- The exact linear-coordinate identity, using the actual quotient automorphism. -/
theorem linearCoordinate_conjugation (a : fixesCenterSubgroup N)
    (t : centralSubgroup N) :
    CentralAutomorphismTorsion.linearCoordinate N p
        (Additive.ofMul (conjugation N (a : MulAut N) t)) =
      (CentralAutomorphismTorsion.linearCoordinate N p (Additive.ofMul t)).comp
        (((characteristicQuotientAut (Subgroup.center N) (a : MulAut N)⁻¹).toMonoidHom.toAdditive).toZModLinearMap p) := by
  apply LinearMap.ext
  intro q
  change CentralAutomorphismTorsion.coordinate N p (conjugation N (a : MulAut N) t) q.toMul =
    CentralAutomorphismTorsion.coordinate N p t
      (characteristicQuotientAut (Subgroup.center N) (a : MulAut N)⁻¹ q.toMul)
  exact torsionCoordinate_conjugation N p a t q.toMul

end Kourovka2135.CentralAutomorphismEquivariance
