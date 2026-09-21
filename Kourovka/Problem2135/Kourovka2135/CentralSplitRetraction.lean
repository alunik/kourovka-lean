import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Prod

/-! Actual retraction onto the central kernel of a split group homomorphism.

All maps are constructed from the supplied homomorphic section. No finite,
perfect, commutative ambient-group, or representation hypothesis is used.
-/

set_option autoImplicit false

namespace Kourovka2135.CentralSplitRetraction

universe u v
variable {E : Type u} {Q : Type v} [Group E] [Group Q]
variable (π : E →* Q) (s : Q →* E) (hπs : π.comp s = MonoidHom.id Q)

include hπs in
/-- The homomorphism-section identity evaluated at an actual quotient element. -/
theorem section_apply (q : Q) : π (s q) = q :=
  DFunLike.congr_fun hπs q

/-- The explicit kernel coordinate determined by the actual section. -/
def remainder (e : E) : E := e * (s (π e))⁻¹

include hπs in
/-- The explicit coordinate really belongs to the actual kernel. -/
theorem remainder_mem_ker (e : E) : remainder π s e ∈ π.ker := by
  apply MonoidHom.mem_ker.mpr
  simp only [remainder, map_mul, map_inv, section_apply π s hπs, mul_inv_cancel]

/-- The original element is kernel coordinate times its section representative. -/
theorem remainder_mul_section (e : E) : remainder π s e * s (π e) = e := by
  simp only [remainder, mul_assoc, inv_mul_cancel, mul_one]

variable (hcentral : π.ker ≤ Subgroup.center E)

/-- Centrality makes the explicit kernel coordinate multiplicative. -/
def retraction : E →* π.ker where
  toFun e := ⟨remainder π s e, remainder_mem_ker π s hπs e⟩
  map_one' := by
    apply Subtype.ext
    simp only [remainder, map_one, inv_one, mul_one, Subgroup.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    change a * b * (s (π (a * b)))⁻¹ =
      (a * (s (π a))⁻¹) * (b * (s (π b))⁻¹)
    rw [map_mul, map_mul, mul_inv_rev]
    have hc : (s (π a))⁻¹ * (b * (s (π b))⁻¹) =
        (b * (s (π b))⁻¹) * (s (π a))⁻¹ :=
      Subgroup.mem_center_iff.mp (hcentral (remainder_mem_ker π s hπs b))
        ((s (π a))⁻¹)
    calc
      a * b * ((s (π b))⁻¹ * (s (π a))⁻¹) =
          a * ((b * (s (π b))⁻¹) * (s (π a))⁻¹) := by
            simp only [mul_assoc]
      _ = a * ((s (π a))⁻¹ * (b * (s (π b))⁻¹)) := congrArg (a * ·) hc.symm
      _ = (a * (s (π a))⁻¹) * (b * (s (π b))⁻¹) := by
        simp only [mul_assoc]

/-- The bundled retraction retains the specified concrete formula. -/
@[simp] theorem retraction_coe (e : E) :
    (retraction π s hπs hcentral e : E) = e * (s (π e))⁻¹ := rfl

/-- On every actual kernel element the retraction is the identity. -/
@[simp] theorem retraction_ker (k : π.ker) :
    retraction π s hπs hcentral (k : E) = k := by
  apply Subtype.ext
  simp only [retraction_coe, MonoidHom.mem_ker.mp k.property, map_one, inv_one, mul_one]

/-- Every actual section value has trivial kernel coordinate. -/
@[simp] theorem retraction_section (q : Q) :
    retraction π s hπs hcentral (s q) = 1 := by
  apply Subtype.ext
  simp only [retraction_coe, section_apply π s hπs, mul_inv_cancel, Subgroup.coe_one]

/-- The actual kernel inclusion has the constructed homomorphism as a left inverse. -/
theorem retraction_comp_subtype :
    (retraction π s hπs hcentral).comp π.ker.subtype = MonoidHom.id π.ker := by
  apply MonoidHom.ext
  intro k
  exact retraction_ker π s hπs hcentral k

/-- The actual retraction is surjective. -/
theorem retraction_surjective : Function.Surjective (retraction π s hπs hcentral) := by
  intro k
  exact ⟨(k : E), retraction_ker π s hπs hcentral k⟩

/-- The explicit central split extension is the direct product of its actual kernel and quotient. -/
def productEquiv : E ≃* π.ker × Q where
  toFun e := (retraction π s hπs hcentral e, π e)
  invFun p := (p.1 : E) * s p.2
  left_inv e := remainder_mul_section π s e
  right_inv p := by
    apply Prod.ext
    · change retraction π s hπs hcentral ((p.1 : E) * s p.2) = p.1
      rw [map_mul, retraction_ker, retraction_section, mul_one]
    · change π ((p.1 : E) * s p.2) = p.2
      rw [map_mul, MonoidHom.mem_ker.mp p.1.property, section_apply π s hπs, one_mul]
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (retraction π s hπs hcentral) a b
    · exact map_mul π a b

/-- The forward direct-product coordinate consists of the actual retraction and original quotient map. -/
@[simp] theorem productEquiv_apply (e : E) :
    productEquiv π s hπs hcentral e = (retraction π s hπs hcentral e, π e) := rfl

/-- The inverse direct-product map multiplies the actual kernel and section representatives. -/
@[simp] theorem productEquiv_symm_apply (k : π.ker) (q : Q) :
    (productEquiv π s hπs hcentral).symm (k, q) = (k : E) * s q := rfl

end Kourovka2135.CentralSplitRetraction
