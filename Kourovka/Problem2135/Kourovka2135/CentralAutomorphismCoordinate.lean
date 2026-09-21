import Kourovka2135.NormalQuotientRepresentation
import Mathlib.Algebra.Group.Hom.Instances

/-! Actual coordinates for automorphisms fixing the center and central quotient.

The subgroup is defined directly inside MulAut N. Its coordinate at nZ(N)
is t(n)n⁻¹, an actual central element. This is a homomorphism on the quotient,
and the resulting coordinate map is injective and respects multiplication.
The center itself is not assumed elementary abelian. If the central quotient
has exponent dividing p, the coordinates (and this automorphism subgroup)
have exponent dividing p.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CentralAutomorphismCoordinate

open scoped IsMulCommutative

variable (N : Type u) [Group N]

/-- Automorphisms fixing the actual center pointwise. -/
def fixesCenterSubgroup : Subgroup (MulAut N) where
  carrier := {a | ∀ z : Subgroup.center N, a z = z}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb z := by
    change a (b (z : N)) = z
    rw [hb z, ha z]
  inv_mem' {a} ha z := by
    apply a.injective
    change a (a.symm (z : N)) = a (z : N)
    rw [MulEquiv.apply_symm_apply, ha z]

/-- The actual subgroup fixing Z(N) pointwise and acting identically on N/Z(N). -/
def centralSubgroup : Subgroup (MulAut N) :=
  fixesCenterSubgroup N ⊓ (characteristicQuotientAut (Subgroup.center N)).ker

variable {N}

/-- The first defining condition acts on actual central elements. -/
theorem fixes_center (a : centralSubgroup N) (z : Subgroup.center N) :
    (a : MulAut N) z = z :=
  a.property.1 z

/-- The second defining condition fixes the actual quotient class of every element. -/
theorem quotient_apply (a : centralSubgroup N) (n : N) :
    QuotientGroup.mk' (Subgroup.center N) ((a : MulAut N) n) =
      QuotientGroup.mk' (Subgroup.center N) n := by
  have h : characteristicQuotientAut (Subgroup.center N) (a : MulAut N) = 1 :=
    a.property.2
  exact congrArg (fun d : MulAut (N ⧸ Subgroup.center N) =>
    d (QuotientGroup.mk' (Subgroup.center N) n)) h

/-- The actual multiplicative difference belongs to the center. -/
theorem difference_mem_center (a : centralSubgroup N) (n : N) :
    (a : MulAut N) n * n⁻¹ ∈ Subgroup.center N := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (Subgroup.center N) ((a : MulAut N) n * n⁻¹) = 1
  rw [map_mul, map_inv, quotient_apply, mul_inv_cancel]

/-- The multiplicative difference is a genuine group homomorphism into the center. -/
def pointCoordinate (a : centralSubgroup N) : N →* Subgroup.center N where
  toFun n := ⟨(a : MulAut N) n * n⁻¹, difference_mem_center a n⟩
  map_one' := by
    apply Subtype.ext
    change (a : MulAut N) 1 * (1 : N)⁻¹ = 1
    rw [map_one, inv_one, mul_one]
  map_mul' n m := by
    apply Subtype.ext
    change (a : MulAut N) (n * m) * (n * m)⁻¹ =
      ((a : MulAut N) n * n⁻¹) * ((a : MulAut N) m * m⁻¹)
    rw [map_mul, mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp (difference_mem_center a m) n⁻¹
    calc
      (a : MulAut N) n * (a : MulAut N) m * (m⁻¹ * n⁻¹) =
          (a : MulAut N) n * (((a : MulAut N) m * m⁻¹) * n⁻¹) := by
        simp only [mul_assoc]
      _ = (a : MulAut N) n * (n⁻¹ * ((a : MulAut N) m * m⁻¹)) := by rw [← hc]
      _ = ((a : MulAut N) n * n⁻¹) * ((a : MulAut N) m * m⁻¹) := by
        simp only [mul_assoc]

@[simp] theorem pointCoordinate_coe (a : centralSubgroup N) (n : N) :
    (pointCoordinate a n : N) = (a : MulAut N) n * n⁻¹ := rfl

/-- Coordinates recover the automorphism by central multiplication. -/
theorem pointCoordinate_mul_self (a : centralSubgroup N) (n : N) :
    (pointCoordinate a n : N) * n = (a : MulAut N) n := by
  change ((a : MulAut N) n * n⁻¹) * n = (a : MulAut N) n
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Fixing the center pointwise makes the coordinate vanish on the center. -/
theorem center_le_ker_pointCoordinate (a : centralSubgroup N) :
    Subgroup.center N ≤ (pointCoordinate a).ker := by
  intro z hz
  change pointCoordinate a z = 1
  apply Subtype.ext
  change (a : MulAut N) z * z⁻¹ = 1
  rw [fixes_center a ⟨z, hz⟩, mul_inv_cancel]

/-- The actual coordinate descends through the central quotient. -/
def quotientCoordinate (a : centralSubgroup N) :
    (N ⧸ Subgroup.center N) →* Subgroup.center N :=
  QuotientGroup.lift (Subgroup.center N) (pointCoordinate a) (center_le_ker_pointCoordinate a)

@[simp] theorem quotientCoordinate_mk (a : centralSubgroup N) (n : N) :
    quotientCoordinate a (QuotientGroup.mk' (Subgroup.center N) n) = pointCoordinate a n := rfl

/-- Composition of actual automorphisms becomes multiplication of central coordinates. -/
theorem pointCoordinate_mul (a b : centralSubgroup N) (n : N) :
    pointCoordinate (a * b) n = pointCoordinate a n * pointCoordinate b n := by
  apply Subtype.ext
  change (a : MulAut N) ((b : MulAut N) n) * n⁻¹ =
    (pointCoordinate a n : N) * (pointCoordinate b n : N)
  calc
    (a : MulAut N) ((b : MulAut N) n) * n⁻¹ =
        (a : MulAut N) ((pointCoordinate b n : N) * n) * n⁻¹ :=
      congrArg (fun x : N => (a : MulAut N) x * n⁻¹) (pointCoordinate_mul_self b n).symm
    _ = (pointCoordinate b n : N) * ((a : MulAut N) n * n⁻¹) := by
      rw [map_mul, fixes_center]
      simp only [mul_assoc]
    _ = (pointCoordinate b n : N) * (pointCoordinate a n : N) := rfl
    _ = (pointCoordinate a n : N) * (pointCoordinate b n : N) :=
      congrArg Subtype.val (mul_comm (pointCoordinate b n) (pointCoordinate a n))

variable (N)

/-- An actual injective coordinate homomorphism into homomorphisms to the whole center. -/
def coordinate : centralSubgroup N →* ((N ⧸ Subgroup.center N) →* Subgroup.center N) where
  toFun := quotientCoordinate
  map_one' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) q
    apply Subtype.ext
    change n * n⁻¹ = 1
    exact mul_inv_cancel n
  map_mul' a b := by
    apply MonoidHom.ext
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) q
    exact pointCoordinate_mul a b n

@[simp] theorem coordinate_mk (a : centralSubgroup N) (n : N) :
    coordinate N a (QuotientGroup.mk' (Subgroup.center N) n) = pointCoordinate a n := rfl

/-- The actual coordinate determines every value of the automorphism. -/
theorem coordinate_injective : Function.Injective (coordinate N) := by
  intro a b h
  apply Subtype.ext
  apply MulEquiv.ext
  intro n
  have hv := congrArg (fun c : (N ⧸ Subgroup.center N) →* Subgroup.center N =>
    (c (QuotientGroup.mk' (Subgroup.center N) n) : N)) h
  change (a : MulAut N) n * n⁻¹ = (b : MulAut N) n * n⁻¹ at hv
  exact mul_right_cancel hv

/-- This actual subgroup is commutative, without assuming the center has exponent p. -/
instance centralSubgroup_isMulCommutative : IsMulCommutative (centralSubgroup N) :=
  ⟨⟨fun a b => coordinate_injective N (by rw [map_mul, map_mul, mul_comm])⟩⟩

/-- Additive coordinates into homomorphisms from the actual central quotient to the actual center. -/
def additiveCoordinate :
    Additive (centralSubgroup N) →+
      (Additive (N ⧸ Subgroup.center N) →+ Additive (Subgroup.center N)) where
  toFun a := (coordinate N a.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro q
    change Additive.ofMul (coordinate N 1 q.toMul) = 0
    rw [map_one]
    rfl
  map_add' a b := by
    apply AddMonoidHom.ext
    intro q
    change Additive.ofMul (coordinate N (a.toMul * b.toMul) q.toMul) =
      Additive.ofMul (coordinate N a.toMul q.toMul * coordinate N b.toMul q.toMul)
    rw [map_mul]
    rfl

/-- The additive coordinate remains injective on the actual automorphism subgroup. -/
theorem additiveCoordinate_injective : Function.Injective (additiveCoordinate N) := by
  intro a b h
  change a.toMul = b.toMul
  apply coordinate_injective N
  apply MonoidHom.ext
  intro q
  exact congrArg Additive.toMul
    (congrArg (fun c : Additive (N ⧸ Subgroup.center N) →+ Additive (Subgroup.center N) =>
      c (Additive.ofMul q)) h)

/-- Every coordinate has exponent dividing p when the central quotient does. -/
theorem coordinate_pow_eq_one (p : ℕ) [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    (a : centralSubgroup N) (q : N ⧸ Subgroup.center N) :
    coordinate N a q ^ p = 1 := by
  rw [← map_pow]
  have hq := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p (N ⧸ Subgroup.center N)) q
  rw [hq, map_one]

/-- The actual automorphism subgroup itself has exponent dividing p. -/
theorem centralSubgroup_pow_eq_one (p : ℕ)
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] (a : centralSubgroup N) :
    a ^ p = 1 := by
  apply coordinate_injective N
  apply MonoidHom.ext
  intro q
  rw [map_pow, map_one]
  exact coordinate_pow_eq_one N p a q

/-- Elementary abelianity of the quotient implies elementary abelianity of this actual subgroup.
The whole center need not be elementary abelian. -/
instance centralSubgroup_isElementaryAbelian (p : ℕ)
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] :
    IsElementaryAbelian p (centralSubgroup N) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (centralSubgroup_pow_eq_one N p)

end Kourovka2135.CentralAutomorphismCoordinate
