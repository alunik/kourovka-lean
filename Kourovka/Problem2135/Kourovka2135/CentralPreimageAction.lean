import Kourovka2135.CentralClassThreePairing
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Lift-independent conjugation through a central quotient. An actual
quotient action normalizing a subgroup induces an action on its full
preimage, fixes the central kernel, and commutes with the projection.
No complement, chosen-order lift, or extension-splitting assumption is used. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.CentralPreimageAction

variable {E S T : Type*} [Group E] [Group S] [Group T]
variable (pi : E →* S) (hpi : Function.Surjective pi) (hker : pi.ker ≤ Subgroup.center E)

/-- Inner conjugation is independent of the lift through a central kernel. -/
def quotientConjugation : S →* MulAut E :=
  pi.liftOfSurjective hpi ⟨MulAut.conj, by
    intro x hx
    apply MulEquiv.ext
    intro y
    change x * y * x⁻¹ = y
    have h := Subgroup.mem_center_iff.mp (hker hx) y
    rw [← h, mul_inv_cancel_right]⟩

theorem quotientConjugation_apply (x y : E) :
    quotientConjugation pi hpi hker (pi x) y = x * y * x⁻¹ := by
  simp only [quotientConjugation, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem projection_conjugation (s : S) (x : E) :
    pi (quotientConjugation pi hpi hker s x) = s * pi x * s⁻¹ := by
  obtain ⟨y, rfl⟩ := hpi s
  rw [quotientConjugation_apply, map_mul, map_mul, map_inv]

theorem quotientConjugation_fixes_kernel (s : S) (x : E) (hx : x ∈ pi.ker) :
    quotientConjugation pi hpi hker s x = x := by
  obtain ⟨y, rfl⟩ := hpi s
  rw [quotientConjugation_apply]
  have h := Subgroup.mem_center_iff.mp (hker hx) y
  rw [h, mul_inv_cancel_right]

variable (U : Subgroup S) (tau : T →* S) (beta : T →* MulAut U)
variable (hbeta : ∀ t x, (beta t x : S) = tau t * (x : S) * (tau t)⁻¹)

abbrev Preimage := U.comap pi

/-- Projection onto the full quotient subgroup. -/
def projection : Preimage pi U →* U where
  toFun x := ⟨pi x.val, x.property⟩
  map_one' := Subtype.ext pi.map_one
  map_mul' x y := Subtype.ext (pi.map_mul x.val y.val)

include hpi in
theorem projection_surjective : Function.Surjective (projection pi U) := by
  intro x
  obtain ⟨y, hy⟩ := hpi x.val
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change pi y ∈ U
  rw [hy]
  exact x.property

include hker in
theorem projection_kernel_central : (projection pi U).ker ≤ Subgroup.center (Preimage pi U) := by
  intro x hx
  have hxpi : pi x.val = 1 := congrArg Subtype.val hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxpi) y.val

def ambientAction : T →* MulAut E := (quotientConjugation pi hpi hker).comp tau

include hbeta in
theorem ambientAction_mem (t : T) (x : Preimage pi U) :
    ambientAction pi hpi hker tau t x.val ∈ Preimage pi U := by
  change pi (quotientConjugation pi hpi hker (tau t) x.val) ∈ U
  rw [projection_conjugation]
  change tau t * (projection pi U x : S) * (tau t)⁻¹ ∈ U
  rw [← hbeta t (projection pi U x)]
  exact (beta t (projection pi U x)).property

/-- Actual restriction of the quotient conjugation to the full preimage. -/
def preimageAut (t : T) : MulAut (Preimage pi U) where
  toFun x := ⟨ambientAction pi hpi hker tau t x.val, ambientAction_mem pi hpi hker U tau beta hbeta t x⟩
  invFun x := ⟨ambientAction pi hpi hker tau t⁻¹ x.val, ambientAction_mem pi hpi hker U tau beta hbeta t⁻¹ x⟩
  left_inv x := by
    apply Subtype.ext
    change ambientAction pi hpi hker tau t⁻¹ (ambientAction pi hpi hker tau t x.val) = x.val
    rw [map_inv]
    exact (ambientAction pi hpi hker tau t).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    change ambientAction pi hpi hker tau t (ambientAction pi hpi hker tau t⁻¹ x.val) = x.val
    rw [map_inv]
    exact (ambientAction pi hpi hker tau t).apply_symm_apply x.val
  map_mul' x y := Subtype.ext ((ambientAction pi hpi hker tau t).map_mul x.val y.val)

def action : T →* MulAut (Preimage pi U) where
  toFun := preimageAut pi hpi hker U tau beta hbeta
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ambientAction pi hpi hker tau 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' t s := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ambientAction pi hpi hker tau (t * s) x.val =
      ambientAction pi hpi hker tau t (ambientAction pi hpi hker tau s x.val)
    rw [map_mul]
    rfl

theorem action_projection (t : T) (x : Preimage pi U) :
    projection pi U (action pi hpi hker U tau beta hbeta t x) = beta t (projection pi U x) := by
  apply Subtype.ext
  change pi (quotientConjugation pi hpi hker (tau t) x.val) = (beta t (projection pi U x) : S)
  rw [projection_conjugation, hbeta]
  rfl

theorem action_fixes_kernel (t : T) (x : Preimage pi U) (hx : x ∈ (projection pi U).ker) :
    action pi hpi hker U tau beta hbeta t x = x := by
  apply Subtype.ext
  exact quotientConjugation_fixes_kernel pi hpi hker (tau t) x.val (congrArg Subtype.val hx)

end Kourovka2135.CentralPreimageAction
