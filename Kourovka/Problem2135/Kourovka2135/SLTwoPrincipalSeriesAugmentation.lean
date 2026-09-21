import Kourovka2135.SLTwoPrincipalSeriesDelta
import Mathlib.FieldTheory.Finite.Basic

/-! The weight-zero homogeneous-function
module is the actual permutation module on the normalized projective line.
Its coordinate sum is invariant under every SL2 matrix; no group-generation
certificate is used. Constants split the augmentation for finite parameter
fields, since their cardinality is zero in the coefficient field.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoPrincipalSeries

open SLTwoHomogeneousFunctions

section ProjectiveCoordinates
variable {F : Type v} [Field F]

/-- Infinity and the affine chart, indexed by `Option F`. -/
def projectiveRepresentative : Option F → Point F
  | none => infinity F
  | some t => affine t

/-- Normalize an actual nonzero row vector to its projective coordinate. -/
def projectiveIndex (z : Point F) : Option F := by
  classical
  exact if z.val 0 = 0 then none else some (z.val 1 / z.val 0)

@[simp] theorem projectiveIndex_representative (t : Option F) :
    projectiveIndex (projectiveRepresentative t) = t := by
  cases t <;> simp [projectiveIndex, projectiveRepresentative]

@[simp] theorem projectiveIndex_scale (a : Fˣ) (z : Point F) :
    projectiveIndex (scalePoint a z) = projectiveIndex z := by
  classical
  by_cases hz : z.val 0 = 0
  · simp [projectiveIndex, hz]
  · have hax : (a : F) * z.val 0 ≠ 0 := mul_ne_zero a.ne_zero hz
    simp [projectiveIndex, hz, hax, mul_div_mul_left _ _ a.ne_zero]

/-- Projective coordinates are insensitive to the normalization before an SL2 action. -/
theorem projectiveIndex_action_representative (g : SLTwo.SL2 F) (z : Point F) :
    projectiveIndex (pointAction g z) =
      projectiveIndex (pointAction g (projectiveRepresentative (projectiveIndex z))) := by
  classical
  by_cases hz : z.val 0 = 0
  · have hrep : projectiveRepresentative (projectiveIndex z) = infinity F := by
      simp [projectiveIndex, hz, projectiveRepresentative]
    rw [hrep]
    calc
      projectiveIndex (pointAction g z) =
          projectiveIndex (pointAction g (scalePoint
            (Units.mk0 (z.val 1) (second_ne_zero_of_first_eq_zero z hz)) (infinity F))) :=
        congrArg (fun w => projectiveIndex (pointAction g w)) (eq_scale_infinity z hz)
      _ = _ := by rw [pointAction_scale, projectiveIndex_scale]
  · have hrep : projectiveRepresentative (projectiveIndex z) = affine (z.val 1 / z.val 0) := by
      simp [projectiveIndex, hz, projectiveRepresentative]
    rw [hrep]
    calc
      projectiveIndex (pointAction g z) =
          projectiveIndex (pointAction g (scalePoint
            (Units.mk0 (z.val 0) hz) (affine (z.val 1 / z.val 0)))) :=
        congrArg (fun w => projectiveIndex (pointAction g w)) (eq_scale_affine z hz)
      _ = _ := by rw [pointAction_scale, projectiveIndex_scale]

/-- The actual projective permutation induced by right row-vector multiplication. -/
def projectivePermutation (g : SLTwo.SL2 F) : Equiv.Perm (Option F) where
  toFun t := projectiveIndex (pointAction g (projectiveRepresentative t))
  invFun t := projectiveIndex (pointAction g⁻¹ (projectiveRepresentative t))
  left_inv t := by
    dsimp only
    rw [← projectiveIndex_action_representative, ← pointAction_mul, mul_inv_cancel,
      pointAction_one, projectiveIndex_representative]
  right_inv t := by
    dsimp only
    rw [← projectiveIndex_action_representative, ← pointAction_mul, inv_mul_cancel,
      pointAction_one, projectiveIndex_representative]

end ProjectiveCoordinates

section WeightZero
variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k)

/-- Weight-zero values depend only on the actual normalized projective coordinate. -/
theorem weightZero_apply_representative (h : Carrier k σ 0) (z : Point F) :
    h z = h (projectiveRepresentative (projectiveIndex z)) := by
  classical
  by_cases hz : z.val 0 = 0
  · simp only [projectiveIndex, hz, ite_true, projectiveRepresentative]
    calc
      h z = h (scalePoint
          (Units.mk0 (z.val 1) (second_ne_zero_of_first_eq_zero z hz)) (infinity F)) :=
        congrArg h (eq_scale_infinity z hz)
      _ = _ := by simp [homogeneous]
  · simp only [projectiveIndex, hz, ite_false, projectiveRepresentative]
    calc
      h z = h (scalePoint (Units.mk0 (z.val 0) hz) (affine (z.val 1 / z.val 0))) :=
        congrArg h (eq_scale_affine z hz)
      _ = _ := by simp [homogeneous]

/-- Constant functions give an actual k-linear map into the weight-zero module. -/
def constants : k →ₗ[k] Carrier k σ 0 where
  toFun c := ⟨fun _ => c, by intro a z; simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem constants_apply (c : k) (z : Point F) : constants k σ c z = c := rfl

@[simp] theorem representation_constants (g : SLTwo.SL2 F) (c : k) :
    representation k σ 0 g (constants k σ c) = constants k σ c := rfl

variable [Fintype F]

/-- Sum of all q+1 actual projective coordinates. -/
def augmentation : Carrier k σ 0 →ₗ[k] k where
  toFun h := ∑ t : Option F, h (projectiveRepresentative t)
  map_add' h h' := by simp [Finset.sum_add_distrib]
  map_smul' c h := by
    change (∑ t : Option F, c • h (projectiveRepresentative t)) =
      c • (∑ t : Option F, h (projectiveRepresentative t))
    rw [Finset.smul_sum]

theorem augmentation_coordinates (h : Carrier k σ 0) :
    augmentation k σ h = (coordinates k σ 0 h).1 +
      ∑ t : F, (coordinates k σ 0 h).2 t := by
  simp [augmentation, Fintype.sum_option, projectiveRepresentative]

/-- Full SL2 invariance follows from the actual projective permutation. -/
theorem augmentation_action (g : SLTwo.SL2 F) (h : Carrier k σ 0) :
    augmentation k σ (representation k σ 0 g h) = augmentation k σ h := by
  change (∑ t : Option F, h (pointAction g (projectiveRepresentative t))) = _
  calc
    _ = ∑ t : Option F, h (projectiveRepresentative (projectivePermutation g t)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact weightZero_apply_representative k σ h _
    _ = _ := Fintype.sum_equiv (projectivePermutation g)
      (fun t => h (projectiveRepresentative (projectivePermutation g t)))
      (fun t => h (projectiveRepresentative t)) (fun _ => rfl)

@[simp] theorem augmentation_constants (c : k) :
    augmentation k σ (constants k σ c) = c := by
  have hq : (Fintype.card F : k) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg σ (Nat.cast_card_eq_zero F)
  simp [augmentation, Fintype.sum_option, projectiveRepresentative, hq]

theorem augmentation_surjective : Function.Surjective (augmentation k σ) :=
  fun c => ⟨constants k σ c, augmentation_constants k σ c⟩

/-- The actual augmentation kernel is stable under every SL2 matrix. -/
theorem augmentation_ker_stable (g : SLTwo.SL2 F) (h : Carrier k σ 0)
    (hh : h ∈ LinearMap.ker (augmentation k σ)) :
    representation k σ 0 g h ∈ LinearMap.ker (augmentation k σ) := by
  change augmentation k σ (representation k σ 0 g h) = 0
  rw [augmentation_action]
  exact hh

end WeightZero
end Kourovka2135.SLTwoPrincipalSeries
