import Kourovka2135.SLTwoUnipotent
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Homogeneous functions on nonzero two-dimensional vectors.

The action is actual transpose-precomposition, implemented as row-vector
multiplication. Evaluation at infinity and the affine representatives gives
an explicit linear equivalence with `k × (F → k)`. The construction uses no
finite-field, irreducibility, or representation-classification hypothesis.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoHomogeneousFunctions

open Matrix
open scoped MatrixGroups

/-- The native domain consists of actual nonzero vectors. -/
abbrev Point (F : Type v) [Field F] := {z : Fin 2 → F // z ≠ 0}

section Points
variable {F : Type v} [Field F]

/-- Scaling a nonzero vector by a unit preserves nonzeroness. -/
def scalePoint (a : Fˣ) (z : Point F) : Point F :=
  ⟨(a : F) • z.val, smul_ne_zero a.ne_zero z.property⟩

@[simp] theorem scalePoint_apply (a : Fˣ) (z : Point F) (i : Fin 2) :
    (scalePoint a z).val i = (a : F) * z.val i := rfl

/-- Right multiplication of row vectors is transpose multiplication on column vectors. -/
def pointAction (g : SLTwo.SL2 F) (z : Point F) : Point F :=
  ⟨z.val ᵥ* g.val, by
    intro hz
    apply z.property
    have h := congrArg (fun w : Fin 2 → F => w ᵥ* (g⁻¹).val) hz
    simpa only [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
      Matrix.zero_vecMul] using h⟩

@[simp] theorem pointAction_val (g : SLTwo.SL2 F) (z : Point F) :
    (pointAction g z).val = z.val ᵥ* g.val := rfl

theorem pointAction_transpose (g : SLTwo.SL2 F) (z : Point F) :
    (pointAction g z).val = g.val.transpose *ᵥ z.val :=
  (Matrix.mulVec_transpose g.val z.val).symm

@[simp] theorem pointAction_one (z : Point F) : pointAction 1 z = z := by
  apply Subtype.ext
  exact Matrix.vecMul_one z.val

/-- Reversal here is what makes precomposition a left representation. -/
theorem pointAction_mul (g h : SLTwo.SL2 F) (z : Point F) :
    pointAction (g * h) z = pointAction h (pointAction g z) := by
  apply Subtype.ext
  exact (Matrix.vecMul_vecMul z.val g.val h.val).symm

theorem pointAction_scale (g : SLTwo.SL2 F) (a : Fˣ) (z : Point F) :
    pointAction g (scalePoint a z) = scalePoint a (pointAction g z) := by
  apply Subtype.ext
  exact Matrix.smul_vecMul (a : F) z.val g.val

/-- Infinity in the chosen projective chart. -/
def infinity (F : Type v) [Field F] : Point F :=
  ⟨![0, 1], by
    intro h
    have h₁ := congrFun h 1
    simp at h₁⟩

/-- The affine chart representative at the parameter t. -/
def affine (t : F) : Point F :=
  ⟨![1, t], by
    intro h
    have h₀ := congrFun h 0
    simp at h₀⟩

@[simp] theorem infinity_zero : (infinity F).val 0 = 0 := rfl
@[simp] theorem infinity_one : (infinity F).val 1 = 1 := rfl
@[simp] theorem affine_zero (t : F) : (affine t).val 0 = 1 := rfl
@[simp] theorem affine_one (t : F) : (affine t).val 1 = t := rfl

theorem second_ne_zero_of_first_eq_zero (z : Point F) (hz : z.val 0 = 0) :
    z.val 1 ≠ 0 := by
  intro h₁
  apply z.property
  funext i
  fin_cases i <;> assumption

theorem eq_scale_infinity (z : Point F) (hz : z.val 0 = 0) :
    z = scalePoint (Units.mk0 (z.val 1) (second_ne_zero_of_first_eq_zero z hz)) (infinity F) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [hz]

theorem eq_scale_affine (z : Point F) (hz : z.val 0 ≠ 0) :
    z = scalePoint (Units.mk0 (z.val 0) hz) (affine (z.val 1 / z.val 0)) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · simp
  · simp only [scalePoint_apply, Units.val_mk0]
    exact (mul_div_cancel₀ (z.val 1) hz).symm

theorem pointAction_uni_infinity (b : F) : pointAction (SLTwo.uni b) (infinity F) = infinity F := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [pointAction, infinity, SLTwo.uni_val]

theorem pointAction_uni_affine (b t : F) :
    pointAction (SLTwo.uni b) (affine t) = affine (t + b) := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [pointAction, affine, SLTwo.uni_val,
      add_comm]

theorem pointAction_tor_infinity (a : Fˣ) :
    pointAction (SLTwo.tor a) (infinity F) = scalePoint a⁻¹ (infinity F) := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [pointAction, infinity, scalePoint, SLTwo.tor_val]

theorem pointAction_tor_affine (a : Fˣ) (t : F) :
    pointAction (SLTwo.tor a) (affine t) =
      scalePoint a (affine ((((a⁻¹ : Fˣ) : F) ^ 2) * t)) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · simp [pointAction, affine, scalePoint, SLTwo.tor_val]
  · simp [pointAction, affine, scalePoint, SLTwo.tor_val]
    rw [← inv_pow]
    calc
      _ = ((a : F) * (a : F)⁻¹) * ((a : F)⁻¹ * t) := by simp [a.ne_zero, mul_comm]
      _ = _ := by ring

end Points

section Functions
variable (k : Type u) [Field k] {F : Type v} [Field F] (σ : F →+* k) (n : ℕ)

/-- Actual functions of homogeneous weight n, as a native linear subspace. -/
def space : Submodule k (Point F → k) where
  carrier := {h | ∀ (a : Fˣ) (z : Point F), h (scalePoint a z) = σ (a : F) ^ n * h z}
  zero_mem' := by intro a z; simp
  add_mem' := by
    intro h h' hh hh' a z
    change h (scalePoint a z) + h' (scalePoint a z) = σ (a : F) ^ n * (h z + h' z)
    rw [hh, hh', mul_add]
  smul_mem' := by
    intro c h hh a z
    change c * h (scalePoint a z) = σ (a : F) ^ n * (c * h z)
    rw [hh]
    ring

/-- The underlying homogeneous-function module. -/
abbrev Carrier := ↥(space k σ n)

instance instCoeFun : CoeFun (Carrier k σ n) (fun _ => Point F → k) := ⟨Subtype.val⟩

theorem homogeneous (h : Carrier k σ n) (a : Fˣ) (z : Point F) :
    h (scalePoint a z) = σ (a : F) ^ n * h z := h.property a z

/-- The genuine left SL2 representation by transpose-precomposition. -/
def representation : Representation k (SLTwo.SL2 F) (Carrier k σ n) where
  toFun g :=
    { toFun h := ⟨fun z => h (pointAction g z), by
        intro a z
        change h (pointAction g (scalePoint a z)) = σ (a : F) ^ n * h (pointAction g z)
        rw [pointAction_scale, homogeneous]⟩
      map_add' := by intro h h'; rfl
      map_smul' := by intro c h; rfl }
  map_one' := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext z
    exact congrArg h (pointAction_one z)
  map_mul' g h := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext z
    exact congrArg t (pointAction_mul g h z)

@[simp] theorem representation_apply (g : SLTwo.SL2 F) (h : Carrier k σ n) (z : Point F) :
    representation k σ n g h z = h (pointAction g z) := rfl

/-- Read off infinity and all affine values. -/
def toCoordinates : Carrier k σ n →ₗ[k] k × (F → k) where
  toFun h := (h (infinity F), fun t => h (affine t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reconstruct a homogeneous function from its two projective charts. -/
def reconstruct (p : k × (F → k)) (z : Point F) : k := by
  classical
  exact if z.val 0 = 0 then σ (z.val 1) ^ n * p.1
    else σ (z.val 0) ^ n * p.2 (z.val 1 / z.val 0)

theorem reconstruct_homogeneous (p : k × (F → k)) (a : Fˣ) (z : Point F) :
    reconstruct k σ n p (scalePoint a z) = σ (a : F) ^ n * reconstruct k σ n p z := by
  classical
  by_cases hz : z.val 0 = 0
  · simp [reconstruct, hz, map_mul, mul_pow, mul_assoc]
  · have hax : (a : F) * z.val 0 ≠ 0 := mul_ne_zero a.ne_zero hz
    have hratio : ((a : F) * z.val 1) / ((a : F) * z.val 0) = z.val 1 / z.val 0 := by
      exact mul_div_mul_left _ _ a.ne_zero
    simp [reconstruct, hz, hax, hratio, map_mul, mul_pow, mul_assoc]

/-- The explicit inverse coordinate map is k-linear. -/
def fromCoordinates : (k × (F → k)) →ₗ[k] Carrier k σ n where
  toFun p := ⟨reconstruct k σ n p, reconstruct_homogeneous k σ n p⟩
  map_add' p q := by
    apply Subtype.ext
    funext z
    by_cases hz : z.val 0 = 0 <;> simp [reconstruct, hz, mul_add]
  map_smul' c p := by
    apply Subtype.ext
    funext z
    by_cases hz : z.val 0 = 0 <;> simp [reconstruct, hz, mul_left_comm]

@[simp] theorem fromCoordinates_infinity (p : k × (F → k)) :
    fromCoordinates k σ n p (infinity F) = p.1 := by
  simp [fromCoordinates, reconstruct]

@[simp] theorem fromCoordinates_affine (p : k × (F → k)) (t : F) :
    fromCoordinates k σ n p (affine t) = p.2 t := by
  simp [fromCoordinates, reconstruct]

theorem fromCoordinates_toCoordinates (h : Carrier k σ n) :
    fromCoordinates k σ n (toCoordinates k σ n h) = h := by
  classical
  apply Subtype.ext
  funext z
  change (if z.val 0 = 0 then σ (z.val 1) ^ n * h (infinity F)
    else σ (z.val 0) ^ n * h (affine (z.val 1 / z.val 0))) = h z
  by_cases hz : z.val 0 = 0
  · have hh : h z = σ (z.val 1) ^ n * h (infinity F) := by
      calc
        h z = h (scalePoint
            (Units.mk0 (z.val 1) (second_ne_zero_of_first_eq_zero z hz)) (infinity F)) :=
          congrArg h (eq_scale_infinity z hz)
        _ = _ := homogeneous k σ n h _ _
    rw [ite_eq_left hz]
    exact hh.symm
  · have hh : h z = σ (z.val 0) ^ n * h (affine (z.val 1 / z.val 0)) := by
      calc
        h z = h (scalePoint (Units.mk0 (z.val 0) hz) (affine (z.val 1 / z.val 0))) :=
          congrArg h (eq_scale_affine z hz)
        _ = _ := homogeneous k σ n h _ _
    rw [ite_eq_right hz]
    exact hh.symm

@[simp] theorem toCoordinates_fromCoordinates (p : k × (F → k)) :
    toCoordinates k σ n (fromCoordinates k σ n p) = p := by
  apply Prod.ext
  · exact fromCoordinates_infinity k σ n p
  · funext t
    exact fromCoordinates_affine k σ n p t

/-- The actual homogeneous-function module has explicit projective coordinates. -/
def coordinates : Carrier k σ n ≃ₗ[k] k × (F → k) where
  __ := toCoordinates k σ n
  invFun := fromCoordinates k σ n
  left_inv := fromCoordinates_toCoordinates k σ n
  right_inv := toCoordinates_fromCoordinates k σ n

@[simp] theorem coordinates_fst (h : Carrier k σ n) :
    (coordinates k σ n h).1 = h (infinity F) := rfl

@[simp] theorem coordinates_snd (h : Carrier k σ n) (t : F) :
    (coordinates k σ n h).2 t = h (affine t) := rfl

/-- Actual upper unipotents translate the affine parameter and fix infinity. -/
theorem coordinates_uni (b : F) (h : Carrier k σ n) :
    coordinates k σ n (representation k σ n (SLTwo.uni b) h) =
      ((coordinates k σ n h).1, fun t => (coordinates k σ n h).2 (t + b)) := by
  apply Prod.ext
  · simp only [coordinates_fst, representation_apply, pointAction_uni_infinity]
  · funext t
    simp only [coordinates_snd, representation_apply, pointAction_uni_affine]

/-- Actual diagonal elements give the positive and negative homogeneous weights. -/
theorem coordinates_tor (a : Fˣ) (h : Carrier k σ n) :
    coordinates k σ n (representation k σ n (SLTwo.tor a) h) =
      (σ ((a⁻¹ : Fˣ) : F) ^ n * (coordinates k σ n h).1,
        fun t => σ (a : F) ^ n *
          (coordinates k σ n h).2 ((((a⁻¹ : Fˣ) : F) ^ 2) * t)) := by
  apply Prod.ext
  · simp only [coordinates_fst, representation_apply, pointAction_tor_infinity,
      homogeneous]
  · funext t
    simp only [coordinates_snd, representation_apply, pointAction_tor_affine,
      homogeneous]

end Functions
end Kourovka2135.SLTwoHomogeneousFunctions
