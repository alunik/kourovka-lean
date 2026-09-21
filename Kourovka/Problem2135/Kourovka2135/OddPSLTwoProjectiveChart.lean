import Kourovka2135.SLTwoUnipotent
import Mathlib.LinearAlgebra.Projectivization.Action

/-! Coordinates for the actual PSL2 projective action.

The affine point x is represented by the column (x,1), and infinity by (1,0).
Mathlib's genuine action of SL2 modulo its center supplies the group action;
the chart only reindexes it. Upper unipotents translate the affine coordinate,
and the diagonal torus multiplies it by a square. These facts hold over every
field; no embedding into a coefficient field is involved.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoProjectiveChart

open scoped MatrixGroups LinearAlgebra.Projectivization Matrix

variable (F : Type*) [Field F]

abbrev Q := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F
abbrev Point := ℙ F (Fin 2 → F)

/-- Native column representatives for the affine chart and infinity. -/
def representative : Option F → Fin 2 → F
  | none => ![1, 0]
  | some x => ![x, 1]

theorem representative_ne_zero (x : Option F) : representative F x ≠ 0 := by
  cases x with
  | none =>
      intro h
      have h0 := congrFun h 0
      simp [representative] at h0
  | some x =>
      intro h
      have h1 := congrFun h 1
      simp [representative] at h1

def point (x : Option F) : Point F :=
  Projectivization.mk F (representative F x) (representative_ne_zero F x)

theorem point_injective : Function.Injective (point F) := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y =>
          have ha0 : a = 0 := by simpa [representative] using congrFun ha 1
          have h01 : (0 : F) = 1 := by
            simpa [representative, ha0] using congrFun ha 0
          exact (zero_ne_one h01).elim
  | some x =>
      cases y with
      | none =>
          have h01 : (0 : F) = 1 := by
            simpa [representative] using congrFun ha 1
          exact (zero_ne_one h01).elim
      | some y =>
          have ha1 : a = 1 := by simpa [representative] using congrFun ha 1
          have hyx : y = x := by simpa [representative, ha1] using congrFun ha 0
          exact congrArg some hyx.symm

theorem point_surjective : Function.Surjective (point F) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
      by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          ext i
          fin_cases i <;> simp [h0, h1]
        refine ⟨none, ?_⟩
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
        refine ⟨(v 0)⁻¹, ?_⟩
        ext i
        fin_cases i <;> simp [representative, h0, h1]
      · refine ⟨some (v 0 / v 1), ?_⟩
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
        refine ⟨(v 1)⁻¹, ?_⟩
        ext i
        fin_cases i <;> simp [representative, h1, div_eq_mul_inv, mul_comm]

/-- The actual projective line is the affine chart with one point at infinity. -/
def pointEquiv : Option F ≃ Point F :=
  Equiv.ofBijective (point F) ⟨point_injective F, point_surjective F⟩

@[simp] theorem pointEquiv_apply (x : Option F) : pointEquiv F x = point F x := rfl

/-- The native quotient map from the actual special linear group. -/
def quotient : SLTwo.SL2 F →* Q F := QuotientGroup.mk' (Subgroup.center (SLTwo.SL2 F))

/-- Reindex mathlib's faithful projective action by the explicit affine chart. -/
def permutation : Q F →* Equiv.Perm (Option F) where
  toFun g := (pointEquiv F).symm.permCongr (Projectivization.PSLAction.toPermHom g)
  map_one' := by
    apply Equiv.ext
    intro x
    change (pointEquiv F).symm
      (Projectivization.PSLAction.toPermHom (1 : Q F) (pointEquiv F x)) = x
    rw [map_one]
    exact (pointEquiv F).symm_apply_apply x
  map_mul' g h := by ext x; simp [Equiv.permCongr_apply]

instance : MulAction (Q F) (Option F) := MulAction.compHom _ (permutation F)

theorem point_smul (g : Q F) (x : Option F) :
    point F (g • x) = g • point F x := by
  change (pointEquiv F) ((pointEquiv F).symm (g • pointEquiv F x)) = _
  exact (pointEquiv F).apply_symm_apply _

instance : MulAction.IsPretransitive (Q F) (Option F) where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := Q F) (point F x) (point F y)
    refine ⟨g, point_injective F ?_⟩
    rw [point_smul]
    exact hg

@[simp] theorem uni_smul_none (t : F) :
    quotient F (SLTwo.uni t) • (none : Option F) = none := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F ((SLTwo.uni t).val.mulVec (representative F none)) _ =
    Projectivization.mk F (representative F none) _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;>
    simp [representative, SLTwo.uni, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem uni_smul_some (t x : F) :
    quotient F (SLTwo.uni t) • (some x : Option F) = some (x + t) := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F ((SLTwo.uni t).val.mulVec (representative F (some x))) _ =
    Projectivization.mk F (representative F (some (x + t))) _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;>
    simp [representative, SLTwo.uni, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem tor_smul_none (r : Fˣ) :
    quotient F (SLTwo.tor r) • (none : Option F) = none := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F ((SLTwo.tor r).val.mulVec (representative F none)) _ =
    Projectivization.mk F (representative F none) _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨(r : F), ?_⟩
  ext i
  fin_cases i <;>
    simp [representative, SLTwo.tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem tor_smul_some (r : Fˣ) (x : F) :
    quotient F (SLTwo.tor r) • (some x : Option F) = some ((r : F) ^ 2 * x) := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F ((SLTwo.tor r).val.mulVec (representative F (some x))) _ =
    Projectivization.mk F (representative F (some ((r : F) ^ 2 * x))) _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨((r⁻¹ : Fˣ) : F), ?_⟩
  ext i
  fin_cases i <;>
    simp [representative, SLTwo.tor, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      pow_two, mul_assoc, mul_comm]

end Kourovka2135.OddPSLTwoProjectiveChart
