import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Prod

/-! The actual determinant-one intertwiner group and the normal graph of N.

The group is an explicit subgroup of G × Aut_k(V), cut out by the actual
intertwining equations and determinant one. Its projection, operator map,
and graph are actual homomorphisms. This structural package does not assert
surjectivity or finiteness of the cover, or identify its scalar kernel.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.DeterminantOneIntertwinerGroup

section Coefficient
variable {k : Type v} [Field k] {A : Type u} [Group A]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k A V)

/-- The given representation as an actual homomorphism to linear automorphisms. -/
def coefficientAut : A →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp ρ.asGroupHom

@[simp] theorem coefficientAut_toLinearMap (a : A) :
    (coefficientAut ρ a).toLinearMap = ρ a := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.asGroupHom a)).toLinearMap = _
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Representation.asGroupHom_apply]

@[simp] theorem coefficientAut_apply (a : A) (v : V) : coefficientAut ρ a v = ρ a v :=
  congrArg (fun T : V →ₗ[k] V => T v) (coefficientAut_toLinearMap ρ a)

/-- The determinant of the actual coefficient automorphism has the original linear-map determinant. -/
theorem coefficientAut_det_val (a : A) :
    (LinearEquiv.det (coefficientAut ρ a) : k) = LinearMap.det (ρ a) := by
  rw [LinearEquiv.coe_det, coefficientAut_toLinearMap]

/-- Unit-valued and field-valued determinant-one premises agree for the actual original action. -/
theorem coefficientAut_det_eq_one_iff (a : A) :
    LinearEquiv.det (coefficientAut ρ a) = 1 ↔ LinearMap.det (ρ a) = 1 := by
  rw [← Units.val_inj, coefficientAut_det_val, Units.val_one]

end Coefficient

variable {k : Type v} [Field k] {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k N V)

/-- The actual composition identity for an operator above g. -/
def Intertwines (g : G) (T : V ≃ₗ[k] V) : Prop :=
  ∀ n : N, T.toLinearMap.comp (ρ n) =
    (ρ (MulAut.conjNormal g n)).comp T.toLinearMap

/-- The same actual intertwining condition in the group of linear automorphisms. -/
theorem intertwines_iff_aut (g : G) (T : V ≃ₗ[k] V) :
    Intertwines N ρ g T ↔
      ∀ n : N, T * coefficientAut ρ n = coefficientAut ρ (MulAut.conjNormal g n) * T := by
  constructor
  · intro h n
    apply LinearEquiv.toLinearMap_injective
    change T.toLinearMap.comp (coefficientAut ρ n).toLinearMap =
      (coefficientAut ρ (MulAut.conjNormal g n)).toLinearMap.comp T.toLinearMap
    simpa only [coefficientAut_toLinearMap] using h n
  · intro h n
    have hn := congrArg (fun e : V ≃ₗ[k] V => e.toLinearMap) (h n)
    change T.toLinearMap.comp (coefficientAut ρ n).toLinearMap =
      (coefficientAut ρ (MulAut.conjNormal g n)).toLinearMap.comp T.toLinearMap at hn
    simpa only [coefficientAut_toLinearMap] using hn

/-- The identity operator lies above the identity group element. -/
theorem intertwines_one : Intertwines N ρ 1 1 := by
  apply (intertwines_iff_aut N ρ 1 1).mpr
  intro n
  simp

/-- Multiplication of actual intertwiners follows the actual ambient product. -/
theorem intertwines_mul {g h : G} {T U : V ≃ₗ[k] V}
    (hT : Intertwines N ρ g T) (hU : Intertwines N ρ h U) :
    Intertwines N ρ (g * h) (T * U) := by
  rw [intertwines_iff_aut] at hT hU ⊢
  intro n
  have hc : MulAut.conjNormal (g * h) n =
      MulAut.conjNormal g (MulAut.conjNormal h n) := by
    rw [map_mul]
    rfl
  calc
    (T * U) * coefficientAut ρ n = T * (U * coefficientAut ρ n) := mul_assoc _ _ _
    _ = T * (coefficientAut ρ (MulAut.conjNormal h n) * U) :=
      congrArg (T * ·) (hU n)
    _ = (T * coefficientAut ρ (MulAut.conjNormal h n)) * U := (mul_assoc _ _ _).symm
    _ = (coefficientAut ρ (MulAut.conjNormal g (MulAut.conjNormal h n)) * T) * U :=
      congrArg (· * U) (hT (MulAut.conjNormal h n))
    _ = coefficientAut ρ (MulAut.conjNormal (g * h) n) * (T * U) := by
      rw [hc]
      exact mul_assoc _ _ _

/-- The inverse of an actual intertwiner lies above the actual inverse group element. -/
theorem intertwines_inv {g : G} {T : V ≃ₗ[k] V} (hT : Intertwines N ρ g T) :
    Intertwines N ρ g⁻¹ T⁻¹ := by
  rw [intertwines_iff_aut] at hT ⊢
  intro n
  have hc : MulAut.conjNormal g (MulAut.conjNormal g⁻¹ n) = n := by
    rw [map_inv]
    exact (MulAut.conjNormal g : MulAut N).apply_symm_apply n
  have hm := hT (MulAut.conjNormal g⁻¹ n)
  rw [hc] at hm
  calc
    T⁻¹ * coefficientAut ρ n =
        T⁻¹ * ((coefficientAut ρ n * T) * T⁻¹) := by simp only [mul_inv_cancel_right]
    _ = T⁻¹ * ((T * coefficientAut ρ (MulAut.conjNormal g⁻¹ n)) * T⁻¹) := by rw [← hm]
    _ = coefficientAut ρ (MulAut.conjNormal g⁻¹ n) * T⁻¹ := by
      simp only [mul_assoc, inv_mul_cancel_left]

/-- The actual determinant-one intertwiner subgroup of G × Aut_k(V). -/
def coverSubgroup : Subgroup (G × (V ≃ₗ[k] V)) where
  carrier a := Intertwines N ρ a.1 a.2 ∧ LinearEquiv.det a.2 = 1
  one_mem' := ⟨intertwines_one N ρ, map_one LinearEquiv.det⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨intertwines_mul N ρ ha.1 hb.1, ?_⟩
    change LinearEquiv.det (a.2 * b.2) = 1
    rw [map_mul, ha.2, hb.2, mul_one]
  inv_mem' := by
    intro a ha
    refine ⟨intertwines_inv N ρ ha.1, ?_⟩
    change LinearEquiv.det a.2⁻¹ = 1
    rw [map_inv, ha.2, inv_one]

/-- Elements of the actual subgroup, used as the cover group. -/
abbrev Carrier := coverSubgroup N ρ

@[simp] theorem mem_coverSubgroup (g : G) (T : V ≃ₗ[k] V) :
    (g, T) ∈ coverSubgroup N ρ ↔ Intertwines N ρ g T ∧ LinearEquiv.det T = 1 := Iff.rfl

/-- The actual first projection of the intertwiner group. -/
def projection : Carrier N ρ →* G :=
  (MonoidHom.fst G (V ≃ₗ[k] V)).comp (coverSubgroup N ρ).subtype

/-- The actual second projection, recording the linear operator. -/
def operator : Carrier N ρ →* (V ≃ₗ[k] V) :=
  (MonoidHom.snd G (V ≃ₗ[k] V)).comp (coverSubgroup N ρ).subtype

@[simp] theorem projection_apply (a : Carrier N ρ) : projection N ρ a = a.val.1 := rfl
@[simp] theorem operator_apply (a : Carrier N ρ) : operator N ρ a = a.val.2 := rfl

/-- Every actual cover element satisfies the requested composition identity. -/
theorem operator_intertwines (a : Carrier N ρ) (n : N) :
    (operator N ρ a).toLinearMap.comp (ρ n) =
      (ρ (MulAut.conjNormal (projection N ρ a) n)).comp (operator N ρ a).toLinearMap :=
  a.property.1 n

/-- Every actual cover operator has determinant one. -/
@[simp] theorem operator_det (a : Carrier N ρ) : LinearEquiv.det (operator N ρ a) = 1 :=
  a.property.2

/-- The actual conjugation formula for the operator of a cover element. -/
theorem operator_conjugation (a : Carrier N ρ) (n : N) :
    operator N ρ a * coefficientAut ρ n * (operator N ρ a)⁻¹ =
      coefficientAut ρ (MulAut.conjNormal (projection N ρ a) n) := by
  have h := (intertwines_iff_aut N ρ (projection N ρ a) (operator N ρ a)).mp a.property.1 n
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- Each original coefficient operator implements actual inner conjugation by its own element. -/
theorem coefficientAut_intertwines (n : N) :
    Intertwines N ρ (n : G) (coefficientAut ρ n) := by
  apply (intertwines_iff_aut N ρ (n : G) (coefficientAut ρ n)).mpr
  intro m
  have hc : MulAut.conjNormal (n : G) m = n * m * n⁻¹ := Subtype.ext rfl
  rw [hc, map_mul, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

variable (hdet : ∀ n : N, LinearEquiv.det (coefficientAut ρ n) = 1)

/-- The graph of the original action, on its original space, as an actual homomorphism. -/
def graph : N →* Carrier N ρ where
  toFun n := ⟨((n : G), coefficientAut ρ n), coefficientAut_intertwines N ρ n, hdet n⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_one (coefficientAut ρ)
  map_mul' n m := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_mul (coefficientAut ρ) n m

/-- The graph remembers the actual subgroup element in its first coordinate. -/
@[simp] theorem projection_graph (n : N) : projection N ρ (graph N ρ hdet n) = (n : G) := rfl

/-- The graph retains the original coefficient operator exactly. -/
@[simp] theorem operator_graph (n : N) : operator N ρ (graph N ρ hdet n) = coefficientAut ρ n := rfl

/-- Graph injectivity does not require the representation to be faithful. -/
theorem graph_injective : Function.Injective (graph N ρ hdet) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (projection N ρ) h

/-- Conjugating the actual graph element gives the actual graph of the conjugated element. -/
theorem graph_conjugation (a : Carrier N ρ) (n : N) :
    a * graph N ρ hdet n * a⁻¹ =
      graph N ρ hdet (MulAut.conjNormal (projection N ρ a) n) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact operator_conjugation N ρ a n

/-- The actual graph subgroup in the cover. -/
def graphSubgroup : Subgroup (Carrier N ρ) := (graph N ρ hdet).range

/-- The graph is normal because the actual cover operators implement ambient conjugation. -/
instance graphSubgroup_normal : (graphSubgroup N ρ hdet).Normal where
  conj_mem x hx a := by
    obtain ⟨n, rfl⟩ := hx
    exact ⟨MulAut.conjNormal (projection N ρ a) n,
      (graph_conjugation N ρ hdet a n).symm⟩

/-- The actual graph meets the projection kernel trivially, even for an unfaithful representation. -/
theorem graph_disjoint_ker : Disjoint (graphSubgroup N ρ hdet) (projection N ρ).ker := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hk
  obtain ⟨n, rfl⟩ := hx
  have hnG : (n : G) = 1 := MonoidHom.mem_ker.mp hk
  have hn : n = 1 := Subtype.ext hnG
  rw [hn, map_one]

end Kourovka2135.DeterminantOneIntertwinerGroup
