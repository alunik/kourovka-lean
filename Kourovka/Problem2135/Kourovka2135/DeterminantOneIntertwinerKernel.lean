import Kourovka2135.DeterminantOneIntertwinerGroup
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-! The actual determinant-one intertwiner kernel is finite and central.

Scalar Schur identifies each actual kernel operator with a scalar. Determinant
one makes its scalar a root of unity of degree dim(V). The scalar coordinate
is injective, giving finiteness without any surjectivity assumption on the
cover. If dim(V) is a power of two, the actual kernel is a 2-group.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.DeterminantOneIntertwinerKernel

open DeterminantOneIntertwinerGroup
open scoped MonoidAlgebra

variable {k : Type v} [Field k] {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (rho : Representation k N V)

/-- The operator determines an element of the actual projection kernel. -/
theorem kernel_operator_injective : Function.Injective
    (fun x : (projection N rho).ker => operator N rho x.val) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact x.property.trans y.property.symm
  · exact h

/-- The actual kernel action, bundled as a homomorphism of endomorphisms. -/
def kernelEnd : (projection N rho).ker →* Module.End k V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((operator N rho).comp (projection N rho).ker.subtype)

@[simp] theorem kernelEnd_apply (x : (projection N rho).ker) :
    kernelEnd N rho x = (operator N rho x.val).toLinearMap := rfl

theorem kernelEnd_injective : Function.Injective (kernelEnd N rho) := by
  intro x y h
  apply kernel_operator_injective N rho
  exact LinearEquiv.toLinearMap_injective h

variable [FiniteDimensional k V] [IsAlgClosed k] [rho.IsIrreducible]

/-- Every actual kernel operator is scalar by Schur's lemma. -/
theorem exists_kernelEnd_scalar (x : (projection N rho).ker) :
    ∃ a : k, kernelEnd N rho x = a • (1 : Module.End k V) := by
  let phi : rho.IntertwiningMap rho := {
    toLinearMap := kernelEnd N rho x
    isIntertwining' := fun n => by
      have hx : projection N rho x.val = 1 := x.property
      simpa [hx] using operator_intertwines N rho x.val n }
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rho)).surjective phi
  refine ⟨a, ?_⟩
  have hlin := congrArg (fun T : rho.IntertwiningMap rho => T.toLinearMap) ha
  calc
    kernelEnd N rho x = phi.toLinearMap := rfl
    _ = (algebraMap k (rho.IntertwiningMap rho) a).toLinearMap := hlin.symm
    _ = a • (1 : Module.End k V) := by
      ext z
      simp [Representation.IntertwiningMap.algebraMap_apply, LinearMap.smul_apply]

/-- A chosen actual scalar coordinate; no character is assumed as input. -/
def scalar (x : (projection N rho).ker) : k :=
  Classical.choose (exists_kernelEnd_scalar N rho x)

theorem scalar_spec (x : (projection N rho).ker) :
    kernelEnd N rho x = scalar N rho x • (1 : Module.End k V) :=
  Classical.choose_spec (exists_kernelEnd_scalar N rho x)

/-- Equal scalar coordinates give equal actual cover-kernel elements. -/
theorem scalar_injective : Function.Injective (scalar N rho) := by
  intro x y h
  apply kernelEnd_injective N rho
  rw [scalar_spec, scalar_spec, h]

/-- The determinant equation bounds the order of every actual scalar. -/
theorem scalar_pow_finrank (x : (projection N rho).ker) :
    scalar N rho x ^ Module.finrank k V = 1 := by
  have hd : LinearMap.det (kernelEnd N rho x) = 1 := by
    have h := congrArg (fun a : kˣ => (a : k)) (operator_det N rho x.val)
    simpa only [LinearEquiv.coe_det, Units.val_one, kernelEnd_apply] using h
  rw [scalar_spec, LinearMap.det_smul, map_one, mul_one] at hd
  exact hd

omit [N.Normal] [IsAlgClosed k] in
include rho in
/-- Actual irreducibility rules out degree zero. -/
theorem coefficient_finrank_pos : 0 < Module.finrank k V := by
  let : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[N] rho.asModule
  let : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
  exact Module.finrank_pos

/-- Every actual kernel element has a coordinate in a finite roots-of-unity group. -/
def scalarRoot (x : (projection N rho).ker) : rootsOfUnity (Module.finrank k V) k := by
  let : NeZero (Module.finrank k V) := ⟨(coefficient_finrank_pos N rho).ne'⟩
  exact rootsOfUnity.mkOfPowEq (scalar N rho x) (scalar_pow_finrank N rho x)

@[simp] theorem scalarRoot_val (x : (projection N rho).ker) :
    ((scalarRoot N rho x : kˣ) : k) = scalar N rho x := rfl

theorem scalarRoot_injective : Function.Injective (scalarRoot N rho) := by
  intro x y h
  apply scalar_injective N rho
  exact congrArg (fun z : rootsOfUnity (Module.finrank k V) k => ((z : kˣ) : k)) h

/-- The actual projection kernel is finite, without assuming cover surjectivity. -/
theorem kernel_finite : Finite (projection N rho).ker := by
  let : NeZero (Module.finrank k V) := ⟨(coefficient_finrank_pos N rho).ne'⟩
  exact Finite.of_injective (scalarRoot N rho) (scalarRoot_injective N rho)

/-- The actual kernel is central in the entire intertwiner cover. -/
theorem kernel_le_center : (projection N rho).ker ≤ Subgroup.center (Carrier N rho) := by
  intro x hx
  obtain ⟨a, ha⟩ := exists_kernelEnd_scalar N rho ⟨x, hx⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change projection N rho y * projection N rho x =
      projection N rho x * projection N rho y
    rw [show projection N rho x = 1 from hx, mul_one, one_mul]
  · apply LinearEquiv.toLinearMap_injective
    change (operator N rho y).toLinearMap * (operator N rho x).toLinearMap =
      (operator N rho x).toLinearMap * (operator N rho y).toLinearMap
    change (operator N rho x).toLinearMap = a • (1 : Module.End k V) at ha
    rw [ha]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- A power-of-two degree forces the actual kernel to be a 2-group. -/
theorem kernel_isPGroup_two (a : ℕ) (hdim : Module.finrank k V = 2 ^ a) :
    IsPGroup 2 (projection N rho).ker := by
  intro x
  refine ⟨a, ?_⟩
  apply kernelEnd_injective N rho
  rw [map_pow, map_one, scalar_spec, smul_pow, one_pow]
  have hs : scalar N rho x ^ (2 ^ a) = 1 := by
    simpa only [hdim] using scalar_pow_finrank N rho x
  rw [hs, one_smul]

/-- Finite ambient group plus finite actual kernel gives a finite cover. -/
theorem carrier_finite [Finite G] : Finite (Carrier N rho) := by
  let : Finite (projection N rho).ker := kernel_finite N rho
  exact (projection N rho).finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

end Kourovka2135.DeterminantOneIntertwinerKernel
