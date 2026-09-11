import Kourovka.Problems.P21_68.Proof.AbelianKernel
import Kourovka.Problems.P21_68.Proof.QuaternionRep
import Kourovka.External.TauCeti.RepresentationTheory.Induction.Restriction
import Kourovka.External.TauCeti.RepresentationTheory.Simple.Basic

/-!
# The representation of the inertia subgroup

Multiplication by a one-dimensional character leaves the invariant-subspace
lattice unchanged. This gives an irreducible representation of `I` by twisting
the inflation of the two-dimensional quaternion representation.
-/

noncomputable section

namespace Kourovka.P21_68

open CategoryTheory

section ScalarTwist

variable {k F V : Type*} [Field k] [Monoid F] [AddCommGroup V] [Module k V]

/-- Twist a representation by a one-dimensional character. -/
def scalarTwist (χ : F →* kˣ) (ρ : Representation k F V) : Representation k F V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- Scalar twisting does not alter the invariant subspaces. -/
def scalarTwistSubrepresentationEquiv (χ : F →* kˣ) (ρ : Representation k F V) :
    Subrepresentation (scalarTwist χ ρ) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := S.toSubmodule.smul_mem ((χ g : k)⁻¹) (S.apply_mem_toSubmodule g hv)
        simpa [scalarTwist, smul_smul] using h }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv =>
        S.toSubmodule.smul_mem (χ g : k) (S.apply_mem_toSubmodule g hv) }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

lemma isIrreducible_scalarTwist_iff (χ : F →* kˣ) (ρ : Representation k F V) :
    Representation.IsIrreducible (scalarTwist χ ρ) ↔ Representation.IsIrreducible ρ :=
  (scalarTwistSubrepresentationEquiv χ ρ).isSimpleOrder_iff

end ScalarTwist

/-- The quotient map from the inertia subgroup to the abstract quaternion complement. -/
def inertiaProjection : I →* H := hEquivHsub.symm.toMonoidHom.comp iProjection

lemma inertiaProjection_surjective : Function.Surjective inertiaProjection :=
  hEquivHsub.symm.surjective.comp iProjection_surjective

/-- Inflation followed by twisting by the extended coordinate character. -/
def inertiaRepresentation : Representation ℂ I (Fin 2 → ℂ) :=
  scalarTwist lambdaExtended (quaternionRepresentation.comp inertiaProjection)

/-- The irreducible representation to be induced to the full group. -/
def inertiaRep : FDRep ℂ I := FDRep.of inertiaRepresentation

@[simp] lemma finrank_inertiaRep : Module.finrank ℂ inertiaRep = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  simp

instance simple_inertiaRep : Simple inertiaRep := by
  apply (FDRep.simple_iff_isIrreducible inertiaRep).2
  apply (isIrreducible_scalarTwist_iff _ _).2
  apply (TauCeti.isIrreducible_comp_surjective_iff _ inertiaProjection_surjective _).2
  exact (FDRep.simple_iff_isIrreducible quaternionRep).1 inferInstance

@[simp] lemma inertiaProjection_iA (a : A) : inertiaProjection (iA a) = 1 := by
  simp [inertiaProjection]

/-- The abelian kernel acts by the chosen scalar character. -/
lemma inertiaRep_iA (a : A) : inertiaRep.ρ (iA a) = (lambda a : ℂ) • LinearMap.id := by
  change (lambdaExtended (iA a) : ℂ) • quaternionRepresentation (inertiaProjection (iA a)) = _
  simp
  rfl

/-- Scalar action on the normal subgroup, in subgroup-inclusion form. -/
lemma inertiaRep_N (n : N) :
    inertiaRep.ρ (Subgroup.inclusion N_le_I n) = (nWeight n : ℂ) • LinearMap.id := by
  change (lambdaExtended (Subgroup.inclusion N_le_I n) : ℂ) •
    quaternionRepresentation (inertiaProjection (Subgroup.inclusion N_le_I n)) = _
  simp [inertiaProjection]
  rfl

end Kourovka.P21_68
