import Mathlib.RepresentationTheory.Character

/-! Matrix averaging from actual irreducibility, without a matrix-orthogonality
premise. The conjugation sum is an actual intertwiner, hence scalar by Schur;
its trace determines that scalar. Applying this result to rank-one operators
and expanding a trace in a finite basis gives matrix-coefficient orthogonality. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IrreducibleMatrixAveraging

open Representation
open scoped BigOperators MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G] [Fintype G]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- The raw sum of actual conjugate operators, before dividing by the group order. -/
def reynolds (T : Module.End k V) : Module.End k V :=
  ∑ n : G, ρ n * T * ρ n⁻¹

/-- Finite left translation proves actual invariance for the conjugation representation. -/
theorem reynolds_invariant (T : Module.End k V) :
    reynolds ρ T ∈ (linHom ρ ρ).invariants := by
  intro g
  change (linHom ρ ρ) g (∑ n : G, (linHom ρ ρ) n T) =
    ∑ n : G, (linHom ρ ρ) n T
  rw [map_sum]
  refine Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ ?_
  intro n
  rw [map_mul, Module.End.mul_apply]

/-- The conjugation sum, bundled as an actual endomorphism of the representation. -/
def reynoldsIntertwiner (T : Module.End k V) : ρ.IntertwiningMap ρ :=
  invariantsEquivIntertwiningMap ρ ρ ⟨reynolds ρ T, reynolds_invariant ρ T⟩

@[simp] theorem reynoldsIntertwiner_toLinearMap (T : Module.End k V) :
    (reynoldsIntertwiner ρ T).toLinearMap = reynolds ρ T := rfl

variable [FiniteDimensional k V] [IsAlgClosed k] [ρ.IsIrreducible]

/-- Schur's lemma supplies the scalar for the proved intertwiner. -/
theorem exists_reynolds_scalar (T : Module.End k V) :
    ∃ a : k, reynolds ρ T = a • (1 : Module.End k V) := by
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (reynoldsIntertwiner ρ T)
  refine ⟨a, ?_⟩
  have hlin := congrArg (fun f : ρ.IntertwiningMap ρ => f.toLinearMap) ha
  calc
    reynolds ρ T = (reynoldsIntertwiner ρ T).toLinearMap := rfl
    _ = (algebraMap k (ρ.IntertwiningMap ρ) a).toLinearMap := hlin.symm
    _ = a • (1 : Module.End k V) := by
      ext v
      simp [Representation.IntertwiningMap.algebraMap_apply, LinearMap.smul_apply]

variable [CharZero k]

omit [Fintype G] [IsAlgClosed k] in
include ρ in
/-- Actual irreducibility makes the coefficient dimension nonzero in characteristic zero. -/
theorem finrank_ne_zero : (Module.finrank k V : k) ≠ 0 := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  exact Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k) (M := V)).ne'

omit [IsAlgClosed k] in
/-- A finite group has nonzero cardinality in a characteristic-zero field. -/
theorem card_ne_zero : (Fintype.card G : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The exact raw Reynolds conjugation sum, with all denominators justified. -/
theorem sum_conjugates (T : Module.End k V) :
    (∑ n : G, ρ n * T * ρ n⁻¹) =
      (((Fintype.card G : k) / (Module.finrank k V : k)) * LinearMap.trace k V T) •
        (1 : Module.End k V) := by
  classical
  obtain ⟨a, ha⟩ := exists_reynolds_scalar ρ T
  have ht : a * (Module.finrank k V : k) =
      (Fintype.card G : k) * LinearMap.trace k V T := by
    calc
      a * (Module.finrank k V : k) =
          LinearMap.trace k V (a • (1 : Module.End k V)) := by
        rw [map_smul, LinearMap.trace_one, smul_eq_mul]
      _ = LinearMap.trace k V (reynolds ρ T) := congrArg (LinearMap.trace k V) ha.symm
      _ = ∑ n : G, LinearMap.trace k V (ρ n * T * ρ n⁻¹) := by
        rw [reynolds, map_sum]
      _ = (Fintype.card G : k) * LinearMap.trace k V T := by
        have heach (n : G) : LinearMap.trace k V (ρ n * T * ρ n⁻¹) =
            LinearMap.trace k V T := by
          rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
        simp only [heach, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have ha' : a = ((Fintype.card G : k) / (Module.finrank k V : k)) *
      LinearMap.trace k V T := by
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff (finrank_ne_zero ρ)).mpr ht
  exact ha.trans (congrArg (fun a : k => a • (1 : Module.End k V)) ha')

/-- Rank-one operators turn the proved Reynolds identity into coefficient averaging. -/
theorem sum_rankOne (φ : Module.Dual k V) (v w : V) :
    (∑ n : G, φ (ρ n⁻¹ w) • ρ n v) =
      (((Fintype.card G : k) / (Module.finrank k V : k)) * φ v) • w := by
  have h := congrArg (fun T : Module.End k V => T w) (sum_conjugates ρ (φ.smulRight v))
  simpa only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smulRight_apply,
    map_smul, LinearMap.trace_smulRight, LinearMap.smul_apply, Module.End.one_apply] using h

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
/-- The trace expanded in actual coordinates of a finite basis. -/
private theorem trace_eq_sum_coord {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k V) (T : Module.End k V) :
    LinearMap.trace k V T = ∑ i : ι, b.coord i (T (b i)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Module.Basis.coord_apply]

/-- Exact matrix-coefficient averaging, derived from rank-one Reynolds averaging. -/
theorem sum_trace_mul_inverse (T : Module.End k V) :
    (∑ n : G, LinearMap.trace k V (ρ n⁻¹ * T) • ρ n) =
      ((Fintype.card G : k) / (Module.finrank k V : k)) • T := by
  classical
  let b := Module.finBasis k V
  let c : k := (Fintype.card G : k) / (Module.finrank k V : k)
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [trace_eq_sum_coord b, Module.End.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ n : G, b.coord i (ρ n⁻¹ (T (b i))) • ρ n v) =
        ∑ i, (c * b.coord i v) • T (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_rankOne ρ (b.coord i) v (T (b i))
    _ = c • T (∑ i, b.coord i v • b i) := by
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
    _ = c • T v := by
      rw [show (∑ i, b.coord i v • b i) = v from by
        simpa only [Module.Basis.coord_apply] using b.sum_repr v]

end Kourovka2135.IrreducibleMatrixAveraging
