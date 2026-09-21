import Kourovka2135.PSL33ModuleTwelveCocycleData
import Kourovka2135.PSLThreeThreeSemidihedralData
import Kourovka2135.CocycleGeneratorBounds
import Kourovka2135.LinearRankCertificate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual H1 and moving-rank certificates for the twelve-dimensional
projective-plane module, using the separately checked short word DAG. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace Kourovka2135.PSL33ModuleTwelveCohomology
open PSL33ModuleTwelve SL33ProjectiveData
open CocycleGeneratorEvaluation CocycleWordConcatenation

def selectedRows : Fin 11 → Fin 4 × Fin 12 := ![(0, 1), (0, 3), (0, 5), (0, 9), (1, 0), (1, 2), (1, 4), (1, 6), (2, 0), (2, 3), (3, 0)]
def selectedColumns : Fin 11 → Fin 2 × Fin 12 := ![(0, 0), (0, 1), (0, 3), (0, 5), (0, 7), (0, 9), (0, 11), (1, 0), (1, 2), (1, 4), (1, 6)]

def columns : (Fin 11 → k) →ₗ[k] (Fin 2 → V) :=
  Fintype.linearCombination k (fun j =>
    Pi.single (selectedColumns j).1 (Pi.single (selectedColumns j).2 1))

def selectRows : (Fin 4 → V) →ₗ[k] (Fin 11 → k) :=
  LinearMap.pi (fun i =>
    (LinearMap.proj (selectedRows i).2 : V →ₗ[k] k).comp
      (LinearMap.proj (selectedRows i).1 : (Fin 4 → V) →ₗ[k] V))

def minor : Matrix (Fin 11) (Fin 11) k :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0;
    1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1;
    1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1]

def minorInverse : Matrix (Fin 11) (Fin 11) k :=
  !![1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

/-- The displayed minor is extracted from the actual coordinate word derivatives. -/
theorem selected_constraint_minor :
    selectRows.comp ((CocycleGeneratorEvaluation.constraints representation gens words).comp columns) =
      minor.mulVecLin := by
  apply LinearMap.toMatrix'.injective
  rw [show LinearMap.toMatrix' minor.mulVecLin = minor from
    LinearMap.toMatrix'_toLin' minor]
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply, columns,
    Fintype.linearCombination_apply_single, one_smul]
  change wordDerivative representation gens (words (selectedRows i).1)
    (Pi.single (selectedColumns j).1 (Pi.single (selectedColumns j).2 1))
      (selectedRows i).2 = minor i j
  rw [← derivativeMatrix_entry, certified_derivative]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem minor_inverse : minorInverse * minor = 1 := by decide +kernel

/-- The rank bound concerns the actual cocycle-constraint operator. -/
theorem constraint_rank :
    11 ≤ Module.finrank k (LinearMap.range
      (CocycleGeneratorEvaluation.constraints representation gens words)) := by
  apply LinearRankCertificate.nat_le_range 11 _ columns (minorInverse.mulVecLin.comp selectRows)
  rw [LinearMap.comp_assoc, selected_constraint_minor, ← Matrix.mulVecLin_mul, minor_inverse, Matrix.mulVecLin_one]

/-- The same actual order-thirteen element is used for the moving-rank certificate. -/
def singer : Q := gens 0 * gens 1

def movingInverse : Matrix (Fin 12) (Fin 12) k :=
  !![1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1;
    1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0;
    0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1;
    1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

theorem moving_matrix : representation singer - LinearMap.id =
    (leftA * leftB - 1).mulVecLin := by
  rw [singer, map_mul, generator_operators (0 : Fin 2),
    generator_operators (1 : Fin 2)]
  change leftA.mulVecLin.comp leftB.mulVecLin - LinearMap.id = _
  change leftA.mulVecLin.comp leftB.mulVecLin - LinearMap.id =
    Matrix.toLin' (leftA * leftB - 1)
  rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_one]
  simp only [Matrix.toLin'_apply']

theorem moving_inverse : movingInverse * (leftA * leftB - 1) = 1 := by decide +kernel

theorem moving_left_inverse : movingInverse.mulVecLin.comp
    (representation singer - LinearMap.id) = LinearMap.id := by
  rw [moving_matrix, ← Matrix.mulVecLin_mul, moving_inverse, Matrix.mulVecLin_one]

theorem moving_injective : Function.Injective
    (representation singer - LinearMap.id : Module.End k V) := by
  intro x y h
  have he := congrArg movingInverse.mulVecLin h
  simpa only [← LinearMap.comp_apply, moving_left_inverse, LinearMap.id_apply] using he

theorem invariants_eq_bot : representation.invariants = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  apply moving_injective
  have hfix := (Representation.mem_invariants representation v).mp hv singer
  simp only [LinearMap.sub_apply, LinearMap.id_apply, hfix, sub_self, map_zero]

theorem moving_rank :
    12 ≤ Module.finrank k (LinearMap.range (representation singer - LinearMap.id)) := by
  apply LinearRankCertificate.nat_le_range 12 _ LinearMap.id movingInverse.mulVecLin
  simpa only [LinearMap.comp_id] using moving_left_inverse

theorem singer_order : orderOf singer = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩
  have hp : (a * b) ^ 13 = 1 := by decide +kernel
  have hn : a * b ≠ 1 := by decide +kernel
  have ho : orderOf (a * b) = 13 := orderOf_eq_prime hp hn
  change orderOf (PSLThreeThreeSemidihedralData.projectiveEquiv (a * b)) = 13
  rw [MulEquiv.orderOf_eq, ho]

/-- The ordinary first cohomology has dimension at most one, proved from the four relations. -/
theorem finrank_H1_le_one :
    Module.finrank k (groupCohomology (Rep.of representation) 1) ≤ 1 := by
  apply CocycleGeneratorBounds.finrank_H1_le_of_two_generator_constraints
    representation gens generators_generate invariants_eq_bot words actual_relations 1
  have h := constraint_rank
  rw [finrank_eq_twelve]
  omega

end Kourovka2135.PSL33ModuleTwelveCohomology
