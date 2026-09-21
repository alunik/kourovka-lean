import Kourovka2135.PSL33ModuleSixteenCocycleData
import Kourovka2135.PSLThreeThreeSemidihedralData
import Kourovka2135.CocycleGeneratorBounds
import Kourovka2135.LinearRankCertificate
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Actual H1 and moving-rank certificates for the 16-dimensional
Singer-coset quotient module, using the separately checked short word DAG. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
open Kourovka2135.BinaryFieldSixteen
namespace Kourovka2135.PSL33ModuleSixteenCohomology
open PSL33ModuleSixteen SL33ProjectiveData PSL33SingerSixteenData
open scoped Matrix
open CocycleGeneratorEvaluation CocycleWordConcatenation

def selectedRows : Fin 16 → Fin 3 × Fin 16 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 7), (0, 11), (1, 0), (1, 1), (1, 3), (1, 5), (1, 8), (1, 9), (2, 0), (2, 2)]
def selectedColumns : Fin 16 → Fin 2 × Fin 16 := ![(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 11), (0, 12), (0, 14), (1, 1), (1, 3), (1, 5), (1, 8), (1, 9), (1, 13)]

def columns : (Fin 16 → k) →ₗ[k] (Fin 2 → V) :=
  Fintype.linearCombination k (fun j =>
    Pi.single (selectedColumns j).1 (Pi.single (selectedColumns j).2 1))

def selectRows : (Fin 3 → V) →ₗ[k] (Fin 16 → k) :=
  LinearMap.pi (fun i =>
    (LinearMap.proj (selectedRows i).2 : V →ₗ[k] k).comp
      (LinearMap.proj (selectedRows i).1 : (Fin 3 → V) →ₗ[k] V))

def minor : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![176093659153, 64424509457, 798863917312, 944892805376, 438086733824, 867584442368, 103095992320, 803427319808, 12682137650186944512, 1099511627776, 12682154142861361152, 17294104044079415296, 17298326168730075136, 72057594037927936, 9933692353320292368, 506808475563733179]

def minorInverse : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![2413237573077932445, 2413237573077915130, 61405, 1184596706199788909, 1184596706199850093, 1096584, 16786175, 268452864, 43741, 56797, 68719476736, 1172526071808, 18030272708608, 281913063374848, 4503599627370496, 365072220160]

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
    16 ≤ Module.finrank k (LinearMap.range
      (CocycleGeneratorEvaluation.constraints representation gens words)) := by
  apply LinearRankCertificate.nat_le_range 16 _ columns (minorInverse.mulVecLin.comp selectRows)
  rw [LinearMap.comp_assoc, selected_constraint_minor, ← Matrix.mulVecLin_mul, minor_inverse, Matrix.mulVecLin_one]

/-- The same actual order-thirteen element is used for the moving-rank certificate. -/
def singer : Q := gens 0 * gens 1

def generatorDifference : Matrix (Fin 2 × Fin 16) (Fin 16) k :=
  fun i j => (![(leftA - 1), (leftB - 1)] i.1) i.2 j

def invariantLeftRows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![87964772471008, 140738696926246, 140738696926246, 140740307561039, 158330899699988, 175922297368285, 70372569767378, 175922297368285, 193514751830645, 123146493973815, 35186553279802, 246291125720404, 105555901703788, 211107508418461, 70372032796130, 52777950865097]) i j else (packedMatrix ![986236395278, 312737272837, 312737272836, 722369780491, 316762817797, 114365693952, 982210907919, 114364645376, 186842219010, 374475260932, 561032333577, 136918794497, 716192483850, 328578368516, 843965533196, 358096241925]) i j
def invariantLeft : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i j => invariantLeftRows i j.1 j.2

theorem invariant_left_inverse : invariantLeft * generatorDifference = 1 := by decide +kernel

theorem generatorDifference_apply (v : V) (i : Fin 2) (j : Fin 16) :
    (generatorDifference *ᵥ v) (i, j) = (ops i v - v) j := by
  fin_cases i
  · change ((leftA - 1) *ᵥ v) j = (leftA *ᵥ v - v) j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  · change ((leftB - 1) *ᵥ v) j = (leftB *ᵥ v - v) j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem invariants_eq_bot : representation.invariants = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  have hfix (i : Fin 2) : ops i v = v := by
    rw [← generator_operators]
    exact (Representation.mem_invariants representation v).mp hv (gens i)
  have hz : generatorDifference *ᵥ v = 0 := by
    funext ⟨i, j⟩
    exact (generatorDifference_apply v i j).trans
      (congrFun (sub_eq_zero.mpr (hfix i)) j)
  have hleft : invariantLeft *ᵥ (generatorDifference *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, invariant_left_inverse, Matrix.one_mulVec]
  rw [hz, Matrix.mulVec_zero] at hleft
  exact hleft.symm

theorem moving_matrix : representation singer - LinearMap.id =
    (leftA * leftB - 1).mulVecLin := by
  rw [singer, map_mul, generator_operators (0 : Fin 2),
    generator_operators (1 : Fin 2)]
  change leftA.mulVecLin.comp leftB.mulVecLin - LinearMap.id = _
  change leftA.mulVecLin.comp leftB.mulVecLin - LinearMap.id =
    Matrix.toLin' (leftA * leftB - 1)
  rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_one]
  simp only [Matrix.toLin'_apply']

def movingColumns : Matrix (Fin 16) (Fin 15) k :=
  packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 0]
def movingRows : Matrix (Fin 15) (Fin 16) k :=
  packedMatrix ![536755202090480160, 1073177316243559489, 77266062902702640, 310169055677767120, 77704708324873552, 537618401129293408, 919087340571398416, 1075744639691836608, 230686349451277104, 1149737337382782016, 770045304921653232, 692885899066596816, 1073756699565193072, 1150441038372370288, 314390011828817088]

theorem moving_certificate : movingRows * ((leftA * leftB - 1) * movingColumns) = 1 :=
  by decide +kernel

theorem moving_rank :
    15 ≤ Module.finrank k (LinearMap.range (representation singer - LinearMap.id)) := by
  rw [moving_matrix]
  exact LinearRankCertificate.matrix_rank_lower_bound 15
    (leftA * leftB - 1) movingColumns movingRows moving_certificate

theorem singer_order : orderOf singer = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩
  have hp : (a * b) ^ 13 = 1 := by decide +kernel
  have hn : a * b ≠ 1 := by decide +kernel
  have ho : orderOf (a * b) = 13 := orderOf_eq_prime hp hn
  change orderOf (PSLThreeThreeSemidihedralData.projectiveEquiv (a * b)) = 13
  rw [MulEquiv.orderOf_eq, ho]

/-- The three actual necessary relations force ordinary H1 to vanish in dimension. -/
theorem finrank_H1_eq_zero :
    Module.finrank k (groupCohomology (Rep.of representation) 1) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply CocycleGeneratorBounds.finrank_H1_le_of_two_generator_constraints
    representation gens generators_generate invariants_eq_bot words actual_relations 0
  have h := constraint_rank
  rw [finrank_eq_sixteen]
  omega

end Kourovka2135.PSL33ModuleSixteenCohomology
