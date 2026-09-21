import Kourovka2135.PSL33ModuleSixteenRankOneData

/-! Actual density from a small group-algebra polynomial and two cyclic bases.
The actual element defined by the certified order-thirteen norm polynomial has the displayed rank-one
operator. Genuine group-word translates of its factors give two certified
bases. The generic sandwich argument constructs every endomorphism in the
actual algebra image, and the existing base-change theorem supplies absolute
irreducibility. No classification or external matrix-rank input occurs.
-/

set_option autoImplicit false
noncomputable section
open Kourovka2135.BinaryFieldSixteen
namespace Kourovka2135.PSL33ModuleSixteenDensity
open scoped MonoidAlgebra
open PSL33ModuleSixteen SL33ProjectiveData PSL33SingerSixteenData PSL33ModuleSixteenRankOneData
open RankOneOperatorSpanCertificate

def element000 : Q := 1
theorem actual_operator_000 : LinearMap.toMatrix' (representation element000) = operator000 := by
  rw [element000, map_one, LinearMap.toMatrix'_one, ← operator_step_000]

def element001 : Q := element000 * PSL33GoodSets.q a
theorem actual_operator_001 : LinearMap.toMatrix' (representation element001) = operator001 := by
  rw [element001, map_mul, LinearMap.toMatrix'_mul, actual_operator_000, toMatrix_a, ← operator_step_001]

def element002 : Q := element000 * PSL33GoodSets.q b
theorem actual_operator_002 : LinearMap.toMatrix' (representation element002) = operator002 := by
  rw [element002, map_mul, LinearMap.toMatrix'_mul, actual_operator_000, toMatrix_b, ← operator_step_002]

def element003 : Q := element001 * PSL33GoodSets.q b
theorem actual_operator_003 : LinearMap.toMatrix' (representation element003) = operator003 := by
  rw [element003, map_mul, LinearMap.toMatrix'_mul, actual_operator_001, toMatrix_b, ← operator_step_003]

def element004 : Q := element002 * PSL33GoodSets.q a
theorem actual_operator_004 : LinearMap.toMatrix' (representation element004) = operator004 := by
  rw [element004, map_mul, LinearMap.toMatrix'_mul, actual_operator_002, toMatrix_a, ← operator_step_004]

def element005 : Q := element002 * PSL33GoodSets.q b
theorem actual_operator_005 : LinearMap.toMatrix' (representation element005) = operator005 := by
  rw [element005, map_mul, LinearMap.toMatrix'_mul, actual_operator_002, toMatrix_b, ← operator_step_005]

def element006 : Q := element003 * PSL33GoodSets.q a
theorem actual_operator_006 : LinearMap.toMatrix' (representation element006) = operator006 := by
  rw [element006, map_mul, LinearMap.toMatrix'_mul, actual_operator_003, toMatrix_a, ← operator_step_006]

def element007 : Q := element003 * PSL33GoodSets.q b
theorem actual_operator_007 : LinearMap.toMatrix' (representation element007) = operator007 := by
  rw [element007, map_mul, LinearMap.toMatrix'_mul, actual_operator_003, toMatrix_b, ← operator_step_007]

def element008 : Q := element004 * PSL33GoodSets.q b
theorem actual_operator_008 : LinearMap.toMatrix' (representation element008) = operator008 := by
  rw [element008, map_mul, LinearMap.toMatrix'_mul, actual_operator_004, toMatrix_b, ← operator_step_008]

def element009 : Q := element005 * PSL33GoodSets.q a
theorem actual_operator_009 : LinearMap.toMatrix' (representation element009) = operator009 := by
  rw [element009, map_mul, LinearMap.toMatrix'_mul, actual_operator_005, toMatrix_a, ← operator_step_009]

def element010 : Q := element006 * PSL33GoodSets.q b
theorem actual_operator_010 : LinearMap.toMatrix' (representation element010) = operator010 := by
  rw [element010, map_mul, LinearMap.toMatrix'_mul, actual_operator_006, toMatrix_b, ← operator_step_010]

def element011 : Q := element007 * PSL33GoodSets.q a
theorem actual_operator_011 : LinearMap.toMatrix' (representation element011) = operator011 := by
  rw [element011, map_mul, LinearMap.toMatrix'_mul, actual_operator_007, toMatrix_a, ← operator_step_011]

def element012 : Q := element008 * PSL33GoodSets.q a
theorem actual_operator_012 : LinearMap.toMatrix' (representation element012) = operator012 := by
  rw [element012, map_mul, LinearMap.toMatrix'_mul, actual_operator_008, toMatrix_a, ← operator_step_012]

def element013 : Q := element008 * PSL33GoodSets.q b
theorem actual_operator_013 : LinearMap.toMatrix' (representation element013) = operator013 := by
  rw [element013, map_mul, LinearMap.toMatrix'_mul, actual_operator_008, toMatrix_b, ← operator_step_013]

def element014 : Q := element009 * PSL33GoodSets.q b
theorem actual_operator_014 : LinearMap.toMatrix' (representation element014) = operator014 := by
  rw [element014, map_mul, LinearMap.toMatrix'_mul, actual_operator_009, toMatrix_b, ← operator_step_014]

def element015 : Q := element010 * PSL33GoodSets.q a
theorem actual_operator_015 : LinearMap.toMatrix' (representation element015) = operator015 := by
  rw [element015, map_mul, LinearMap.toMatrix'_mul, actual_operator_010, toMatrix_a, ← operator_step_015]

def element016 : Q := element010 * PSL33GoodSets.q b
theorem actual_operator_016 : LinearMap.toMatrix' (representation element016) = operator016 := by
  rw [element016, map_mul, LinearMap.toMatrix'_mul, actual_operator_010, toMatrix_b, ← operator_step_016]

def element017 : Q := element011 * PSL33GoodSets.q b
theorem actual_operator_017 : LinearMap.toMatrix' (representation element017) = operator017 := by
  rw [element017, map_mul, LinearMap.toMatrix'_mul, actual_operator_011, toMatrix_b, ← operator_step_017]

def element018 : Q := element012 * PSL33GoodSets.q b
theorem actual_operator_018 : LinearMap.toMatrix' (representation element018) = operator018 := by
  rw [element018, map_mul, LinearMap.toMatrix'_mul, actual_operator_012, toMatrix_b, ← operator_step_018]

def element019 : Q := element013 * PSL33GoodSets.q a
theorem actual_operator_019 : LinearMap.toMatrix' (representation element019) = operator019 := by
  rw [element019, map_mul, LinearMap.toMatrix'_mul, actual_operator_013, toMatrix_a, ← operator_step_019]

def element020 : Q := element014 * PSL33GoodSets.q a
theorem actual_operator_020 : LinearMap.toMatrix' (representation element020) = operator020 := by
  rw [element020, map_mul, LinearMap.toMatrix'_mul, actual_operator_014, toMatrix_a, ← operator_step_020]

def element021 : Q := element015 * PSL33GoodSets.q b
theorem actual_operator_021 : LinearMap.toMatrix' (representation element021) = operator021 := by
  rw [element021, map_mul, LinearMap.toMatrix'_mul, actual_operator_015, toMatrix_b, ← operator_step_021]

def element022 : Q := element016 * PSL33GoodSets.q a
theorem actual_operator_022 : LinearMap.toMatrix' (representation element022) = operator022 := by
  rw [element022, map_mul, LinearMap.toMatrix'_mul, actual_operator_016, toMatrix_a, ← operator_step_022]

def element023 : Q := element017 * PSL33GoodSets.q a
theorem actual_operator_023 : LinearMap.toMatrix' (representation element023) = operator023 := by
  rw [element023, map_mul, LinearMap.toMatrix'_mul, actual_operator_017, toMatrix_a, ← operator_step_023]

def element024 : Q := element018 * PSL33GoodSets.q a
theorem actual_operator_024 : LinearMap.toMatrix' (representation element024) = operator024 := by
  rw [element024, map_mul, LinearMap.toMatrix'_mul, actual_operator_018, toMatrix_a, ← operator_step_024]

def element025 : Q := element018 * PSL33GoodSets.q b
theorem actual_operator_025 : LinearMap.toMatrix' (representation element025) = operator025 := by
  rw [element025, map_mul, LinearMap.toMatrix'_mul, actual_operator_018, toMatrix_b, ← operator_step_025]

def element026 : Q := element019 * PSL33GoodSets.q b
theorem actual_operator_026 : LinearMap.toMatrix' (representation element026) = operator026 := by
  rw [element026, map_mul, LinearMap.toMatrix'_mul, actual_operator_019, toMatrix_b, ← operator_step_026]

def element027 : Q := element020 * PSL33GoodSets.q b
theorem actual_operator_027 : LinearMap.toMatrix' (representation element027) = operator027 := by
  rw [element027, map_mul, LinearMap.toMatrix'_mul, actual_operator_020, toMatrix_b, ← operator_step_027]

def element028 : Q := element021 * PSL33GoodSets.q a
theorem actual_operator_028 : LinearMap.toMatrix' (representation element028) = operator028 := by
  rw [element028, map_mul, LinearMap.toMatrix'_mul, actual_operator_021, toMatrix_a, ← operator_step_028]

def element029 : Q := element022 * PSL33GoodSets.q b
theorem actual_operator_029 : LinearMap.toMatrix' (representation element029) = operator029 := by
  rw [element029, map_mul, LinearMap.toMatrix'_mul, actual_operator_022, toMatrix_b, ← operator_step_029]

def element030 : Q := element023 * PSL33GoodSets.q b
theorem actual_operator_030 : LinearMap.toMatrix' (representation element030) = operator030 := by
  rw [element030, map_mul, LinearMap.toMatrix'_mul, actual_operator_023, toMatrix_b, ← operator_step_030]

def element031 : Q := element024 * PSL33GoodSets.q b
theorem actual_operator_031 : LinearMap.toMatrix' (representation element031) = operator031 := by
  rw [element031, map_mul, LinearMap.toMatrix'_mul, actual_operator_024, toMatrix_b, ← operator_step_031]

def element032 : Q := element025 * PSL33GoodSets.q a
theorem actual_operator_032 : LinearMap.toMatrix' (representation element032) = operator032 := by
  rw [element032, map_mul, LinearMap.toMatrix'_mul, actual_operator_025, toMatrix_a, ← operator_step_032]

def element033 : Q := element026 * PSL33GoodSets.q a
theorem actual_operator_033 : LinearMap.toMatrix' (representation element033) = operator033 := by
  rw [element033, map_mul, LinearMap.toMatrix'_mul, actual_operator_026, toMatrix_a, ← operator_step_033]

def element034 : Q := element027 * PSL33GoodSets.q a
theorem actual_operator_034 : LinearMap.toMatrix' (representation element034) = operator034 := by
  rw [element034, map_mul, LinearMap.toMatrix'_mul, actual_operator_027, toMatrix_a, ← operator_step_034]

def element035 : Q := element028 * PSL33GoodSets.q b
theorem actual_operator_035 : LinearMap.toMatrix' (representation element035) = operator035 := by
  rw [element035, map_mul, LinearMap.toMatrix'_mul, actual_operator_028, toMatrix_b, ← operator_step_035]

def element036 : Q := element029 * PSL33GoodSets.q a
theorem actual_operator_036 : LinearMap.toMatrix' (representation element036) = operator036 := by
  rw [element036, map_mul, LinearMap.toMatrix'_mul, actual_operator_029, toMatrix_a, ← operator_step_036]

def element037 : Q := element030 * PSL33GoodSets.q a
theorem actual_operator_037 : LinearMap.toMatrix' (representation element037) = operator037 := by
  rw [element037, map_mul, LinearMap.toMatrix'_mul, actual_operator_030, toMatrix_a, ← operator_step_037]

def element038 : Q := element031 * PSL33GoodSets.q a
theorem actual_operator_038 : LinearMap.toMatrix' (representation element038) = operator038 := by
  rw [element038, map_mul, LinearMap.toMatrix'_mul, actual_operator_031, toMatrix_a, ← operator_step_038]

def element039 : Q := element035 * PSL33GoodSets.q a
theorem actual_operator_039 : LinearMap.toMatrix' (representation element039) = operator039 := by
  rw [element039, map_mul, LinearMap.toMatrix'_mul, actual_operator_035, toMatrix_a, ← operator_step_039]

def element040 : Q := element039 * PSL33GoodSets.q b
theorem actual_operator_040 : LinearMap.toMatrix' (representation element040) = operator040 := by
  rw [element040, map_mul, LinearMap.toMatrix'_mul, actual_operator_039, toMatrix_b, ← operator_step_040]

def element041 : Q := element040 * PSL33GoodSets.q a
theorem actual_operator_041 : LinearMap.toMatrix' (representation element041) = operator041 := by
  rw [element041, map_mul, LinearMap.toMatrix'_mul, actual_operator_040, toMatrix_a, ← operator_step_041]

def element042 : Q := element041 * PSL33GoodSets.q b
theorem actual_operator_042 : LinearMap.toMatrix' (representation element042) = operator042 := by
  rw [element042, map_mul, LinearMap.toMatrix'_mul, actual_operator_041, toMatrix_b, ← operator_step_042]

def element043 : Q := element042 * PSL33GoodSets.q a
theorem actual_operator_043 : LinearMap.toMatrix' (representation element043) = operator043 := by
  rw [element043, map_mul, LinearMap.toMatrix'_mul, actual_operator_042, toMatrix_a, ← operator_step_043]

def element044 : Q := element043 * PSL33GoodSets.q b
theorem actual_operator_044 : LinearMap.toMatrix' (representation element044) = operator044 := by
  rw [element044, map_mul, LinearMap.toMatrix'_mul, actual_operator_043, toMatrix_b, ← operator_step_044]

def element045 : Q := element044 * PSL33GoodSets.q a
theorem actual_operator_045 : LinearMap.toMatrix' (representation element045) = operator045 := by
  rw [element045, map_mul, LinearMap.toMatrix'_mul, actual_operator_044, toMatrix_a, ← operator_step_045]

def element046 : Q := element045 * PSL33GoodSets.q b
theorem actual_operator_046 : LinearMap.toMatrix' (representation element046) = operator046 := by
  rw [element046, map_mul, LinearMap.toMatrix'_mul, actual_operator_045, toMatrix_b, ← operator_step_046]

def element047 : Q := element046 * PSL33GoodSets.q a
theorem actual_operator_047 : LinearMap.toMatrix' (representation element047) = operator047 := by
  rw [element047, map_mul, LinearMap.toMatrix'_mul, actual_operator_046, toMatrix_a, ← operator_step_047]

def element048 : Q := element047 * PSL33GoodSets.q b
theorem actual_operator_048 : LinearMap.toMatrix' (representation element048) = operator048 := by
  rw [element048, map_mul, LinearMap.toMatrix'_mul, actual_operator_047, toMatrix_b, ← operator_step_048]

def element049 : Q := element048 * PSL33GoodSets.q a
theorem actual_operator_049 : LinearMap.toMatrix' (representation element049) = operator049 := by
  rw [element049, map_mul, LinearMap.toMatrix'_mul, actual_operator_048, toMatrix_a, ← operator_step_049]

def element050 : Q := element049 * PSL33GoodSets.q b
theorem actual_operator_050 : LinearMap.toMatrix' (representation element050) = operator050 := by
  rw [element050, map_mul, LinearMap.toMatrix'_mul, actual_operator_049, toMatrix_b, ← operator_step_050]

def element051 : Q := element050 * PSL33GoodSets.q a
theorem actual_operator_051 : LinearMap.toMatrix' (representation element051) = operator051 := by
  rw [element051, map_mul, LinearMap.toMatrix'_mul, actual_operator_050, toMatrix_a, ← operator_step_051]

def element052 : Q := element051 * PSL33GoodSets.q b
theorem actual_operator_052 : LinearMap.toMatrix' (representation element052) = operator052 := by
  rw [element052, map_mul, LinearMap.toMatrix'_mul, actual_operator_051, toMatrix_b, ← operator_step_052]

def element053 : Q := element052 * PSL33GoodSets.q a
theorem actual_operator_053 : LinearMap.toMatrix' (representation element053) = operator053 := by
  rw [element053, map_mul, LinearMap.toMatrix'_mul, actual_operator_052, toMatrix_a, ← operator_step_053]

def element054 : Q := element053 * PSL33GoodSets.q b
theorem actual_operator_054 : LinearMap.toMatrix' (representation element054) = operator054 := by
  rw [element054, map_mul, LinearMap.toMatrix'_mul, actual_operator_053, toMatrix_b, ← operator_step_054]

def elements : Fin 55 → Q := ![element000, element001, element002, element003, element004, element005, element006, element007, element008, element009, element010, element011, element012, element013, element014, element015, element016, element017, element018, element019, element020, element021, element022, element023, element024, element025, element026, element027, element028, element029, element030, element031, element032, element033, element034, element035, element036, element037, element038, element039, element040, element041, element042, element043, element044, element045, element046, element047, element048, element049, element050, element051, element052, element053, element054]
set_option maxRecDepth 4096 in
theorem actual_operators (i : Fin 55) : LinearMap.toMatrix' (representation (elements i)) = operators i := by
  fin_cases i
  · exact actual_operator_000
  · exact actual_operator_001
  · exact actual_operator_002
  · exact actual_operator_003
  · exact actual_operator_004
  · exact actual_operator_005
  · exact actual_operator_006
  · exact actual_operator_007
  · exact actual_operator_008
  · exact actual_operator_009
  · exact actual_operator_010
  · exact actual_operator_011
  · exact actual_operator_012
  · exact actual_operator_013
  · exact actual_operator_014
  · exact actual_operator_015
  · exact actual_operator_016
  · exact actual_operator_017
  · exact actual_operator_018
  · exact actual_operator_019
  · exact actual_operator_020
  · exact actual_operator_021
  · exact actual_operator_022
  · exact actual_operator_023
  · exact actual_operator_024
  · exact actual_operator_025
  · exact actual_operator_026
  · exact actual_operator_027
  · exact actual_operator_028
  · exact actual_operator_029
  · exact actual_operator_030
  · exact actual_operator_031
  · exact actual_operator_032
  · exact actual_operator_033
  · exact actual_operator_034
  · exact actual_operator_035
  · exact actual_operator_036
  · exact actual_operator_037
  · exact actual_operator_038
  · exact actual_operator_039
  · exact actual_operator_040
  · exact actual_operator_041
  · exact actual_operator_042
  · exact actual_operator_043
  · exact actual_operator_044
  · exact actual_operator_045
  · exact actual_operator_046
  · exact actual_operator_047
  · exact actual_operator_048
  · exact actual_operator_049
  · exact actual_operator_050
  · exact actual_operator_051
  · exact actual_operator_052
  · exact actual_operator_053
  · exact actual_operator_054
def leftElements (i : Fin 16) : Q := elements (leftIndices i)
def rightElements (i : Fin 16) : Q := elements (rightIndices i)

/-- The actual group-algebra generators, with no presentation quotient. -/
def algebraA : k[Q] := MonoidAlgebra.single (PSL33GoodSets.q a) 1
def algebraB : k[Q] := MonoidAlgebra.single (PSL33GoodSets.q b) 1

def averageElement : k[Q] := ∑ i : Fin 13, (algebraA * algebraB) ^ i.val
def rankOneElement : k[Q] := averageElement

theorem matrix_algebraA : matrixAction representation algebraA = leftA := by
  rw [algebraA, matrixAction_single_one, toMatrix_a]

theorem matrix_algebraB : matrixAction representation algebraB = leftB := by
  rw [algebraB, matrixAction_single_one, toMatrix_b]

theorem matrix_average : matrixAction representation averageElement = average := by
  simp only [averageElement, map_sum, map_pow, map_mul, matrix_algebraA, matrix_algebraB, power_formula]
  exact average_eq.symm

theorem matrix_rankOne : matrixAction representation rankOneElement = rankOne := by
  rw [rankOneElement, matrix_average, ← rankOne_eq]

/-- This is an actual rank-one group-algebra operator, not a supplied density assumption. -/
theorem rank_one_operator :
    LinearMap.toMatrix' (representation.asAlgebraHom rankOneElement) =
      Matrix.vecMulVec column row := matrix_rankOne.trans rankOne_factor

/-- The actual group-algebra action contains every linear operator. -/
theorem asAlgebraHom_surjective : Function.Surjective representation.asAlgebraHom := by
  apply RankOneOperatorSpanCertificate.asAlgebraHom_surjective representation rankOneElement
    leftElements rightElements column row leftInverse rightInverse rank_one_operator
  · have h : cyclicColumns (fun i => LinearMap.toMatrix' (representation (leftElements i)))
        column = leftCyclic := by
      simp only [leftElements, actual_operators]
      exact left_cyclic
    rw [h]
    exact left_inverse.1
  · have h : cyclicRows (fun i => LinearMap.toMatrix' (representation (rightElements i)))
        row = rightCyclic := by
      simp only [rightElements, actual_operators]
      exact right_cyclic
    rw [h]
    exact right_inverse.2

/-- Irreducibility of the actual binary representation. -/
theorem isIrreducible : representation.IsIrreducible :=
  RepresentationDensityBaseChange.isIrreducible_of_asAlgebraHom_surjective
    representation asAlgebraHom_surjective

/-- Full operator image for every actual field extension. -/
theorem baseChange_asAlgebraHom_surjective (L : Type*) [Field L] [Algebra k L] :
    Function.Surjective (RepresentationDensityBaseChange.baseChange L representation).asAlgebraHom :=
  RepresentationDensityBaseChange.baseChange_asAlgebraHom_surjective representation
    asAlgebraHom_surjective

/-- Absolute irreducibility expressed on the actual scalar-extended representation. -/
theorem baseChange_isIrreducible (L : Type*) [Field L] [Algebra k L] :
    (RepresentationDensityBaseChange.baseChange L representation).IsIrreducible :=
  RepresentationDensityBaseChange.baseChange_isIrreducible L representation
    asAlgebraHom_surjective

end Kourovka2135.PSL33ModuleSixteenDensity
