import Kourovka2135.SuzukiEightCoverCodeForms
import Kourovka2135.SuzukiRootCoordinates
import Mathlib.Tactic

/-! Canonical code matrices generate the actual Suzuki group of order 29120.
The 64 root cases and seven torus cases below are exhaustive finite kernel
certificates; no presentation or enumeration-completeness assumption is used.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Kourovka2135.SuzukiEightCodeGeometry
open SuzukiEightCodeField SuzukiEightCoverCodeMatrices
open BenderSuzuki.MatrixGroups

def rootMatrix (a b : Element) : M :=
  !![1, a, b, a ^ 6 + a * b + b ^ 4;
     0, 1, a ^ 4, a ^ 5 + b;
     0, 0, 1, a;
     0, 0, 0, 1]

def torusMatrixPositive (a : Element) : M :=
  !![a ^ 3, 0, 0, 0; 0, a ^ 2, 0, 0;
     0, 0, a ^ 5, 0; 0, 0, 0, a ^ 4]

theorem b_rootMatrix : bMatrix = rootMatrix alpha 0 := by decide +kernel
theorem c_square_matrix : cMatrix * cMatrix = 1 := by decide +kernel
theorem b_fourth_matrix : bMatrix * bMatrix * bMatrix * bMatrix = 1 := by
  decide +kernel

theorem c_square : c ^ 2 = 1 := by
  apply Units.ext
  change cMatrix ^ 2 = (1 : M)
  simpa only [pow_two] using c_square_matrix

theorem b_fourth : b ^ 4 = 1 := by
  apply Units.ext
  change bMatrix ^ 4 = (1 : M)
  simpa only [pow_succ, pow_zero, one_mul] using b_fourth_matrix

theorem pc0_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    pc0 ∈ H := by

  rw [← pc0_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb hc) hb) hc) hb) hb) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) hb) hb) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc) hb)

theorem pc1_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    pc1 ∈ H := by

  rw [← pc1_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) hb) hc) (H.inv_mem hb)) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc) (H.inv_mem hb)) hc) hb) hc) hb)

theorem pc2_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    pc2 ∈ H := by

  rw [← pc2_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb hb) hc) hb) hb) hc) hb) hb) hc) hb) hc) hb) hb) hc) hb) hb) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc)

theorem pc3_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    pc3 ∈ H := by

  rw [← pc3_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb hc) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) hb)

theorem pc4_mem (H : Subgroup UnitMatrix) (_hc : c ∈ H) (hb : b ∈ H) :
    pc4 ∈ H := by

  rw [← pc4_from_cb]
  exact (H.mul_mem hb hb)

theorem pc5_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    pc5 ∈ H := by

  rw [← pc5_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hc (H.inv_mem hb)) hc) hb) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc)

theorem torus_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H) :
    torus ∈ H := by
  rw [← torus_from_cb]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hc hb) hc) (H.inv_mem hb)) hc) (H.inv_mem hb)) hc) hb) hc) (H.inv_mem hb)) hc) hb) hc) hb) hb) hc) (H.inv_mem hb)) hc) hb) hb)

def rootIndex (a b : Fin 8) : Fin 256 :=
  ![![0, 4, 8, 12, 16, 20, 24, 28],
    ![32, 36, 40, 44, 48, 52, 56, 60],
    ![64, 68, 72, 76, 80, 84, 88, 92],
    ![104, 108, 96, 100, 120, 124, 112, 116],
    ![128, 132, 136, 140, 144, 148, 152, 156],
    ![176, 180, 184, 188, 160, 164, 168, 172],
    ![212, 208, 220, 216, 196, 192, 204, 200],
    ![236, 232, 228, 224, 252, 248, 244, 240]] a b

def rootWitness (a b : Fin 8) : UnitMatrix :=
  SuzukiEightCoverCodeForms.form (rootIndex a b)

theorem rootWitness_val (a b : Fin 8) :
    (rootWitness a b : M) = rootMatrix (ofCode a) (ofCode b) := by
  change (SuzukiEightCoverCodeForms.form (rootIndex a b)).val = _
  rw [SuzukiEightCoverCodeForms.form_val]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rootWitness_mem (H : Subgroup UnitMatrix) (hc : c ∈ H) (hb : b ∈ H)
    (a b : Fin 8) : rootWitness a b ∈ H := by
  have hpc0 := pc0_mem H hc hb
  have hpc1 := pc1_mem H hc hb
  have hpc2 := pc2_mem H hc hb
  have hpc3 := pc3_mem H hc hb
  have hpc4 := pc4_mem H hc hb
  have hpc5 := pc5_mem H hc hb
  fin_cases a <;> fin_cases b
  · exact H.one_mem
  · exact hpc5
  · exact hpc4
  · exact (H.mul_mem hpc4 hpc5)
  · exact hpc3
  · exact (H.mul_mem hpc3 hpc5)
  · exact (H.mul_mem hpc3 hpc4)
  · exact (H.mul_mem (H.mul_mem hpc3 hpc4) hpc5)
  · exact hpc2
  · exact (H.mul_mem hpc2 hpc5)
  · exact (H.mul_mem hpc2 hpc4)
  · exact (H.mul_mem (H.mul_mem hpc2 hpc4) hpc5)
  · exact (H.mul_mem hpc2 hpc3)
  · exact (H.mul_mem (H.mul_mem hpc2 hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc2 hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc2 hpc3) hpc4) hpc5)
  · exact hpc1
  · exact (H.mul_mem hpc1 hpc5)
  · exact (H.mul_mem hpc1 hpc4)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc4) hpc5)
  · exact (H.mul_mem hpc1 hpc3)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc1 hpc3) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc2) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc1 hpc2) hpc4) hpc5)
  · exact (H.mul_mem hpc1 hpc2)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc2) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc1 hpc2) hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc1 hpc2) hpc3) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc1 hpc2) hpc3)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc1 hpc2) hpc3) hpc5)
  · exact hpc0
  · exact (H.mul_mem hpc0 hpc5)
  · exact (H.mul_mem hpc0 hpc4)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc4) hpc5)
  · exact (H.mul_mem hpc0 hpc3)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc3) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc2) hpc3)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc2) hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc2) hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc2) hpc3) hpc4) hpc5)
  · exact (H.mul_mem hpc0 hpc2)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc2) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc2) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc2) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc1) hpc3)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc3) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc1) hpc5)
  · exact (H.mul_mem hpc0 hpc1)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc1) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc5)
  · exact (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc3) hpc4) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc3) hpc4)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc3) hpc5)
  · exact (H.mul_mem (H.mul_mem (H.mul_mem hpc0 hpc1) hpc2) hpc3)

def torusExponent (a : Fin 8) : ℕ :=
  ![0, 0, 5, 1, 3, 2, 6, 4] a

theorem torusWitness_val (a : Fin 8) (ha : a ≠ 0) :
    ((torus ^ torusExponent a : UnitMatrix) : M) =
      torusMatrixPositive (ofCode a) := by
  fin_cases a
  · exact False.elim (ha rfl)
  all_goals decide +kernel

theorem seventh_power (a : Fin 8) (ha : a ≠ 0) : (ofCode a) ^ 7 = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  all_goals decide +kernel

abbrev ActualUnitMatrix := Matrix.GeneralLinearGroup (Fin 4) (SuzukiGeometry.K 1)

/-- Entrywise application of the proved finite-field equivalence. -/
def actualMap : UnitMatrix →* ActualUnitMatrix :=
  Matrix.GeneralLinearGroup.map actualEquiv.toRingHom

def actualC : ActualUnitMatrix := SuzukiWeylGL 1
def actualB : ActualUnitMatrix := SuzukiRootGL 1 actualAlpha 0

theorem actualMap_c : actualMap c = actualC := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualMap, Matrix.GeneralLinearGroup.map, c, cMatrix,
      actualC, SuzukiWeylGL, SuzukiWeylMatrix]

theorem map_rootMatrix (a b : Element) :
    (rootMatrix a b).map actualEquiv =
      SuzukiRootMatrix 1 (actualEquiv a) (actualEquiv b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, SuzukiRootMatrix, Matrix.map_apply]

theorem actualMap_b : actualMap b = actualB := by
  apply Units.ext
  change bMatrix.map actualEquiv = SuzukiRootMatrix 1 actualAlpha 0
  rw [b_rootMatrix, map_rootMatrix]
  simp only [map_zero, actualAlpha]

theorem actualMap_rootWitness (a b : Fin 8) :
    actualMap (rootWitness a b) =
      SuzukiRootGL 1 (actualEquiv (ofCode a)) (actualEquiv (ofCode b)) := by
  apply Units.ext
  change (rootWitness a b : M).map actualEquiv = _
  rw [rootWitness_val, map_rootMatrix]
  rfl

theorem map_torusMatrixPositive (a : Fin 8) (ha : a ≠ 0)
    (x : (SuzukiGeometry.K 1)ˣ) (hx : actualEquiv (ofCode a) = x) :
    (torusMatrixPositive (ofCode a)).map actualEquiv = SuzukiTorusMatrix 1 x := by
  have hseven : (x : SuzukiGeometry.K 1) ^ 7 = 1 := by
    simpa only [map_pow, map_one, hx] using congrArg actualEquiv (seventh_power a ha)
  have hinv2 : ((x : SuzukiGeometry.K 1) ^ 2)⁻¹ = (x : SuzukiGeometry.K 1) ^ 5 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_add] using hseven
  have hinv3 : ((x : SuzukiGeometry.K 1) ^ 3)⁻¹ = (x : SuzukiGeometry.K 1) ^ 4 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_add] using hseven
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrixPositive, SuzukiTorusMatrix, Matrix.map_apply, hx, hinv2, hinv3]

theorem actualMap_torusWitness (a : Fin 8) (ha : a ≠ 0)
    (x : (SuzukiGeometry.K 1)ˣ) (hx : actualEquiv (ofCode a) = x) :
    actualMap (torus ^ torusExponent a) = SuzukiTorusGL 1 x := by
  apply Units.ext
  change ((torus ^ torusExponent a : UnitMatrix) : M).map actualEquiv = _
  rw [torusWitness_val a ha, map_torusMatrixPositive a ha x hx]
  rfl

theorem actualC_mem : actualC ∈ SuzukiMatrixSubgroup 1 :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem actualB_mem : actualB ∈ SuzukiMatrixSubgroup 1 :=
  Subgroup.subset_closure (Or.inl ⟨actualAlpha, 0, rfl⟩)

/-- Every actual root and torus generator lies in any subgroup containing C,B. -/
theorem actual_subgroup_le (H : Subgroup ActualUnitMatrix)
    (hc : actualC ∈ H) (hb : actualB ∈ H) : SuzukiMatrixSubgroup 1 ≤ H := by
  have hc' : c ∈ H.comap actualMap := by simpa only [Subgroup.mem_comap, actualMap_c] using hc
  have hb' : b ∈ H.comap actualMap := by simpa only [Subgroup.mem_comap, actualMap_b] using hb
  apply (Subgroup.closure_le _).2
  intro g hg
  rcases hg with ⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl
  · let ac : Element := actualEquiv.symm a
    let bc : Element := actualEquiv.symm b
    have ha : actualEquiv (ofCode ac.code) = a := actualEquiv.apply_symm_apply a
    have hb : actualEquiv (ofCode bc.code) = b := actualEquiv.apply_symm_apply b
    have h := rootWitness_mem (H.comap actualMap) hc' hb' ac.code bc.code
    change actualMap (rootWitness ac.code bc.code) ∈ H at h
    change SuzukiRootGL 1 a b ∈ H
    simpa only [actualMap_rootWitness, ha, hb] using h
  · let ac : Element := actualEquiv.symm (x : SuzukiGeometry.K 1)
    have ha : actualEquiv (ofCode ac.code) = x := actualEquiv.apply_symm_apply x
    have hne : ac.code ≠ 0 := by
      intro h
      have hz : (x : SuzukiGeometry.K 1) = 0 := by simpa only [h, ofCode_zero, map_zero] using ha.symm
      exact x.ne_zero hz
    have h := (H.comap actualMap).pow_mem (torus_mem (H.comap actualMap) hc' hb')
      (torusExponent ac.code)
    change actualMap (torus ^ torusExponent ac.code) ∈ H at h
    change SuzukiTorusGL 1 x ∈ H
    simpa only [actualMap_torusWitness ac.code hne x ha] using h
  · exact hc

theorem actual_generates :
    Subgroup.closure ({actualC, actualB} : Set ActualUnitMatrix) = SuzukiMatrixSubgroup 1 := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact actualC_mem
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact actualB_mem
  · exact actual_subgroup_le _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

def C : SuzukiGeometry.G 1 := ⟨actualC, actualC_mem⟩
def B : SuzukiGeometry.G 1 := ⟨actualB, actualB_mem⟩

theorem generates : Subgroup.closure ({C, B} : Set (SuzukiGeometry.G 1)) = ⊤ := by
  let H := Subgroup.closure ({C, B} : Set (SuzukiGeometry.G 1))
  have hmap : H.map (SuzukiMatrixSubgroup 1).subtype = SuzukiMatrixSubgroup 1 := by
    dsimp [H]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, C, B, Subgroup.coe_subtype] using actual_generates
  apply top_unique
  intro g _
  have hg : (g : ActualUnitMatrix) ∈ H.map (SuzukiMatrixSubgroup 1).subtype := by
    rw [hmap]
    exact g.property
  obtain ⟨h, hh, he⟩ := hg
  have he' : h = g := Subtype.ext he
  exact he' ▸ hh

theorem C_sq : C ^ 2 = 1 := by
  apply Subtype.ext
  change actualC ^ 2 = 1
  rw [← actualMap_c, ← map_pow, c_square, map_one]

theorem B_fourth : B ^ 4 = 1 := by
  apply Subtype.ext
  change actualB ^ 4 = 1
  rw [← actualMap_b, ← map_pow, b_fourth, map_one]

end Kourovka2135.SuzukiEightCodeGeometry
