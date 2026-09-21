import Kourovka2135.PSLThreeThreeSemidihedralData

/-! An order-four generating good class in the actual SL(3,3).
The untrusted search supplies short words only. Lean checks each matrix product,
then reuses the proved generation by the original order-eight pair. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Kourovka2135.SL33OrderFourGoodSet
open Matrix
open scoped MatrixGroups
abbrev S := SL(3, ZMod 3)

def a : S := ⟨!![0, 1, 0; 2, 0, 0; 0, 0, 1], by decide⟩
def b : S := ⟨!![0, 0, 1; 0, 2, 1; 1, 2, 2], by decide⟩
def s : S := ⟨!![1, 2, 1; 1, 0, 2; 1, 1, 1], by decide⟩
def t : S := ⟨!![1, 2, 2; 2, 2, 1; 1, 1, 0], by decide⟩
def first1 : S := ⟨!![0, 1, 0; 2, 0, 0; 0, 0, 1], by decide⟩
def first2 : S := ⟨!![0, 2, 1; 0, 0, 2; 1, 2, 2], by decide⟩
def first3 : S := ⟨!![1, 0, 1; 0, 0, 2; 1, 1, 2], by decide⟩
def first4 : S := ⟨!![1, 2, 0; 2, 1, 1; 2, 0, 0], by decide⟩
def first5 : S := ⟨!![2, 2, 0; 1, 1, 1; 0, 1, 0], by decide⟩
def first6 : S := ⟨!![0, 2, 2; 1, 1, 1; 1, 2, 0], by decide⟩
def first7 : S := ⟨!![1, 0, 2; 2, 1, 1; 1, 1, 0], by decide⟩
def first8 : S := ⟨!![2, 1, 2; 1, 1, 2; 0, 2, 2], by decide⟩
def first9 : S := ⟨!![1, 1, 2; 1, 2, 2; 2, 0, 2], by decide⟩
def first10 : S := ⟨!![2, 1, 1; 0, 0, 1; 0, 1, 2], by decide⟩

theorem a8_mem (H : Subgroup S) (ha : a ∈ H) (hb : b ∈ H) :
    SL33Witnesses.a8 ∈ H := by
  have e1 : (1 : S) * a = first1 := by decide
  have h1 : first1 ∈ H := e1 ▸ H.mul_mem H.one_mem ha
  have e2 : first1 * b = first2 := by decide
  have h2 : first2 ∈ H := e2 ▸ H.mul_mem h1 hb
  have e3 : first2 * a = first3 := by decide
  have h3 : first3 ∈ H := e3 ▸ H.mul_mem h2 ha
  have e4 : first3 * b = first4 := by decide
  have h4 : first4 ∈ H := e4 ▸ H.mul_mem h3 hb
  have e5 : first4 * a⁻¹ = first5 := by decide
  have h5 : first5 ∈ H := e5 ▸ H.mul_mem h4 (H.inv_mem ha)
  have e6 : first5 * b⁻¹ = first6 := by decide
  have h6 : first6 ∈ H := e6 ▸ H.mul_mem h5 (H.inv_mem hb)
  have e7 : first6 * a = first7 := by decide
  have h7 : first7 ∈ H := e7 ▸ H.mul_mem h6 ha
  have e8 : first7 * b = first8 := by decide
  have h8 : first8 ∈ H := e8 ▸ H.mul_mem h7 hb
  have e9 : first8 * a⁻¹ = first9 := by decide
  have h9 : first9 ∈ H := e9 ▸ H.mul_mem h8 (H.inv_mem ha)
  have e10 : first9 * b⁻¹ = first10 := by decide
  have h10 : first10 ∈ H := e10 ▸ H.mul_mem h9 (H.inv_mem hb)
  exact (by decide : first10 = SL33Witnesses.a8) ▸ h10

def second1 : S := ⟨!![0, 0, 1; 0, 2, 1; 1, 2, 2], by decide⟩
def second2 : S := ⟨!![0, 0, 1; 2, 0, 1; 2, 2, 2], by decide⟩
def second3 : S := ⟨!![1, 0, 0; 2, 1, 2; 2, 2, 2], by decide⟩
def second4 : S := ⟨!![0, 2, 0; 1, 1, 2; 2, 1, 2], by decide⟩
def second5 : S := ⟨!![2, 1, 0; 2, 1, 1; 1, 0, 2], by decide⟩
def second6 : S := ⟨!![2, 2, 0; 2, 2, 1; 0, 1, 2], by decide⟩
def second7 : S := ⟨!![0, 2, 2; 1, 2, 2; 0, 2, 0], by decide⟩
def second8 : S := ⟨!![2, 0, 2; 2, 2, 2; 2, 0, 0], by decide⟩
def second9 : S := ⟨!![2, 1, 0; 2, 2, 2; 0, 0, 2], by decide⟩
def second10 : S := ⟨!![2, 2, 0; 1, 2, 2; 0, 0, 2], by decide⟩
def second11 : S := ⟨!![1, 2, 0; 1, 1, 2; 0, 0, 2], by decide⟩

theorem b8_mem (H : Subgroup S) (ha : a ∈ H) (hb : b ∈ H) :
    SL33Witnesses.b8 ∈ H := by
  have e1 : (1 : S) * b = second1 := by decide
  have h1 : second1 ∈ H := e1 ▸ H.mul_mem H.one_mem hb
  have e2 : second1 * a⁻¹ = second2 := by decide
  have h2 : second2 ∈ H := e2 ▸ H.mul_mem h1 (H.inv_mem ha)
  have e3 : second2 * b⁻¹ = second3 := by decide
  have h3 : second3 ∈ H := e3 ▸ H.mul_mem h2 (H.inv_mem hb)
  have e4 : second3 * a⁻¹ = second4 := by decide
  have h4 : second4 ∈ H := e4 ▸ H.mul_mem h3 (H.inv_mem ha)
  have e5 : second4 * b⁻¹ = second5 := by decide
  have h5 : second5 ∈ H := e5 ▸ H.mul_mem h4 (H.inv_mem hb)
  have e6 : second5 * a = second6 := by decide
  have h6 : second6 ∈ H := e6 ▸ H.mul_mem h5 ha
  have e7 : second6 * b⁻¹ = second7 := by decide
  have h7 : second7 ∈ H := e7 ▸ H.mul_mem h6 (H.inv_mem hb)
  have e8 : second7 * a⁻¹ = second8 := by decide
  have h8 : second8 ∈ H := e8 ▸ H.mul_mem h7 (H.inv_mem ha)
  have e9 : second8 * b = second9 := by decide
  have h9 : second9 ∈ H := e9 ▸ H.mul_mem h8 hb
  have e10 : second9 * a = second10 := by decide
  have h10 : second10 ∈ H := e10 ▸ H.mul_mem h9 ha
  have e11 : second10 * a = second11 := by decide
  have h11 : second11 ∈ H := e11 ▸ H.mul_mem h10 ha
  exact (by decide : second11 = SL33Witnesses.b8) ▸ h11

theorem generating : Subgroup.closure ({a, b} : Set S) = ⊤ := by
  let H := Subgroup.closure ({a, b} : Set S)
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  apply top_le_iff.mp
  rw [← SL33Witnesses.generating8]
  apply (Subgroup.closure_le H).mpr
  intro x hx
  rcases hx with rfl | ⟨rfl⟩
  · exact a8_mem H ha hb
  · exact b8_mem H ha hb

theorem conjugate : s⁻¹ * a * s = b := by decide
theorem commutator : paperCommutator a b = t⁻¹ * a * t := by decide

theorem goodClass : IsGeneratingGoodSet (conjugatesOf a) := by
  apply isGeneratingGoodSet_conjugatesOf_of_certificate a s t
  · rw [conjugate, commutator]
  · rw [conjugate, generating]

theorem orderOf_a : orderOf a = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1)
    (by decide : a ^ 2 ≠ 1) (by decide : a ^ 4 = 1)

theorem mem_subgroup : a ∈ PSLThreeThreeSemidihedralData.subgroup := by
  change a ∈ PSLThreeThreeSemidihedralData.elements
  decide

theorem normalizes : a ∈ Subgroup.normalizer
    (PSLThreeThreeSemidihedralData.subgroup : Set S) :=
  PSLThreeThreeSemidihedralData.subgroup.le_normalizer mem_subgroup

theorem double_commutator_ne_one :
    paperCommutator a (PSLThreeThreeSemidihedralData.x⁻¹ * a *
      PSLThreeThreeSemidihedralData.x) ≠ 1 := by decide

end Kourovka2135.SL33OrderFourGoodSet
