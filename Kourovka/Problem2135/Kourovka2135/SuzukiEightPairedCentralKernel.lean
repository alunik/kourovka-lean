import Kourovka2135.SuzukiEightPairedProjection
import Kourovka2135.SuzukiBruhat
import Kourovka2135.SuzukiEightPairedPcData
import Kourovka2135.SuzukiEightPairedUpperBound
import Kourovka2135.CentralDoubleCoverUniqueness

/-! The paired matrix cover has exactly four kernel elements, all central.
The upper bound comes from the explicit coset certificate; the lower bound
uses one matrix entry of four displayed elements. -/

set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace Kourovka2135.SuzukiEightPairedCentralKernel

open SuzukiEightPairedGoodSet SuzukiEightPairedProjection

private theorem code_pc6_one : SuzukiEightCoverCodeMatrices.pc6 = 1 := by
  apply Units.ext
  decide +kernel

private theorem code_pc7_one : SuzukiEightCoverCodeMatrices.pc7 = 1 := by
  apply Units.ext
  decide +kernel

private theorem central_of_commute (g : E)
    (hc : Commute g.val c) (hb : Commute g.val b) :
    g ∈ Subgroup.center E := by
  have h : g.val ∈ Subgroup.centralizer ({c, b} : Set Ambient) := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hc.eq.symm
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact hb.eq.symm
  have hall : g.val ∈ Subgroup.centralizer (coverGroup : Set Ambient) := by
    rw [coverGroup, Subgroup.centralizer_closure]
    exact h
  apply Subgroup.mem_center_iff.mpr
  intro a
  exact Subtype.ext (hall a.val a.property)

theorem pc6_mem_kernel : SuzukiEightPairedPcData.pc6 ∈ projection.ker := by
  rw [mem_kernel_iff]
  exact code_pc6_one

theorem pc7_mem_kernel : SuzukiEightPairedPcData.pc7 ∈ projection.ker := by
  rw [mem_kernel_iff]
  exact code_pc7_one

theorem pc6_central : SuzukiEightPairedPcData.pc6 ∈ Subgroup.center E := by
  apply central_of_commute
  · apply Prod.ext
    · change SuzukiEightCoverCodeMatrices.pc6 * SuzukiEightCoverCodeMatrices.c =
        SuzukiEightCoverCodeMatrices.c * SuzukiEightCoverCodeMatrices.pc6
      rw [code_pc6_one, one_mul, mul_one]
    · exact SuzukiEightCoverPcWords.pc6_commute_c.eq
  · apply Prod.ext
    · change SuzukiEightCoverCodeMatrices.pc6 * SuzukiEightCoverCodeMatrices.b =
        SuzukiEightCoverCodeMatrices.b * SuzukiEightCoverCodeMatrices.pc6
      rw [code_pc6_one, one_mul, mul_one]
    · exact SuzukiEightCoverPcWords.pc6_commute_b.eq

theorem pc7_central : SuzukiEightPairedPcData.pc7 ∈ Subgroup.center E := by
  apply central_of_commute
  · apply Prod.ext
    · change SuzukiEightCoverCodeMatrices.pc7 * SuzukiEightCoverCodeMatrices.c =
        SuzukiEightCoverCodeMatrices.c * SuzukiEightCoverCodeMatrices.pc7
      rw [code_pc7_one, one_mul, mul_one]
    · exact SuzukiEightCoverPcWords.pc7_commute_c.eq
  · apply Prod.ext
    · change SuzukiEightCoverCodeMatrices.pc7 * SuzukiEightCoverCodeMatrices.b =
        SuzukiEightCoverCodeMatrices.b * SuzukiEightCoverCodeMatrices.pc7
      rw [code_pc7_one, one_mul, mul_one]
    · exact SuzukiEightCoverPcWords.pc7_commute_b.eq

def four : Fin 4 → E :=
  ![1, SuzukiEightPairedPcData.pc7, SuzukiEightPairedPcData.pc6,
    SuzukiEightPairedPcData.pc6 * SuzukiEightPairedPcData.pc7]

theorem four_mem_kernel (i : Fin 4) : four i ∈ projection.ker := by
  fin_cases i
  · exact projection.ker.one_mem
  · exact pc7_mem_kernel
  · exact pc6_mem_kernel
  · exact projection.ker.mul_mem pc6_mem_kernel pc7_mem_kernel

theorem four_central (i : Fin 4) : four i ∈ Subgroup.center E := by
  fin_cases i
  · exact (Subgroup.center E).one_mem
  · exact pc7_central
  · exact pc6_central
  · exact (Subgroup.center E).mul_mem pc6_central pc7_central

def signature : Fin 4 → ZMod 5 := ![1, 2, 4, 3]

theorem signature_injective : Function.Injective signature := by decide +kernel

theorem four_entry (i : Fin 4) : (four i).val.2.val 12 12 = signature i := by
  fin_cases i
  · change (1 : SuzukiEightCoverMatrices.M) 12 12 = 1
    decide +kernel
  · change SuzukiEightCoverPcMatrices.pc7Matrix 12 12 = 2
    decide +kernel
  · change SuzukiEightCoverPcMatrices.pc6Matrix 12 12 = 4
    decide +kernel
  · change SuzukiEightCoverPcForms.form003.val 12 12 = 3
    rw [SuzukiEightCoverPcForms.form003_val]
    decide +kernel

def kernelElement (i : Fin 4) : projection.ker := ⟨four i, four_mem_kernel i⟩

theorem kernelElement_injective : Function.Injective kernelElement := by
  intro i j h
  apply signature_injective
  rw [← four_entry i, ← four_entry j]
  exact congrArg (fun g : projection.ker => g.val.val.2.val 12 12) h

theorem card_kernel_ge_four : 4 ≤ Nat.card projection.ker := by
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective kernelElement kernelElement_injective

theorem card_base : Nat.card (SuzukiGeometry.G 1) = 29120 := by
  rw [SuzukiGeometry.card_group]
  norm_num [SuzukiGeometry.q]

theorem card_kernel_le_four : Nat.card projection.ker ≤ 4 := by
  have hcard := CentralDoubleCoverUniqueness.card_eq_card_base_mul_card_ker
    projection projection_surjective
  rw [card_base] at hcard
  have hupper := SuzukiEightPairedUpperBound.card_le
  omega

theorem card_kernel : Nat.card projection.ker = 4 :=
  Nat.le_antisymm card_kernel_le_four card_kernel_ge_four

theorem kernelElement_surjective : Function.Surjective kernelElement :=
  (kernelElement_injective.bijective_of_nat_card_le (by
    rw [Nat.card_fin, card_kernel])).2

theorem kernel_central : projection.ker ≤ Subgroup.center E := by
  intro g hg
  obtain ⟨i, hi⟩ := kernelElement_surjective ⟨g, hg⟩
  have he : four i = g := congrArg Subtype.val hi
  exact he ▸ four_central i

theorem kernel_binary : IsPGroup 2 projection.ker := by
  apply isPGroup_iff_card_dvd_pow.mpr
  refine ⟨2, ?_⟩
  rw [card_kernel]
  decide

end Kourovka2135.SuzukiEightPairedCentralKernel
