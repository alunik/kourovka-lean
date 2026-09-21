import Kourovka2135.MinimalSimpleModels
import Kourovka2135.PSL33OrderObstructions

/-! Explicit even-order witnesses in every concrete minimal-simple model.
No family cardinality formula or classification hypothesis is used here. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups

section PSLTwo
variable (R : Type*) [CommRing R] [Nontrivial R]

def pslTwoInvolutionLift : SL(2, R) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

omit [Nontrivial R] in
theorem pslTwoInvolutionLift_sq_mem_center :
    pslTwoInvolutionLift R ^ 2 ∈ Subgroup.center SL(2, R) := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1, by simp, ?_⟩
  change Matrix.scalar (Fin 2) (-1 : R) = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar]

theorem pslTwoInvolutionLift_not_mem_center :
    pslTwoInvolutionLift R ∉ Subgroup.center SL(2, R) := by
  intro h
  have he := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center h (0 : Fin 2)
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) he
  simp [pslTwoInvolutionLift, Matrix.scalar] at hh

theorem exists_orderOf_eq_two_pslTwo : ∃ x : PSL(2, R), orderOf x = 2 := by
  let q := QuotientGroup.mk' (Subgroup.center SL(2, R))
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨q (pslTwoInvolutionLift R), orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pslTwoInvolutionLift_sq_mem_center R)
  · intro he
    exact pslTwoInvolutionLift_not_mem_center R ((QuotientGroup.eq_one_iff _).mp he)

theorem two_dvd_card_pslTwo : 2 ∣ Nat.card PSL(2, R) := by
  obtain ⟨x, hx⟩ := exists_orderOf_eq_two_pslTwo R
  have h := orderOf_dvd_natCard x
  rwa [hx] at h

end PSLTwo

noncomputable def suzukiInvolution (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem suzukiInvolution_sq (m : ℕ) : suzukiInvolution m ^ 2 = 1 := by
  apply Subtype.ext
  change SuzukiWeylGL m ^ 2 = 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem suzukiInvolution_ne_one (m : ℕ) : suzukiInvolution m ≠ 1 := by
  intro h
  have he := congrArg (fun x : SuzukiMatrixGroup m => x.val.val 0 0) h
  simp [suzukiInvolution, SuzukiWeylGL, SuzukiWeylMatrix] at he

theorem orderOf_suzukiInvolution (m : ℕ) : orderOf (suzukiInvolution m) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (suzukiInvolution_sq m) (suzukiInvolution_ne_one m)

theorem two_dvd_card_suzuki (m : ℕ) : 2 ∣ Nat.card (SuzukiMatrixGroup m) := by
  have h := orderOf_dvd_natCard (suzukiInvolution m)
  rwa [orderOf_suzukiInvolution] at h

theorem two_dvd_card_pslThreeThree : 2 ∣ Nat.card PSL(3, ZMod 3) := by
  have h : 8 ∣ Nat.card PSL(3, ZMod 3) :=
    PSL33OrderObstructions.order_y8 ▸ orderOf_dvd_natCard PSL33GoodSets.y8
  exact (by decide : 2 ∣ 8).trans h

theorem IsMinimalSimpleModel.two_dvd_card
    {G : Type u} [Group G] (h : IsMinimalSimpleModel G) : 2 ∣ Nat.card G := by
  rcases h with ⟨f, _, ⟨e⟩⟩ | ⟨f, _, _, ⟨e⟩⟩ |
    ⟨ell, hp, _, _, he⟩ | ⟨m, _, _, ⟨e⟩⟩ | ⟨e⟩
  · rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_pslTwo _
  · rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_pslTwo _
  · let : Fact ell.Prime := ⟨hp⟩
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_pslTwo _
  · rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_suzuki m
  · obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_pslThreeThree

end Kourovka2135
