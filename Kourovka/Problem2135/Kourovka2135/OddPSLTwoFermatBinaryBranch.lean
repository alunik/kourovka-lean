import Kourovka2135.OddPSLTwoPrimeTraceBranch
import Kourovka2135.OddPSLTwoFermatGeneration
import Kourovka2135.BinarySLTwoMinimalException

/-! The Fermat-parameter binary least-exception branch. The only theorem
parameter is the permitted minimal-simple classification; all matrix
generation, conjugate-power bounds and Frattini lifting are proved. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open OddPSLTwoProjectiveChart

theorem OrderMinimalException.false_of_binary_fermat_pslTwo_quotient
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G)
    (F : Type) [Field F] [Finite F]
    (hp : (Nat.card F).Prime) (hsize : 17 ≤ Nat.card F)
    (hfermat : ∃ n : ℕ, Nat.card F - 1 = 2 ^ n)
    (e : (G ⧸ solubleRadical G) ≃* Q F) : False := by
  have hodd : Odd (Nat.card F) := hp.odd_of_ne_two (by omega)
  obtain ⟨n, hn⟩ := hfermat
  have hcard : Nat.card Fˣ = 2 ^ n := by rwa [Nat.card_units]
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable_two classification)
  obtain ⟨s, hs4, hs, hns, hgen⟩ :=
    OddPSLTwoFermatGeneration.exists_generating_parameter F hodd n hcard hsize hsolv
  exact h.false_of_binary_prime_pslTwo_matrix_generation F hp hodd hsize
    s hs hs4 hns hgen e

end Kourovka2135
