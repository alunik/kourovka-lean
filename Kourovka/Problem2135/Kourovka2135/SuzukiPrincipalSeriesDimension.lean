import Kourovka2135.SuzukiPrincipalSeries
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! The actual principal-series dimension and the properness test needed
for concrete tensor images. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SuzukiPrincipalSeriesDimension

open SuzukiGeometry SuzukiPrincipalSeries SuzukiPrincipalSeriesBorel

variable (m : ℕ) {k : Type u} [Field k] (σ : K m →+* k) (n : ℕ)

theorem finrank_space : Module.finrank k (Space m σ n) = (q m) ^ 2 + 1 := by
  calc
    _ = Nat.card (CoinducedCharacterFormula.RightCosets (borel m)) :=
      CoinducedLinearCharacter.finrank_space (borel m) (character m σ n)
    _ = (borel m).index := Nat.card_congr
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := borel m))
    _ = _ := borel_index m

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {ρ : Representation k (G m) V}

/-- A lower-dimensional actual source cannot fill the principal series. -/
theorem range_ne_top_of_finrank_le (j : ρ.IntertwiningMap (representation m σ n))
    (hdim : Module.finrank k V ≤ (q m) ^ 2) : j.range ≠ ⊤ := by
  intro he
  have hs : Function.Surjective j.toLinearMap := by
    intro f
    have hf : f ∈ j.range := by rw [he]; trivial
    exact hf
  have hd := LinearMap.finrank_le_finrank_of_surjective hs
  rw [finrank_space] at hd
  omega

end Kourovka2135.SuzukiPrincipalSeriesDimension
