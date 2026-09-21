import Kourovka2135.CoinducedLinearCharacter
import Kourovka2135.MonomialDeterminant

/-! An actual character of binary exponent induces determinant-one operators
at odd-order elements. Right multiplication gives the actual coordinate
permutation, and the coefficients are evaluations of the inducing character.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CoinducedBinaryDeterminant

open CoinducedCharacterFormula CoinducedLinearCharacter

variable {G k : Type*} [Group G] [Field k]

def rightTranslate (S : Subgroup G) (g : G) : RightCosets S → RightCosets S :=
  Quotient.map (fun h => h * g) (by
    intro x y h
    change (QuotientGroup.rightRel S).r x y at h
    change (QuotientGroup.rightRel S).r (x * g) (y * g)
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h)

@[simp] theorem rightTranslate_mk (S : Subgroup G) (g h : G) :
    rightTranslate S g (Quotient.mk (QuotientGroup.rightRel S) h) =
      Quotient.mk (QuotientGroup.rightRel S) (h * g) := rfl

/-- The actual right-coset coordinate permutation. -/
def rightPermutation (S : Subgroup G) (g : G) : Equiv.Perm (RightCosets S) where
  toFun := rightTranslate S g
  invFun := rightTranslate S g⁻¹
  left_inv q := by
    induction q using Quotient.inductionOn with | _ h =>
      simp only [rightTranslate_mk, mul_inv_cancel_right]
  right_inv q := by
    induction q using Quotient.inductionOn with | _ h =>
      simp only [rightTranslate_mk, inv_mul_cancel_right]

theorem rightPermutation_out (S : Subgroup G) (g : G) (q : RightCosets S) :
    rightPermutation S g q =
      Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) := by
  change rightTranslate S g q = _
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

variable [Finite G]

/-- Binary coefficient powers and the actual odd operator power force determinant one. -/
theorem det_induced_eq_one_of_odd_pow
    (S : Subgroup G) (χ : S →* kˣ) (r : ℕ)
    (hχ : ∀ s : S, χ s ^ (2 ^ r) = 1)
    (g : G) (m : ℕ) (hm : Odd m) (hgm : g ^ m = 1) :
    LinearMap.det (induced S χ g) = 1 := by
  classical
  let e := coindVEquivQuotient S (linear S χ)
  let L := coindCoordinateEnd S (linear S χ) g
  let a : RightCosets S → k := fun q => (χ (rightCosetCorrection S (Quotient.out q * g)) : k)
  have hL : ∀ (x : RightCosets S → k) (q : RightCosets S),
      L x q = a q * x (rightPermutation S g q) := by
    intro x q
    rw [rightPermutation_out]
    rfl
  have ha : ∀ q, a q ^ (2 ^ r) = 1 := by
    intro q
    exact congrArg (fun u : kˣ => (u : k)) (hχ (rightCosetCorrection S (Quotient.out q * g)))
  have hpow : L ^ m = 1 := by
    change (e.conjRingEquiv (induced S χ g)) ^ m = 1
    rw [← map_pow, ← map_pow, hgm, map_one, map_one]
  have hdet := MonomialDeterminant.det_eq_one_of_odd_pow
    L (rightPermutation S g) a hL r m ha hm hpow
  change LinearMap.det (e.conj (induced S χ g)) = 1 at hdet
  exact (LinearMap.det_conj (induced S χ g) e).symm.trans hdet

theorem det_induced_eq_one_of_odd_orderOf
    (S : Subgroup G) (χ : S →* kˣ) (r : ℕ)
    (hχ : ∀ s : S, χ s ^ (2 ^ r) = 1)
    (g : G) (hg : Odd (orderOf g)) : LinearMap.det (induced S χ g) = 1 :=
  det_induced_eq_one_of_odd_pow S χ r hχ g (orderOf g) hg (pow_orderOf_eq_one g)

end Kourovka2135.CoinducedBinaryDeterminant
