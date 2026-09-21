import Kourovka2135.SuzukiPairWeightCollisions
import Kourovka2135.BinaryEvenIntervals
import Kourovka2135.SuzukiPairWeightFinite

/-! Actual natural-weight differences and injectivity of the sixteen pair
weights outside the two exceptional twist gaps. -/

set_option autoImplicit false
namespace Kourovka2135.SuzukiNaturalWeightDifferences

open BinaryWeights BinaryCyclicIntervals BinaryEvenIntervals SuzukiPairWeightCollisions
open Finset BinaryCyclicRotations

private theorem power_square (m : ℕ) : 2^(2*m+1) = 2*(2^m)^2 := by
  rw [show 2*m+1 = m*2+1 by omega, pow_add, pow_mul]
  ring

private theorem radius_ge {m : ℕ} (hm : 2 ≤ m) : 4 ≤ 2^m := by
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm

theorem baseValue_strictMono {r : ℕ} (hr : 4 ≤ r) : StrictMono (baseValue r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [baseValue] at *
  all_goals omega

theorem baseValue_lt_modulus {m : ℕ} (hm : 2 ≤ m) (i : Fin 4) :
    baseValue (2^m) i < 2^(2*m+1)-1 := by
  have hr := radius_ge hm
  have hv : baseValue (2^m) i ≤ 2*(2^m)+2 := by
    fin_cases i <;> norm_num [baseValue]
  have hp := Nat.mul_le_mul_right (2^m) hr
  have hsub := Nat.sub_add_cancel (show 1 ≤ 2*(2^m)^2 by
    have hp : 0 < 2*(2^m)^2 := by positivity
    omega)
  rw [power_square]
  nlinarith

theorem baseWeight_injective {m : ℕ} (hm : 2 ≤ m) : Function.Injective (baseWeight m) := by
  intro i j he
  have hcast : (baseValue (2^m) i : Residue m) = baseValue (2^m) j := by
    unfold baseWeight at he
    linear_combination he
  have hn := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact (baseValue_strictMono (radius_ge hm)).injective
    (hn.eq_of_lt_of_lt (baseValue_lt_modulus hm i) (baseValue_lt_modulus hm j))

theorem two_pow_cycle (m : ℕ) : (2 : Residue m)^(2*m+1) = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (two_pow_modEq_reduced (2*m+1) (2*m+1))
  simpa only [Nat.mod_self, pow_zero, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using h

theorem two_pow_mul_injective {m j : ℕ} (hj : j ≤ 2*m+1) :
    Function.Injective (fun x : Residue m => 2^j*x) := by
  have hinv : (2 : Residue m)^((2*m+1)-j) * 2^j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, two_pow_cycle]
  intro x y h
  change (2 : Residue m)^j*x = 2^j*y at h
  calc
    x = ((2 : Residue m)^((2*m+1)-j) * 2^j) * x := by rw [hinv, one_mul]
    _ = 2^((2*m+1)-j) * (2^j*x) := mul_assoc _ _ _
    _ = 2^((2*m+1)-j) * (2^j*y) := by rw [h]
    _ = y := by rw [← mul_assoc, hinv, one_mul]

def pairValue (m j : ℕ) (p : Fin 4 × Fin 4) : Residue m :=
  baseWeight m p.1 + 2^j*baseWeight m p.2

/-- Outside the proved exceptional gaps, all sixteen actual pair weights
are distinct. -/
theorem pairValue_injective {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2*m+1)
    (hj0 : j ≠ 0) (hjm : j ≠ m) (hjm1 : j ≠ m+1) :
    Function.Injective (pairValue m j) := by
  intro p q he
  by_cases hfirst : p.1 = q.1
  · apply Prod.ext hfirst
    apply baseWeight_injective hm
    apply two_pow_mul_injective (Nat.le_of_lt hj)
    unfold pairValue at he
    rw [hfirst] at he
    exact add_left_cancel he
  · have hsecond : q.2 ≠ p.2 := by
      intro hsame
      apply hfirst
      apply baseWeight_injective hm
      unfold pairValue at he
      rw [hsame] at he
      exact add_right_cancel he
    have hdiff : baseWeight m p.1 - baseWeight m q.1 =
        2^j*(baseWeight m q.2 - baseWeight m p.2) := by
      unfold pairValue at he
      linear_combination he
    rcases difference_rotation_gap hm hj p.1 q.1 q.2 p.2 hfirst hsecond hdiff with
      h | h | h
    · exact False.elim (hj0 h)
    · exact False.elim (hjm h)
    · exact False.elim (hjm1 h)

/-- Small natural differences cannot wrap around the binary torus modulus,
so their binary block identity is an ordinary integer identity. -/
theorem natural_difference_isBlock {m a b d : ℕ} (hm : 2 ≤ m)
    (ha : a < 2*m+1) (hb : b < 2*m+1) (hd : 0 < d) (hdle : d ≤ 2*(2^m)+2)
    (h : (d : Residue m) = 2^a - 2^b) : IsBlock d := by
  have hr := radius_ge hm
  have hpb : 2^b ≤ (2^m)^2 := by
    have hh : b ≤ m*2 := by omega
    simpa only [pow_mul] using Nat.pow_le_pow_right (by decide : 0 < 2) hh
  have hprod := Nat.mul_le_mul_right (2^m) (show 4 ≤ 2^m from hr)
  have hsub := Nat.sub_add_cancel (show 1 ≤ 2*(2^m)^2 by
    have hp : 0 < 2*(2^m)^2 := by positivity
    omega)
  have hsumlt : d + 2^b < 2^(2*m+1)-1 := by
    rw [power_square]
    nlinarith
  have hcast : ((d+2^b : ℕ) : Residue m) = (2^a : ℕ) := by
    push_cast
    linear_combination h
  have he := ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast).eq_of_lt_of_lt
    hsumlt (two_pow_lt_modulus (by omega) ha)
  refine ⟨a,b,?_,he⟩
  by_contra hh
  have hle : 2^a ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem not_block_residue_one_two {d : ℕ} (hd : 8 ≤ d)
    (hres : d%16 = 1 ∨ d%16 = 2) : ¬ IsBlock d := by
  rintro ⟨a,b,_,he⟩
  have hb : 0 < 2^b := by positivity
  have ha16 : 2^a%16 = 0 := by
    rcases power_mod_sixteen a with h | h | h | h | h
    all_goals omega
  rcases power_mod_sixteen b with h | h | h | h | h
  all_goals omega

private theorem nonadjacent_residue {r : ℕ} (hr : 8 ≤ r) (hdiv : 8 ∣ r)
    (i j : Fin 4) (hij : i < j) (hne : j.val ≠ i.val+1) :
    8 ≤ baseValue r j - baseValue r i ∧
      ((baseValue r j - baseValue r i)%16 = 1 ∨
       (baseValue r j - baseValue r i)%16 = 2) := by
  obtain ⟨t, rfl⟩ := hdiv
  fin_cases i <;> fin_cases j <;> norm_num [baseValue] at * <;> omega

/-- Only adjacent entries of the four natural weights can have a Frobenius
power difference. This supplies the row-path condition in the grid count. -/
theorem adjacent_of_frobenius_difference {m a b : ℕ} (hm : 3 ≤ m)
    (ha : a < 2*m+1) (hb : b < 2*m+1) (i j : Fin 4) (hij : i < j)
    (h : baseWeight m j - baseWeight m i = (2 : Residue m)^a - 2^b) :
    j.val = i.val+1 := by
  have hr : 8 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hdiv : 8 ∣ 2^m := by
    refine ⟨2^(m-3), ?_⟩
    conv_lhs => rw [show m = 3+(m-3) by omega, pow_add]
    norm_num
  have hv := baseValue_strictMono (by omega : 4 ≤ 2^m) hij
  let d := baseValue (2^m) j - baseValue (2^m) i
  have hd : 0 < d := by dsimp [d]; omega
  have hdle : d ≤ 2*(2^m)+2 := by
    have hvj : baseValue (2^m) j ≤ 2*(2^m)+2 := by
      fin_cases j <;> norm_num [baseValue]
    dsimp [d]
    omega
  have he : (d : Residue m) = 2^a - 2^b := by
    dsimp [d]
    rw [Nat.cast_sub (Nat.le_of_lt hv)]
    unfold baseWeight at h
    linear_combination h
  have hblock := natural_difference_isBlock (by omega) ha hb hd hdle he
  by_contra hne
  obtain ⟨hd8, hres⟩ := nonadjacent_residue hr hdiv i j hij hne
  exact not_block_residue_one_two hd8 hres hblock

/-- The two differences forced by an outer and a middle selected row edge.
Their binary support sizes are `m` and `m+2`. -/
def mixedSupport (m : ℕ) (upper : Bool) : Finset ℕ :=
  if upper then range (m+2) else Ico 1 (m+1)

theorem mixedSupport_subset {m : ℕ} (hm : 2 ≤ m) (upper : Bool) :
    mixedSupport m upper ⊆ range (2*m+1) := by
  intro i hi
  cases upper
  · simp only [mixedSupport, Bool.false_eq_true, ↓reduceIte, mem_Ico] at hi
    exact mem_range.mpr (by omega)
  · simp only [mixedSupport, ↓reduceIte, mem_range] at hi
    exact mem_range.mpr (by omega)

theorem mixedSupport_card (m : ℕ) (upper : Bool) :
    (mixedSupport m upper).card = if upper then m+2 else m := by
  cases upper <;> simp [mixedSupport]

theorem mixedSupport_ne_range {m : ℕ} (hm : 2 ≤ m) (upper : Bool) :
    mixedSupport m upper ≠ range (2*m+1) := by
  intro he
  have hc := congrArg Finset.card he
  rw [mixedSupport_card, card_range] at hc
  split_ifs at hc <;> omega

theorem mixedSupport_weight (m : ℕ) (upper : Bool) :
    (weight (mixedSupport m upper) : Residue m) =
      if upper then 4 * (2 : Residue m)^m - 1 else 2 * (2 : Residue m)^m - 2 := by
  cases upper
  · have hn := weight_Ico_add (show 1 ≤ m+1 by omega)
    have hz := congrArg (fun n : ℕ => (n : Residue m)) hn
    push_cast at hz
    change (weight (Ico 1 (m+1)) : Residue m) = 2 * (2 : Residue m)^m - 2
    rw [pow_succ (2 : Residue m) m] at hz
    linear_combination hz
  · change (weight (range (m+2)) : Residue m) = 4 * (2 : Residue m)^m - 1
    rw [weight_range, Nat.cast_sub (by
      have hp : 0 < (2 : ℕ)^(m+2) := by positivity
      omega : 1 ≤ 2^(m+2))]
    push_cast
    rw [pow_add (2 : Residue m) m 2]
    ring

/-- A support-cardinality obstruction replaces the longer six-point
overlap/diameter argument once `m≥4`. -/
theorem no_mixed_difference_large {m j : ℕ} (hm : 4 ≤ m)
    (a b : Fin 4) (hab : a ≠ b) (upper : Bool) :
    (2 : Residue m)^j * (baseWeight m a - baseWeight m b) ≠
      (if upper then 4 * (2 : Residue m)^m - 1 else 2 * (2 : Residue m)^m - 2) := by
  intro he
  rw [base_difference (by omega) a b hab, ← mixedSupport_weight] at he
  have hs := (rotate_weight_eq_iff (by omega : 0 < 2*m+1) j
    (signedSupport_subset (by omega) (decide (a < b)) (differenceType a b))
    (mixedSupport_subset (by omega) upper)
    (signedSupport_ne_range (by omega) (decide (a < b)) (differenceType a b))
    (mixedSupport_ne_range (by omega) upper)).mp he
  have hc := congrArg Finset.card hs
  rw [rotate_card j (signedSupport_subset (by omega) _ _),
    signedSupport_card (by omega), mixedSupport_card] at hc
  split_ifs at hc <;> omega

/-- For every `m≥3`, no rotation of a nonzero natural difference can join
the lower endpoint of an outer selected edge to a middle selected edge. -/
theorem no_mixed_difference {m j : ℕ} (hm : 3 ≤ m) (hj : j < 2*m+1)
    (a b : Fin 4) (hab : a ≠ b) :
    (2 : Residue m)^j * (baseWeight m a - baseWeight m b) ≠ 2 * (2 : Residue m)^m - 2 ∧
    (2 : Residue m)^j * (baseWeight m a - baseWeight m b) ≠ 4 * (2 : Residue m)^m - 1 := by
  by_cases hm4 : 4 ≤ m
  · exact ⟨no_mixed_difference_large hm4 a b hab false,
      no_mixed_difference_large hm4 a b hab true⟩
  · have hm3 : m = 3 := by omega
    subst m
    have hbase (i : Fin 4) : baseWeight 3 i = SuzukiPairWeightFinite.eightWeight i := by
      fin_cases i <;> norm_num [baseWeight, baseValue, SuzukiPairWeightFinite.eightWeight]
    have hh := SuzukiPairWeightFinite.seven_exponent_no_mixed_difference ⟨j, hj⟩ a b
    norm_num [hbase]
    exact hh

end Kourovka2135.SuzukiNaturalWeightDifferences
