import Kourovka.Problems.P21_03.Proof.CanonicalPartialMatching

/-!
# Weighted local-lemma bounds for canonical partial matchings

This module packages the exact canonical-event denominator together with the
finite lopsided local lemma.  It also records the rational weight used by the
conditioned-simple-completion argument: for `n >= 123`, the uniform two-edge
weight `9 / (4 n (n-1))` has core penalty at least `4/9` and one-endpoint
penalty at least `2/3` after the stated incidence bounds are inserted.
-/

namespace Kourovka213

open scoped BigOperators

namespace CanonicalPartialMatching

variable {alpha I : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The falling-factorial denominator of a canonical event, as a real. -/
def denominator (c : CanonicalPartialMatching alpha) : Real :=
  ((Fintype.card alpha).descFactorial c.size : Nat)

theorem denominator_pos (c : CanonicalPartialMatching alpha) :
    0 < c.denominator := by
  have hsize : c.size <= Fintype.card alpha := by
    simpa using Fintype.card_le_of_injective c.source c.source.injective
  rw [denominator]
  exact_mod_cast Nat.descFactorial_pos.mpr hsize

/-- The standard weighted choice `x_i = t^{s_i} / (n)_{s_i}`. -/
noncomputable def weight (t : Real) (c : CanonicalPartialMatching alpha) : Real :=
  t ^ c.size / c.denominator

theorem weight_nonneg {t : Real} (ht : 0 <= t)
    (c : CanonicalPartialMatching alpha) : 0 <= c.weight t := by
  exact div_nonneg (pow_nonneg ht _) (le_of_lt c.denominator_pos)

/-- A canonical weighted local lemma.  The product condition is written in
its most convenient penalty form: multiplying the neighbor product by
`t^{s_i}` must recover at least one. -/
theorem weighted_lll_of_penalty
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (t : Real)
    (ht : 0 <= t)
    (hx1 : forall i, (C i).weight t < 1)
    (hpenalty : forall i,
      1 <= t ^ (C i).size *
        ∏ j ∈ neighborhood C i, (1 - (C j).weight t)) :
    (∏ i : I, (1 - (C i).weight t)) *
        Fintype.card (Equiv.Perm alpha) <=
      ((avoidEvents (fun i => (C i).event) Finset.univ).card : Real) := by
  apply finite_asymmetric_lopsided_lll (finiteLopsidedBound_event C)
    (fun i => weight_nonneg ht (C i)) hx1
  intro i
  have hd := (C i).denominator_pos
  change 1 / (C i).denominator <=
    (t ^ (C i).size / (C i).denominator) *
      ∏ j ∈ neighborhood C i, (1 - (C j).weight t)
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hd).mpr (hpenalty i)

/-- The generic relative bound for one additional event after conditioning
on avoidance of a weighted canonical core family. -/
theorem weighted_conditioned_external
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (x : I -> Real)
    (hx0 : forall i, 0 <= x i) (hx1 : forall i, x i < 1)
    (hp : forall i,
      1 / (C i).denominator <=
        x i * ∏ j ∈ neighborhood C i, (1 - x j))
    (A : Finset (Equiv.Perm alpha)) (R S : Finset I) (q : Real)
    (hq : 0 <= q)
    (hExternal : forall T : Finset I,
      (∀ j ∈ T, j ∉ R) ->
        ((A ∩ avoidEvents (fun j => (C j).event) T).card : Real) <=
          q * ((avoidEvents (fun j => (C j).event) T).card : Real)) :
    (∏ j ∈ S.filter fun j => j ∈ R, (1 - x j)) *
        ((A ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
      q * ((avoidEvents (fun j => (C j).event) S).card : Real) := by
  exact finiteLopsided_conditioned_external_bound
    (finiteLopsidedBound_event C) hx0 hx1 hp A R S q hq hExternal

end CanonicalPartialMatching

/-- The uniform core weight corresponding to the optimal rational choice
`t = 3/2` in the Bernoulli proof. -/
noncomputable def conditionedCoreWeight (n : Nat) : Real :=
  9 / (4 * (n : Real) * ((n : Real) - 1))

/-- Exact arithmetic behind the cutoff `n >= 123`.  A core event has at most
`30n` broad neighbors, while each source or target endpoint contributes at
most `9n` events. -/
theorem conditionedCoreWeight_bounds {n : Nat} (hn : 123 <= n) :
    0 <= conditionedCoreWeight n ∧ conditionedCoreWeight n < 1 ∧
      (4 / 9 : Real) <= 1 - 30 * n * conditionedCoreWeight n ∧
      (2 / 3 : Real) <= 1 - 18 * n * conditionedCoreWeight n := by
  have hnR : (123 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnpos : (0 : Real) < n := by linarith
  have hnm1 : (0 : Real) < (n : Real) - 1 := by linarith
  have hden : (0 : Real) < 4 * n * ((n : Real) - 1) := by positivity
  have hx0 : 0 <= conditionedCoreWeight n := by
    exact div_nonneg (by norm_num) hden.le
  have hx1 : conditionedCoreWeight n < 1 := by
    rw [conditionedCoreWeight, div_lt_one hden]
    nlinarith [mul_pos hnpos hnm1]
  have hcoreIdentity :
      30 * (n : Real) * conditionedCoreWeight n =
        135 / (2 * ((n : Real) - 1)) := by
    rw [conditionedCoreWeight]
    field_simp
    ring
  have hendpointIdentity :
      18 * (n : Real) * conditionedCoreWeight n =
        81 / (2 * ((n : Real) - 1)) := by
    rw [conditionedCoreWeight]
    field_simp
    ring
  have hcoreFraction :
      135 / (2 * ((n : Real) - 1)) <= (5 / 9 : Real) := by
    apply (div_le_iff₀ (by positivity : (0 : Real) < 2 * ((n : Real) - 1))).mpr
    nlinarith
  have hendpointFraction :
      81 / (2 * ((n : Real) - 1)) <= (1 / 3 : Real) := by
    apply (div_le_iff₀ (by positivity : (0 : Real) < 2 * ((n : Real) - 1))).mpr
    nlinarith
  refine ⟨hx0, hx1, ?_, ?_⟩
  · rw [hcoreIdentity]
    nlinarith
  · rw [hendpointIdentity]
    nlinarith

/-- A constant product over at most `d` factors is bounded below by the
`d`th power when the common factor lies in `[0,1]`. -/
theorem pow_le_prod_one_sub_of_card_le
    {J : Type*} [DecidableEq J] (S : Finset J) {x : Real} {d : Nat}
    (hx0 : 0 <= x) (hx1 : x < 1) (hcard : S.card <= d) :
    (1 - x) ^ d <= ∏ _j ∈ S, (1 - x) := by
  rw [Finset.prod_const]
  exact pow_le_pow_of_le_one
    (sub_nonneg.mpr (le_of_lt hx1)) (sub_le_self 1 hx0) hcard

/-- Bernoulli's inequality in the exact normalization used for local-lemma
penalties. -/
theorem one_sub_mul_le_pow_one_sub {x : Real} (hx1 : x < 1) (d : Nat) :
    1 - (d : Real) * x <= (1 - x) ^ d := by
  have hbase : (-1 : Real) <= 1 - x := by linarith
  calc
    1 - (d : Real) * x = 1 + (d : Real) * ((1 - x) - 1) := by ring
    _ <= (1 - x) ^ d := one_add_mul_sub_le_pow hbase d

/-- For `n >= 123`, any collection of at most `30n` core neighbors retains
at least the factor `4/9`. -/
theorem conditionedCoreWeight_core_product
    {J : Type*} [DecidableEq J] {n : Nat} (hn : 123 <= n)
    (S : Finset J) (hcard : S.card <= 30 * n) :
    (4 / 9 : Real) <= ∏ _j ∈ S, (1 - conditionedCoreWeight n) := by
  have hb := conditionedCoreWeight_bounds hn
  have hpow := pow_le_prod_one_sub_of_card_le S hb.1 hb.2.1 hcard
  have hBernoulli := one_sub_mul_le_pow_one_sub hb.2.1 (30 * n)
  calc
    (4 / 9 : Real) <= 1 - 30 * (n : Real) * conditionedCoreWeight n := hb.2.2.1
    _ = 1 - ((30 * n : Nat) : Real) * conditionedCoreWeight n := by
      norm_num
    _ <= (1 - conditionedCoreWeight n) ^ (30 * n) := hBernoulli
    _ <= ∏ _j ∈ S, (1 - conditionedCoreWeight n) := hpow

/-- For `n >= 123`, a prescription with `s` source and `s` target endpoints
retains at least `(2/3)^s` when it conflicts with at most `18ns` core events. -/
theorem conditionedCoreWeight_external_product
    {J : Type*} [DecidableEq J] {n s : Nat} (hn : 123 <= n)
    (S : Finset J) (hcard : S.card <= 18 * n * s) :
    (2 / 3 : Real) ^ s <=
      ∏ _j ∈ S, (1 - conditionedCoreWeight n) := by
  have hb := conditionedCoreWeight_bounds hn
  have hpow := pow_le_prod_one_sub_of_card_le S hb.1 hb.2.1 hcard
  have hBernoulli := one_sub_mul_le_pow_one_sub hb.2.1 (18 * n)
  have hone :
      (2 / 3 : Real) <= (1 - conditionedCoreWeight n) ^ (18 * n) := by
    calc
      (2 / 3 : Real) <= 1 - 18 * (n : Real) * conditionedCoreWeight n := hb.2.2.2
      _ = 1 - ((18 * n : Nat) : Real) * conditionedCoreWeight n := by
        norm_num
      _ <= (1 - conditionedCoreWeight n) ^ (18 * n) := hBernoulli
  calc
    (2 / 3 : Real) ^ s <=
        ((1 - conditionedCoreWeight n) ^ (18 * n)) ^ s :=
      pow_le_pow_left₀ (by norm_num) hone s
    _ = (1 - conditionedCoreWeight n) ^ (18 * n * s) := by
      simpa [Nat.mul_assoc] using
        (pow_mul (1 - conditionedCoreWeight n) (18 * n) s).symm
    _ <= ∏ _j ∈ S, (1 - conditionedCoreWeight n) := hpow

/-- The integer ceiling of the uniform quadratic core-event count
`9 n^2 / 2`.  Writing the ceiling in this form keeps all subsequent
estimates in `Nat` until the final analytic inequality. -/
def conditionedCoreEventCap (n : Nat) : Nat :=
  (9 * n ^ 2 + 1) / 2

theorem two_mul_conditionedCoreEventCap_le (n : Nat) :
    2 * conditionedCoreEventCap n <= 9 * n ^ 2 + 1 := by
  simpa only [conditionedCoreEventCap] using
    Nat.mul_div_le (9 * n ^ 2 + 1) 2

/-- The elementary logarithmic estimate used to control the reciprocal of
a local-lemma product.  It is the inequality
`(1-x)^{-K} <= exp(Kx/(1-x))` for `0 <= x < 1`. -/
theorem inv_pow_one_sub_le_exp {x : Real} (_hx0 : 0 <= x) (hx1 : x < 1)
    (K : Nat) :
    ((1 - x) ^ K)⁻¹ <= Real.exp ((K : Real) * x / (1 - x)) := by
  have hbase : 0 < 1 - x := sub_pos.mpr hx1
  have hinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hbase
  have hlog : Real.log ((1 - x)⁻¹) <= x / (1 - x) := by
    calc
      Real.log ((1 - x)⁻¹) <= (1 - x)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos hinv
      _ = x / (1 - x) := by
        field_simp [ne_of_gt hbase]
        ring
  have hinv_le : (1 - x)⁻¹ <= Real.exp (x / (1 - x)) :=
    (Real.log_le_iff_le_exp hinv).mp hlog
  calc
    ((1 - x) ^ K)⁻¹ = ((1 - x)⁻¹) ^ K := by rw [inv_pow]
    _ <= (Real.exp (x / (1 - x))) ^ K :=
      pow_le_pow_left₀ hinv.le hinv_le K
    _ = Real.exp ((K : Real) * x / (1 - x)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- With at most `ceil(9 n^2 / 2)` core events, the exponent controlling the
reciprocal local-lemma product is at most `10.21` once `n >= 123`. -/
theorem conditionedCoreWeight_totalExponent_le
    {n K : Nat} (hn : 123 <= n) (hK : K <= conditionedCoreEventCap n) :
    (K : Real) * conditionedCoreWeight n /
        (1 - conditionedCoreWeight n) <= 1021 / 100 := by
  have hnR : (123 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnpos : (0 : Real) < n := by linarith
  have hnm1 : (0 : Real) < (n : Real) - 1 := by linarith
  have hden0 : (0 : Real) < 4 * n * ((n : Real) - 1) := by positivity
  have hgap : (0 : Real) < 4 * n * ((n : Real) - 1) - 9 := by
    nlinarith
  have htwoK : 2 * K <= 9 * n ^ 2 + 1 :=
    (Nat.mul_le_mul_left 2 hK).trans (two_mul_conditionedCoreEventCap_le n)
  have htwoKR : (2 : Real) * K <= 9 * (n : Real) ^ 2 + 1 := by
    exact_mod_cast htwoK
  have hpolyNonneg :
      0 <= ((n : Real) - 123) * (68 * (n : Real) + 196) :=
    mul_nonneg (sub_nonneg.mpr hnR) (by positivity)
  have hfrac :
      (K : Real) * 9 /
          (4 * (n : Real) * ((n : Real) - 1) - 9) <= 1021 / 100 := by
    apply (div_le_iff₀ hgap).mpr
    nlinarith [htwoKR, hpolyNonneg]
  calc
    (K : Real) * conditionedCoreWeight n /
          (1 - conditionedCoreWeight n) =
        (K : Real) * 9 /
          (4 * (n : Real) * ((n : Real) - 1) - 9) := by
      rw [conditionedCoreWeight]
      field_simp [ne_of_gt hden0, ne_of_gt hgap]
    _ <= 1021 / 100 := hfrac

/-- Sharpened inverse-core conditioning cap.  This is substantially smaller
than the earlier uniform `3^11` cap and is the factor used in the effective
support tail. -/
theorem conditionedCoreWeight_inverse_product_lt_two_pow_fifteen
    {n K : Nat} (hn : 123 <= n) (hK : K <= conditionedCoreEventCap n) :
    ((1 - conditionedCoreWeight n) ^ K)⁻¹ < (2 : Real) ^ 15 := by
  have hb := conditionedCoreWeight_bounds hn
  have hfirst := inv_pow_one_sub_le_exp hb.1 hb.2.1 K
  have hexponent := conditionedCoreWeight_totalExponent_le hn hK
  have hlog : (1021 / 100 : Real) < Real.log ((2 : Real) ^ 15) := by
    rw [Real.log_pow]
    nlinarith [Real.log_two_gt_d9]
  have hexp : Real.exp (1021 / 100 : Real) < (2 : Real) ^ 15 :=
    (Real.lt_log_iff_exp_lt (by positivity)).mp hlog
  exact hfirst.trans_lt ((Real.exp_le_exp.mpr hexponent).trans_lt hexp)

/-- Finset-product form of the sharpened inverse-core cap. -/
theorem conditionedCoreWeight_inverse_finsetProduct_lt_two_pow_fifteen
    {J : Type*} [DecidableEq J] {n : Nat} (hn : 123 <= n)
    (S : Finset J) (hcard : S.card <= conditionedCoreEventCap n) :
    (∏ _j ∈ S, (1 - conditionedCoreWeight n))⁻¹ < (2 : Real) ^ 15 := by
  rw [Finset.prod_const]
  exact conditionedCoreWeight_inverse_product_lt_two_pow_fifteen hn hcard

/-- The two-point canonical density is exactly the chosen core weight times
the retained core factor `4/9`. -/
theorem one_div_descFactorial_two_eq_conditionedCoreWeight_mul
    {n : Nat} (hn : 123 <= n) :
    1 / ((n.descFactorial 2 : Nat) : Real) =
      conditionedCoreWeight n * (4 / 9 : Real) := by
  have hnR : (123 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnpos : (0 : Real) < n := by linarith
  have hnm1 : (0 : Real) < (n : Real) - 1 := by linarith
  rw [Nat.cast_descFactorial_two, conditionedCoreWeight]
  field_simp [ne_of_gt hnpos, ne_of_gt hnm1]

namespace CanonicalPartialMatching

variable {alpha I : Type*} [Fintype alpha] [DecidableEq alpha]

/-- A canonical prescription conditioned on a two-point core family.  The
hypotheses expose only the two combinatorial degree bounds: `30n` for a core
neighborhood and `18ns` for the core events meeting an external event of
size `s`.  No positivity assumption on the conditioned sample-space
cardinality is needed. -/
theorem conditioned_external_event_relative_bound
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (hn : 123 <= Fintype.card alpha)
    (hsize : forall i, (C i).size = 2)
    (hdegree : forall i,
      (neighborhood C i).card <= 30 * Fintype.card alpha)
    (c : CanonicalPartialMatching alpha)
    (hconflict : (conflictSet C c).card <=
      18 * Fintype.card alpha * c.size) :
    (2 / 3 : Real) ^ c.size *
        ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
      (1 / c.denominator) *
        ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) := by
  classical
  let n := Fintype.card alpha
  let x := conditionedCoreWeight n
  let R := conflictSet C c
  have hb := conditionedCoreWeight_bounds hn
  have hx0 : forall _i : I, 0 <= x := fun _ => hb.1
  have hx1 : forall _i : I, x < 1 := fun _ => hb.2.1
  have hp : forall i,
      1 / (C i).denominator <=
        x * ∏ j ∈ neighborhood C i, (1 - x) := by
    intro i
    have hprod := conditionedCoreWeight_core_product hn
      (neighborhood C i) (hdegree i)
    calc
      1 / (C i).denominator =
          1 / (((Fintype.card alpha).descFactorial 2 : Nat) : Real) := by
        simp only [denominator, hsize i]
      _ = x * (4 / 9 : Real) := by
        exact one_div_descFactorial_two_eq_conditionedCoreWeight_mul hn
      _ <= x * ∏ j ∈ neighborhood C i, (1 - x) :=
        mul_le_mul_of_nonneg_left hprod hb.1
  have hq : 0 <= 1 / c.denominator :=
    one_div_nonneg.mpr (le_of_lt c.denominator_pos)
  have hExternal : forall T : Finset I,
      (∀ j ∈ T, j ∉ R) ->
        ((c.event ∩ avoidEvents (fun j => (C j).event) T).card : Real) <=
          (1 / c.denominator) *
            ((avoidEvents (fun j => (C j).event) T).card : Real) := by
    intro T hT
    apply external_event_density_le C c T
    intro j hjT hconf
    exact hT j hjT (mem_conflictSet.mpr hconf)
  have hconditioned := weighted_conditioned_external C (fun _ => x)
    hx0 hx1 hp c.event R Finset.univ (1 / c.denominator) hq hExternal
  have hfilter :
      Finset.univ.filter (fun j : I => j ∈ R) = R := by
    ext j
    simp
  rw [hfilter] at hconditioned
  have hproduct :
      (2 / 3 : Real) ^ c.size <= ∏ _j ∈ R, (1 - x) :=
    conditionedCoreWeight_external_product hn R hconflict
  calc
    (2 / 3 : Real) ^ c.size *
          ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
        (∏ _j ∈ R, (1 - x)) *
          ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) :=
      mul_le_mul_of_nonneg_right hproduct (by positivity)
    _ <= (1 / c.denominator) *
          ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) :=
      hconditioned

/-- Denominator-cleared form of `conditioned_external_event_relative_bound`.
It remains valid if the core-simple set happens to be empty. -/
theorem conditioned_external_event_descFactorial_bound
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (hn : 123 <= Fintype.card alpha)
    (hsize : forall i, (C i).size = 2)
    (hdegree : forall i,
      (neighborhood C i).card <= 30 * Fintype.card alpha)
    (c : CanonicalPartialMatching alpha)
    (hconflict : (conflictSet C c).card <=
      18 * Fintype.card alpha * c.size) :
    c.denominator * (2 / 3 : Real) ^ c.size *
        ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
      ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) := by
  have hrelative := conditioned_external_event_relative_bound
    C hn hsize hdegree c hconflict
  have hdiv :
      (2 / 3 : Real) ^ c.size *
          ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
        ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) /
          c.denominator := by
    calc
      (2 / 3 : Real) ^ c.size *
          ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
        (1 / c.denominator) *
          ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) := hrelative
      _ = ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) /
          c.denominator := by ring
  have hmul := (le_div_iff₀ c.denominator_pos).mp hdiv
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Fully integral version of the conditioned canonical-event estimate:
`(n)_s 2^s` times the number of conditioned realizations is at most `3^s`
times the number of core-simple permutations. -/
theorem conditioned_external_event_nat_bound
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (hn : 123 <= Fintype.card alpha)
    (hsize : forall i, (C i).size = 2)
    (hdegree : forall i,
      (neighborhood C i).card <= 30 * Fintype.card alpha)
    (c : CanonicalPartialMatching alpha)
    (hconflict : (conflictSet C c).card <=
      18 * Fintype.card alpha * c.size) :
    (Fintype.card alpha).descFactorial c.size * 2 ^ c.size *
        (c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card <=
      3 ^ c.size *
        (avoidEvents (fun j => (C j).event) Finset.univ).card := by
  have hclear := conditioned_external_event_descFactorial_bound
    C hn hsize hdegree c hconflict
  have hpow :
      (3 : Real) ^ c.size * (2 / 3 : Real) ^ c.size =
        (2 : Real) ^ c.size := by
    rw [← mul_pow]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hclear
    (pow_nonneg (by norm_num : (0 : Real) <= 3) c.size)
  have hscaled' :
      (((Fintype.card alpha).descFactorial c.size : Nat) : Real) *
          (2 : Real) ^ c.size *
          ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) <=
        (3 : Real) ^ c.size *
          ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) := by
    rw [denominator] at hscaled
    calc
      (((Fintype.card alpha).descFactorial c.size : Nat) : Real) *
            (2 : Real) ^ c.size *
            ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real) =
          (3 : Real) ^ c.size *
            ((((Fintype.card alpha).descFactorial c.size : Nat) : Real) *
              (2 / 3 : Real) ^ c.size *
              ((c.event ∩ avoidEvents (fun j => (C j).event) Finset.univ).card : Real)) := by
        rw [← hpow]
        ring
      _ <= (3 : Real) ^ c.size *
            ((avoidEvents (fun j => (C j).event) Finset.univ).card : Real) := hscaled
  exact_mod_cast hscaled'

end CanonicalPartialMatching

end Kourovka213
