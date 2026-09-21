import Kourovka2135.SLTwoNonscalarWordValues
import Kourovka2135.OddPSLTwoProjectiveChart
import Kourovka2135.FocalLift

/-! In a prime field, nonscalar matrices with trace ±2 have projective
images conjugate to powers of one another. The proof uses actual order-p
Sylow conjugacy, not an identification of GL2 conjugacy with SL2 conjugacy.
The finite-field parameter is arbitrary, with prime cardinality, so this also
applies directly to GaloisField p 1 without a scalar-model identification. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoPrimeUnipotentPowers

open scoped Matrix
open SLTwoNonscalarWordValues SLTwoGeneralLinearConjugation OddPSLTwoProjectiveChart

/-- When the prime occurs just once in the group order, all elements of that
prime order are conjugate to powers of any one of them. -/
theorem exists_isConj_pow_of_prime_order
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : ¬ p ^ 2 ∣ Nat.card G) (x y : G)
    (hx : orderOf x = p) (hy : orderOf y = p) :
    ∃ n : ℕ, IsConj (x ^ n) y := by
  classical
  let H := Subgroup.zpowers x
  have hH : Nat.card H = p := by simpa only [H, Nat.card_zpowers] using hx
  have hP : IsPGroup p H := IsPGroup.of_card (n := 1) (by simpa using hH)
  have hindex : ¬ p ∣ H.index := by
    intro h
    apply hcard
    rw [← H.card_mul_index, hH, pow_two]
    exact Nat.mul_dvd_mul_left p h
  obtain ⟨z, hz⟩ := FocalLift.exists_conj_mem_sylow (hP.toSylow hindex)
    (x := y) ⟨1, by simpa using hy⟩
  have hzH : z * y * z⁻¹ ∈ Subgroup.zpowers x := hz
  obtain ⟨n, _, hn⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hzH)
  exact ⟨n, (isConj_iff.mpr ⟨z, hn.symm⟩).symm⟩

variable {F : Type*} [Field F]

private instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

theorem uni_one_nonscalar : Nonscalar (SLTwo.uni (1 : F)) := by
  rintro ⟨r, hr⟩
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  simp [SLTwo.uni, Matrix.scalar] at he

theorem orderOf_uni_one (p : ℕ) [CharP F p] : orderOf (SLTwo.uni (1 : F)) = p := by
  calc
    _ = orderOf (Multiplicative.ofAdd (1 : F)) :=
      orderOf_injective (SLTwo.uniHom F) SLTwo.uniHom_injective _
    _ = p := CharP.eq F (CharP.addOrderOf_one F) inferInstance

theorem orderOf_of_trace_two (p : ℕ) [CharP F p]
    (g : SLTwo.SL2 F) (hg : Nonscalar g) (ht : g.val.trace = 2) :
    orderOf g = p := by
  have hu : (SLTwo.uni (1 : F)).val.trace = 2 := by
    norm_num [SLTwo.uni, Matrix.trace_fin_two]
  obtain ⟨C, hC⟩ := exists_automorphism_of_trace g (SLTwo.uni (1 : F)) hg
    uni_one_nonscalar (ht.trans hu.symm)
  calc
    _ = orderOf (automorphism C g) := (MulEquiv.orderOf_eq _ _).symm
    _ = p := by rw [hC, orderOf_uni_one p]

theorem quotient_neg (g : SLTwo.SL2 F) : quotient F (-g) = quotient F g := by
  have hc : quotient F (-1 : SLTwo.SL2 F) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨-1, by simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [show -g = (-1 : SLTwo.SL2 F) * g by simp, map_mul, hc, one_mul]

theorem nonscalar_neg {g : SLTwo.SL2 F} (hg : Nonscalar g) : Nonscalar (-g) := by
  rintro ⟨r, hr⟩
  apply hg
  refine ⟨-r, ?_⟩
  change -g.val = Matrix.scalar (Fin 2) r at hr
  calc
    g.val = -Matrix.scalar (Fin 2) r := neg_eq_iff_eq_neg.mp hr
    _ = Matrix.scalar (Fin 2) (-r) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem exists_trace_two_lift (g : SLTwo.SL2 F) (hg : Nonscalar g)
    (ht : g.val.trace = 2 ∨ g.val.trace = -2) :
    ∃ u : SLTwo.SL2 F, Nonscalar u ∧ u.val.trace = 2 ∧ quotient F u = quotient F g := by
  rcases ht with ht | ht
  · exact ⟨g, hg, ht, rfl⟩
  · exact ⟨-g, nonscalar_neg hg, by simpa using congrArg Neg.neg ht, quotient_neg g⟩

/-- Prime cardinality is an actual field hypothesis, not a choice of the
concrete ZMod model. No oddness or field-size lower bound is needed. -/
theorem exists_projective_isConj_pow [Finite F] (hp : (Nat.card F).Prime)
    (g h : SLTwo.SL2 F) (hg : Nonscalar g) (hh : Nonscalar h)
    (hgt : g.val.trace = 2 ∨ g.val.trace = -2)
    (hht : h.val.trace = 2 ∨ h.val.trace = -2) :
    ∃ n : ℕ, IsConj ((quotient F g) ^ n) (quotient F h) := by
  let p := Nat.card F
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simp [p, Nat.card_eq_fintype_card])
  have hcard : ¬ p ^ 2 ∣ Nat.card (SLTwo.SL2 F) := by
    rw [SLTwo.sl2_card_formula]
    change ¬ p ^ 2 ∣ p * (p ^ 2 - 1)
    intro hd
    have hd' : p ∣ p ^ 2 - 1 :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mp (by simpa only [pow_two] using hd)
    have hpp : p ∣ p ^ 2 := by simp [pow_two]
    have hle : 1 ≤ p ^ 2 := by have := hp.two_le; nlinarith
    have h1 : p ∣ 1 := by
      have he := Nat.dvd_sub hpp hd'
      simpa [Nat.sub_sub_self hle] using he
    exact hp.not_dvd_one h1
  obtain ⟨u, hu, hut, huq⟩ := exists_trace_two_lift g hg hgt
  obtain ⟨v, hv, hvt, hvq⟩ := exists_trace_two_lift h hh hht
  obtain ⟨n, hn⟩ := exists_isConj_pow_of_prime_order hcard u v
    (orderOf_of_trace_two p u hu hut) (orderOf_of_trace_two p v hv hvt)
  refine ⟨n, ?_⟩
  have hm := (quotient F).map_isConj hn
  simpa only [map_pow, huq, hvq] using hm

end Kourovka2135.SLTwoPrimeUnipotentPowers
