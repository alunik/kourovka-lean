import Kourovka2135.OddNormalizerModelObstruction
import Kourovka2135.BinarySplitGoodSetGeneration
import Kourovka2135.BinarySplitGoodSetObstruction
import Kourovka2135.BinarySLTwoMinimalException
import Kourovka2135.MinimalSimpleReduction

/-! Every even-characteristic PSL2 radical quotient is excluded for an
odd-prime least exception with noncentral radical. The split-prime good set
and actual root 2-subgroup give a concrete nontrivial second commutator.
The field size four is included by the same argument. No classification,
module, multiplier, cover, or persistent-lift premise remains.
-/

set_option autoImplicit false
noncomputable section
universe u v
namespace Kourovka2135.EvenPSLTwoOddNormalizerBranch

variable {F : Type v} [Field F] [CharP F 2]

/-- The split torus acts without nonidentity fixed points on its root group. -/
theorem tor_eq_one_of_commute_uni (u : Fˣ) (b : F) (hb : b ≠ 0)
    (h : Commute (SLTwo.tor u) (SLTwo.uni b)) : u = 1 := by
  have heq : SLTwo.uni ((u : F) ^ 2 * b) = SLTwo.uni b := by
    rw [← SLTwo.tor_conj_uni, h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hparam : (Multiplicative.ofAdd ((u : F) ^ 2 * b) : Multiplicative F) =
      Multiplicative.ofAdd b := SLTwo.uniHom_injective (K := F) heq
  have hmul : (u : F) ^ 2 * b = b := congrArg Multiplicative.toAdd hparam
  have hsq : (u : F) ^ 2 = 1 :=
    mul_right_cancel₀ hb (by simpa only [one_mul] using hmul)
  have hu : (u : F) = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hsq
  exact Units.ext hu

/-- The exact normalizer witness needed by the odd-prime lifting theorem. -/
theorem tor_conjugate_commutator_ne_one (u : Fˣ) (hu : u ≠ 1) :
    paperCommutator (SLTwo.tor u)
      ((SLTwo.uni (1 : F))⁻¹ * SLTwo.tor u * SLTwo.uni (1 : F)) ≠ 1 := by
  let d := SLTwo.tor u
  let x := SLTwo.uni (1 : F)
  have hdnorm : d ∈ Subgroup.normalizer (SLTwo.Unip F : Set (SLTwo.SL2 F)) :=
    SLTwo.torus_le_normalizer ⟨u, rfl⟩
  have hx : x ∈ SLTwo.Unip F := (SLTwo.mem_Unip_iff _).mpr ⟨1, rfl⟩
  have hcU : paperCommutator d x ∈ SLTwo.Unip F := by
    apply (SLTwo.Unip F).mul_mem ?_ hx
    exact (Subgroup.mem_normalizer_iff''.mp hdnorm x⁻¹).mp ((SLTwo.Unip F).inv_mem hx)
  obtain ⟨b, hb⟩ := (SLTwo.mem_Unip_iff _).mp hcU
  have hb0 : b ≠ 0 := by
    intro hzero
    have hz : paperCommutator d x = 1 := by
      rw [hb, hzero]
      exact (SLTwo.uniHom F).map_one
    exact hu (BinarySplitGoodSetObstruction.tor_parameter_eq_one_of_commute u
      ((paperCommutator_eq_one_iff _ _).mp hz))
  have heq : paperCommutator d (x⁻¹ * d * x) =
      paperCommutator d (paperCommutator d x) := by
    unfold paperCommutator
    group
  intro hz
  change paperCommutator d (x⁻¹ * d * x) = 1 at hz
  rw [heq, hb] at hz
  exact hu (tor_eq_one_of_commute_uni u b hb0 ((paperCommutator_eq_one_iff _ _).mp hz))

/-- An odd split prime exists already at exponent two, including the field
of four elements. -/
theorem exists_split_prime (f : ℕ) (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ 2 ^ f - 1 := by
  have hpow : 4 ≤ 2 ^ f := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hf)
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f - 1 ≠ 1 by omega)
  have htwo : 2 ∣ 2 ^ f :=
    even_iff_two_dvd.mp ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega))
  have hrne : r ≠ 2 := by
    intro heq
    subst r
    have hdiv : 2 ∣ 2 ^ f - (2 ^ f - 1) := Nat.dvd_sub htwo hd
    have hone : 2 ^ f - (2 ^ f - 1) = 1 := by omega
    rw [hone] at hdiv
    exact Nat.prime_two.not_dvd_one hdiv
  exact ⟨r, hr, hr.odd_of_ne_two hrne, hd⟩

end Kourovka2135.EvenPSLTwoOddNormalizerBranch

namespace Kourovka2135

/-- The actual SL2 model, with every field size 2^f for f at least two. -/
theorem OrderMinimalException.false_of_odd_noncentral_even_slTwo_quotient
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type v) [Field F] [Finite F] [CharP F 2]
    (f : ℕ) (hcard : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃* SLTwo.SL2 F) : False := by
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable hp hnoncentral)
  obtain ⟨r, hr, hrOdd, hrdiv⟩ := EvenPSLTwoOddNormalizerBranch.exists_split_prime f hf
  let : Fact r.Prime := ⟨hr⟩
  have hsplit : r ∣ Nat.card F - 1 := by rwa [hcard]
  have hgood := BinarySplitGoodSetGeneration.isGeneratingGoodSet F hsolv hrOdd hsplit
  have hdiv : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r hdiv
  have hane : a ≠ 1 := by
    intro he
    exact hr.ne_one (by simpa only [he, orderOf_one] using ha.symm)
  exact h.false_of_odd_model_normalizer_good_set hp Nat.prime_two hodd hodd.symm
    hnoncentral e hgood (SLTwo.Unip F) BinarySplitGoodSetObstruction.unip_isPGroup
    (SLTwo.tor a) (SLTwo.uni (1 : F)) ⟨a, ha, IsConj.refl _⟩
    (SLTwo.torus_le_normalizer ⟨a, rfl⟩)
    ((SLTwo.mem_Unip_iff _).mpr ⟨1, rfl⟩)
    (EvenPSLTwoOddNormalizerBranch.tor_conjugate_commutator_ne_one a hane)

/-- The corresponding genuine projective-group entry; the characteristic-two
SL2-to-PSL2 isomorphism is proved, not assumed. -/
theorem OrderMinimalException.false_of_odd_noncentral_even_pslTwo_quotient
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (F : Type v) [Field F] [Finite F] [CharP F 2]
    (f : ℕ) (hcard : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    (e : (G ⧸ solubleRadical G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : False :=
  h.false_of_odd_noncentral_even_slTwo_quotient hp hodd hnoncentral F f hcard hf
    (e.trans (BinarySLTwoProjectiveEquiv.equiv F).symm)

end Kourovka2135
