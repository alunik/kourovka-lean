import Kourovka2135.WordCalculus
import Kourovka2135.OrderObstruction
import Mathlib.Tactic.Group

/-!
# Derived-value centralization

This proves the assertions of Contreras Rojas–Grazian–Monetta,
arXiv:2105.14474v1, Lemmas 5.1 and 5.2. For the final coprime-action step
we use an elementary commuting-power calculation instead of importing a
general coprime-action theorem. Solubility is not assumed.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135

variable {G : Type u} [Group G]

/-- The commutator convention in the problem and its ordinary proof. -/
def paperCommutator (a b : G) : G := a⁻¹ * b⁻¹ * a * b

theorem tripleCommutator_mem_derivedValues {k : ℕ} {x : G}
    (hx : x ∈ (OuterWord.derivedWord k).values G) (g : G) :
    paperCommutator (paperCommutator g x) x ∈ (OuterWord.derivedWord k).values G := by
  have ha := (OuterWord.derivedWord k).conj_mem_values
    ((OuterWord.derivedWord k).inv_mem_values hx) g
  have hb : paperCommutator (g⁻¹ * x⁻¹ * g) x ∈
      (OuterWord.derivedWord (k + 1)).values G := by
    exact (OuterWord.mem_values_bracket _ _ _).mpr ⟨_, ha, x, hx, rfl⟩
  have hc := (OuterWord.derivedWord (k + 1)).conj_mem_values hb x
  have heq : paperCommutator (paperCommutator g x) x =
      x⁻¹ * paperCommutator (g⁻¹ * x⁻¹ * g) x * x := by
    simp only [paperCommutator]
    group
  rw [heq]
  exact (OuterWord.derivedWord k).derivedWord_values_subset (k + 1)
    (by simp) hc

/-- CGM Lemma 5.1, retaining single values throughout. -/
theorem ProductOrderCondition.not_dvd_orderOf_tripleCommutator
    {k p : ℕ} (h : ProductOrderCondition (OuterWord.derivedWord k) p G)
    {x : G} (hx : x ∈ (OuterWord.derivedWord k).values G)
    (hxp : ¬ p ∣ orderOf x) (g : G) :
    ¬ p ∣ orderOf (paperCommutator (paperCommutator g x) x) := by
  intro hdiv
  have hxinv := (OuterWord.derivedWord k).inv_mem_values hx
  have hprime : ¬ p ∣ orderOf x⁻¹ := by simpa only [orderOf_inv] using hxp
  have ht := h x⁻¹ hxinv (paperCommutator (paperCommutator g x) x)
    (tripleCommutator_mem_derivedValues hx g) hprime hdiv
  let d := paperCommutator g x
  have heq : x⁻¹ * paperCommutator d x =
      (MulAut.conj (d * x)⁻¹) x⁻¹ := by
    simp [paperCommutator, mul_assoc]
  change p ∣ orderOf (x⁻¹ * paperCommutator d x) at ht
  rw [heq, MulEquiv.orderOf_eq, orderOf_inv] at ht
  exact hxp ht

/-- An elementary coprime-action step for a single commutator. -/
theorem commute_of_tripleCommutator_eq_one
    {p : ℕ} (hp : p.Prime) (P : Subgroup G) (hP : IsPGroup p P)
    {g x : G} (hcP : paperCommutator g x ∈ P) (hxp : ¬ p ∣ orderOf x)
    (ht : paperCommutator (paperCommutator g x) x = 1) : Commute g x := by
  let : Fact p.Prime := ⟨hp⟩
  let c := paperCommutator g x
  have hcx : Commute c x := by
    change c * x = x * c
    change c⁻¹ * x⁻¹ * c * x = 1 at ht
    have hh := congrArg (fun z : G => x * c * z) ht
    simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using hh
  have hconj : c * x⁻¹ = (MulAut.conj g⁻¹) x⁻¹ := by
    simp [c, paperCommutator, mul_assoc]
  have hpow : (c * x⁻¹) ^ orderOf x = 1 := by
    rw [hconj, ← map_pow]
    simp only [inv_pow, pow_orderOf_eq_one, inv_one, map_one]
  rw [hcx.inv_right.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one] at hpow
  have hc : c = 1 := by
    by_contra hne
    have hneP : (⟨c, hcP⟩ : P) ≠ 1 := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    have hd : p ∣ orderOf c := by
      simpa only [Subgroup.orderOf_mk] using hP.dvd_orderOf hneP
    exact hxp (hd.trans (orderOf_dvd_iff_pow_eq_one.mpr hpow))
  change g * x = x * g
  change g⁻¹ * x⁻¹ * g * x = 1 at hc
  have hh := congrArg (fun z : G => x * g * z) hc
  simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using hh

/-- CGM Lemma 5.2: a p′-order derived-word value normalizing a p-subgroup
centralizes it. All finite-group cases follow; no solubility is assumed. -/
theorem ProductOrderCondition.derivedValue_centralizes_pSubgroup
    {k p : ℕ} (hp : p.Prime)
    (h : ProductOrderCondition (OuterWord.derivedWord k) p G)
    (P : Subgroup G) (hP : IsPGroup p P) {x : G}
    (hx : x ∈ (OuterWord.derivedWord k).values G)
    (hxp : ¬ p ∣ orderOf x) (hxn : x ∈ Subgroup.normalizer P) :
    ∀ g ∈ P, Commute g x := by
  let : Fact p.Prime := ⟨hp⟩
  intro g hg
  have mem_comm (a : G) (ha : a ∈ P) : paperCommutator a x ∈ P := by
    have hh := ((Subgroup.mem_normalizer_iff''.mp hxn) a).mp ha
    simpa only [paperCommutator, mul_assoc] using P.mul_mem (P.inv_mem ha) hh
  have hcP := mem_comm g hg
  have htP := mem_comm (paperCommutator g x) hcP
  have ht : paperCommutator (paperCommutator g x) x = 1 := by
    by_contra hne
    have hneP : (⟨paperCommutator (paperCommutator g x) x, htP⟩ : P) ≠ 1 := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    have hdiv : p ∣ orderOf (paperCommutator (paperCommutator g x) x) := by
      simpa only [Subgroup.orderOf_mk] using hP.dvd_orderOf hneP
    exact h.not_dvd_orderOf_tripleCommutator hx hxp g hdiv
  exact commute_of_tripleCommutator_eq_one hp P hP hcP hxp ht

end Kourovka2135
