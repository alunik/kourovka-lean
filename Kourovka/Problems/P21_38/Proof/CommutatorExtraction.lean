import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.CompactCore

/-!
# Extracting commutators from local interpolation

Agreement on a set supporting a permutation gives agreement of conjugates.
Applying this twice extracts a commutator from two interpolating elements.
For the compact core, interpolation on every interior grid interval therefore
implies containment of its commutator subgroup.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson GroupApproximation.HydeLodha
open scoped commutatorElement

/-- Two successive local interpolations preserve a commutator exactly.

The first interpolation agrees with `f` on a set supporting `g`; the second
agrees with `g` on a set supporting the first interpolation. The two supporting
sets need not be nested. -/
theorem commutator_eq_of_local_interpolations
    {X : Type*} {f g h k : Equiv.Perm X} {U V : Set X}
    (hg : SupportedIn g U) (hh : SupportedIn h V)
    (hhf : Set.EqOn h f U) (hkg : Set.EqOn k g V) :
    ⁅h, k⁆ = ⁅f, g⁆ := by
  have hfirst := conj_eq_of_eqOn hg hhf
  have hsecond := conj_eq_of_eqOn hh.inv hkg
  calc
    ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    _ = h * (g * h⁻¹ * g⁻¹) := by rw [hsecond]
    _ = (h * g * h⁻¹) * g⁻¹ := by group
    _ = (f * g * f⁻¹) * g⁻¹ := by rw [hfirst]
    _ = ⁅f, g⁆ := rfl

/-- Local interpolation of compact-core elements on interior grid intervals
by elements that belong both to `H` and to the compact core. -/
def CoreLocalInterpolation (m : ℕ) (H : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ f ∈ compactCore m, ∀ a b : ℚ,
    (∃ N, a ∈ Grid (m + 2) N) → (∃ N, b ∈ Grid (m + 2) N) →
    0 < a → a < b → b < 1 →
    ∃ h ∈ H, h ∈ compactCore m ∧ Set.EqOn h f (Set.Icc a b)

/-- Local interpolation supplies actual subgroup elements whose commutator
equals any prescribed commutator of compact-core elements. -/
theorem exists_commutator_eq_of_coreLocalInterpolation
    {m : ℕ} {H : Subgroup (Equiv.Perm ℚ)} (hlocal : CoreLocalInterpolation m H)
    {f g : Equiv.Perm ℚ} (hf : f ∈ compactCore m) (hg : g ∈ compactCore m) :
    ∃ h ∈ H, ∃ k ∈ H, ⁅h, k⁆ = ⁅f, g⁆ := by
  obtain ⟨a, b, ha, hb, ha0, hab, hb1, hgsupp, _⟩ :=
    compactCore_supportedIn₂ hg hg
  obtain ⟨h, hhH, hhcore, hhf⟩ := hlocal f hf a b ha hb ha0 hab hb1
  obtain ⟨c, d, hc, hd, hc0, hcd, hd1, hhsupp, _⟩ :=
    compactCore_supportedIn₂ hhcore hhcore
  obtain ⟨k, hkH, _, hkg⟩ := hlocal g hg c d hc hd hc0 hcd hd1
  refine ⟨h, hhH, k, hkH, commutator_eq_of_local_interpolations hgsupp hhsupp ?_ ?_⟩
  · exact hhf.mono Set.Ioo_subset_Icc_self
  · exact hkg.mono Set.Ioo_subset_Icc_self

/-- A subgroup with local interpolation contains the commutator subgroup of
the compact core. This conclusion requires no normality assumption on `H`. -/
theorem commutator_compactCore_le_of_local_interpolation
    {m : ℕ} {H : Subgroup (Equiv.Perm ℚ)} (hlocal : CoreLocalInterpolation m H) :
    ⁅compactCore m, compactCore m⁆ ≤ H := by
  apply Subgroup.commutator_le.mpr
  intro f hf g hg
  obtain ⟨h, hh, k, hk, heq⟩ :=
    exists_commutator_eq_of_coreLocalInterpolation hlocal hf hg
  rw [← heq, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh hk) (H.inv_mem hh)) (H.inv_mem hk)

#audit_axioms commutator_compactCore_le_of_local_interpolation

end Kourovka.P21_38
