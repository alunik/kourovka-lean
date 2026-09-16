import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Kourovka.External.GroupApproximation.Meta.AxiomGuard

/-!
# Cofinal motion in an interval

A bounded orbit of increasing real permutations has a common fixed point at
its supremum. For rational permutations the same construction instead gives
an invariant real cut. The rational results therefore assume that no such cut
is invariant; absence of rational common fixed points alone is insufficient.

This isolates the orbital argument in Golan-Polak, *The generation problem in
Thompson group F*, arXiv:1608.02572v2, Lemmas 7.9--7.10. In that argument the
absence of common fixed points concerns every real point of the orbital.
-/

namespace Kourovka.P21_38

open Set

/-- An increasing real permutation fixes the supremum of a nonempty bounded
set that it preserves. -/
theorem real_sSup_fixed_of_invariant
    {f : Equiv.Perm ℝ} (hf : StrictMono f) {s : Set ℝ}
    (hne : s.Nonempty) (hbounded : BddAbove s) (hinvariant : f '' s = s) :
    f (sSup s) = sSup s := by
  let e : ℝ ≃o ℝ := { f with map_rel_iff' := hf.le_iff_le }
  calc
    f (sSup s) = sSup (e '' s) := e.map_csSup' hne hbounded
    _ = sSup s := by rw [show e '' s = s from hinvariant]

/-- An orbit bounded above by `y` gives a common real fixed point between its
initial point and `y`. -/
theorem real_common_fixedPoint_of_bounded_orbit
    (H : Subgroup (Equiv.Perm ℝ))
    (hmono : ∀ h ∈ H, StrictMono h) {x y : ℝ}
    (hbound : ∀ h ∈ H, h x ≤ y) :
    ∃ c : ℝ, x ≤ c ∧ c ≤ y ∧ ∀ h ∈ H, h c = c := by
  let s : Set ℝ := range (fun h : H => h.1 x)
  have hx : x ∈ s := ⟨1, rfl⟩
  have hne : s.Nonempty := ⟨x, hx⟩
  have hy : y ∈ upperBounds s := by
    rintro z ⟨h, rfl⟩
    exact hbound h.1 h.2
  have hbounded : BddAbove s := ⟨y, hy⟩
  refine ⟨sSup s, le_csSup hbounded hx, csSup_le hne hy, ?_⟩
  intro h hh
  apply real_sSup_fixed_of_invariant (hmono h hh) hne hbounded
  apply Set.Subset.antisymm
  · rintro z ⟨w, ⟨g, rfl⟩, rfl⟩
    exact ⟨⟨h * g.1, H.mul_mem hh g.2⟩, rfl⟩
  · rintro z ⟨g, rfl⟩
    refine ⟨(h⁻¹ * g.1) x, ⟨⟨h⁻¹ * g.1, H.mul_mem (H.inv_mem hh) g.2⟩, rfl⟩, ?_⟩
    simp

/-- Without a common real fixed point in an interval, an orbit can move past
any prescribed point below the right endpoint. -/
theorem real_exists_moves_past
    (H : Subgroup (Equiv.Perm ℝ))
    (hmono : ∀ h ∈ H, StrictMono h) {a b x y : ℝ}
    (hnofixed : ∀ c ∈ Ioo a b, ∃ h ∈ H, h c ≠ c)
    (hax : a < x) (hyb : y < b) :
    ∃ h ∈ H, y < h x := by
  by_contra hnot
  have hbound : ∀ h ∈ H, h x ≤ y := by
    intro h hh
    exact le_of_not_gt (fun hgt => hnot ⟨h, hh, hgt⟩)
  obtain ⟨c, hxc, hcy, hfixed⟩ := real_common_fixedPoint_of_bounded_orbit H hmono hbound
  obtain ⟨h, hh, hmove⟩ := hnofixed c ⟨hax.trans_le hxc, hcy.trans_lt hyb⟩
  exact hmove (hfixed h hh)

/-- Every real cut inside `(a,b)` is changed by some rational permutation in
`H`. The cut is encoded by the rational numbers strictly below it. -/
def NoInvariantRealCut (H : Subgroup (Equiv.Perm ℚ)) (a b : ℚ) : Prop :=
  ∀ c : ℝ, (a : ℝ) < c → c < (b : ℝ) →
    ∃ h ∈ H, ∃ q : ℚ, ¬ ((h q : ℝ) < c ↔ (q : ℝ) < c)

/-- The supremum of a bounded rational orbit determines an invariant real cut. -/
theorem rational_invariant_cut_of_bounded_orbit
    (H : Subgroup (Equiv.Perm ℚ))
    (hmono : ∀ h ∈ H, StrictMono h) {x y : ℚ}
    (hbound : ∀ h ∈ H, h x ≤ y) :
    ∃ c : ℝ, (x : ℝ) ≤ c ∧ c ≤ (y : ℝ) ∧
      ∀ h ∈ H, ∀ q : ℚ, ((h q : ℝ) < c ↔ (q : ℝ) < c) := by
  let s : Set ℝ := range (fun h : H => (h.1 x : ℝ))
  have hx : (x : ℝ) ∈ s := ⟨1, rfl⟩
  have hne : s.Nonempty := ⟨x, hx⟩
  have hy : (y : ℝ) ∈ upperBounds s := by
    rintro z ⟨h, rfl⟩
    change (h.1 x : ℝ) ≤ (y : ℝ)
    exact_mod_cast hbound h.1 h.2
  have hbounded : BddAbove s := ⟨y, hy⟩
  have hpres : ∀ h ∈ H, ∀ q : ℚ, (q : ℝ) < sSup s → (h q : ℝ) < sSup s := by
    intro h hh q hq
    obtain ⟨r, ⟨g, rfl⟩, hqr⟩ := (lt_csSup_iff hbounded hne).mp hq
    have hqg : q < g.1 x := by
      change (q : ℝ) < (g.1 x : ℝ) at hqr
      exact_mod_cast hqr
    have hstep : (h q : ℝ) < (h (g.1 x) : ℝ) := by
      exact_mod_cast hmono h hh hqg
    have himage : (h (g.1 x) : ℝ) ∈ s :=
      ⟨⟨h * g.1, H.mul_mem hh g.2⟩, rfl⟩
    exact hstep.trans_le (le_csSup hbounded himage)
  refine ⟨sSup s, le_csSup hbounded hx, csSup_le hne hy, ?_⟩
  intro h hh q
  constructor
  · intro hq
    simpa using hpres h⁻¹ (H.inv_mem hh) (h q) hq
  · exact hpres h hh q

/-- The rational cofinal-motion theorem, with the real-cut hypothesis stated
explicitly. No rational completeness or intermediate value theorem is used. -/
theorem rational_exists_moves_past
    (H : Subgroup (Equiv.Perm ℚ))
    (hmono : ∀ h ∈ H, StrictMono h) {a b x y : ℚ}
    (hcuts : NoInvariantRealCut H a b) (hax : a < x) (hyb : y < b) :
    ∃ h ∈ H, y < h x := by
  by_contra hnot
  have hbound : ∀ h ∈ H, h x ≤ y := by
    intro h hh
    exact le_of_not_gt (fun hgt => hnot ⟨h, hh, hgt⟩)
  obtain ⟨c, hxc, hcy, hcut⟩ := rational_invariant_cut_of_bounded_orbit H hmono hbound
  have hac : (a : ℝ) < c := (by exact_mod_cast hax : (a : ℝ) < x).trans_le hxc
  have hcb : c < (b : ℝ) := hcy.trans_lt (by exact_mod_cast hyb)
  obtain ⟨h, hh, q, hchange⟩ := hcuts c hac hcb
  exact hchange (hcut h hh q)

/-- A finite collection of displaced rational intervals covering all real cuts
between `x` and `y` suffices to move `x` past `y`. This provides a finite way to
discharge the cut condition on the compact interval relevant to a motion. -/
theorem rational_exists_moves_past_of_finite_cover
    (H : Subgroup (Equiv.Perm ℚ))
    (hmono : ∀ h ∈ H, StrictMono h) {x y : ℚ}
    (intervals : List (ℚ × ℚ))
    (hcover : ∀ c ∈ Icc (x : ℝ) (y : ℝ), ∃ I ∈ intervals,
      (I.1 : ℝ) < c ∧ c < (I.2 : ℝ))
    (hmove : ∀ I ∈ intervals, ∃ h ∈ H, I.2 ≤ h I.1) :
    ∃ h ∈ H, y < h x := by
  by_contra hnot
  have hbound : ∀ h ∈ H, h x ≤ y := by
    intro h hh
    exact le_of_not_gt (fun hgt => hnot ⟨h, hh, hgt⟩)
  obtain ⟨c, hxc, hcy, hcut⟩ := rational_invariant_cut_of_bounded_orbit H hmono hbound
  obtain ⟨I, hI, hl, hr⟩ := hcover c ⟨hxc, hcy⟩
  obtain ⟨h, hh, hdisplace⟩ := hmove I hI
  have hright : c < (h I.1 : ℝ) := hr.trans_le (by exact_mod_cast hdisplace)
  exact (not_lt_of_gt hright) ((hcut h hh I.1).mpr hl)

/-- Cofinal motion compresses a closed rational subinterval toward a fixed
right endpoint. -/
theorem rational_interval_compression
    (H : Subgroup (Equiv.Perm ℚ))
    (hmono : ∀ h ∈ H, StrictMono h) {a b x y target : ℚ}
    (hcuts : NoInvariantRealCut H a b) (hfix : ∀ h ∈ H, h b = b)
    (hax : a < x) (hyb : y < b) (htarget : target < b) :
    ∃ h ∈ H, MapsTo h (Icc x y) (Ioo target b) := by
  obtain ⟨h, hh, hmove⟩ := rational_exists_moves_past H hmono hcuts hax htarget
  refine ⟨h, hh, ?_⟩
  intro z hz
  have hright : h y < b := by simpa [hfix h hh] using hmono h hh hyb
  exact ⟨hmove.trans_le ((hmono h hh).monotone hz.1),
    ((hmono h hh).monotone hz.2).trans_lt hright⟩

#audit_axioms real_exists_moves_past
#audit_axioms rational_exists_moves_past
#audit_axioms rational_exists_moves_past_of_finite_cover
#audit_axioms rational_interval_compression

end Kourovka.P21_38
