import Kourovka.Problems.P21_38.Proof.BinaryDyadic
import Kourovka.Problems.P21_38.Proof.AffineBranches
import Kourovka.Problems.P21_38.Proof.BinaryPartitions
import Kourovka.Problems.P21_38.Proof.OrbitMotion
import Kourovka.Problems.P21_38.Proof.CommutatorExtraction
import Kourovka.Problems.P21_38.Proof.EndpointSlopes

/-!
# Local branch corrections

The input relation is actual branch equivalence in a subgroup. Powers of a
one-sided branch shift, and their conjugates, give the local corrections used
in Golan-Polak's local interpolation argument (arXiv:1608.02572v2, Section 7).
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson
open BinaryWord Set

/-- Any two interior binary intervals have all sufficiently deep descendants
equivalent by elements of the actual subgroup. The suffix lengths may differ. -/
def DeepBranchCommunication (H : Subgroup (Equiv.Perm ℚ)) : Prop :=
  ∀ u v : List Bool, (false ∈ u ∧ true ∈ u) → (false ∈ v ∧ true ∈ v) →
    ∃ N : ℕ, ∀ s t : List Bool, N ≤ s.length → N ≤ t.length →
      BranchRelated H (u ++ s) (v ++ t)

/-- A branch that is equivalent to a zero extension of the distinguished word. -/
def ZeroExtensionRelated (H : Subgroup (Equiv.Perm ℚ)) (u w : List Bool) : Prop :=
  ∃ k : ℕ, BranchRelated H (u ++ List.replicate k false) w

/-- Deep communication relates every sufficiently deep interior descendant to
a zero extension of any word containing `true`. -/
theorem DeepBranchCommunication.eventually_zeroExtension
    {H : Subgroup (Equiv.Perm ℚ)} (hdeep : DeepBranchCommunication H)
    {u w : List Bool} (hu : true ∈ u) (hw : false ∈ w ∧ true ∈ w) :
    ∃ N : ℕ, ∀ s : List Bool, N ≤ s.length → ZeroExtensionRelated H u (w ++ s) := by
  obtain ⟨N, hN⟩ := hdeep (u ++ [false]) w (by simp [hu]) hw
  refine ⟨N, fun s hs => ⟨N + 1, ?_⟩⟩
  have hr := hN (List.replicate N false) s (by simp) hs
  simpa only [List.append_assoc, List.singleton_append, List.replicate_succ] using hr

/-- A common refinement depth works for a finite collection of interior words. -/
theorem DeepBranchCommunication.eventually_zeroExtension_list
    {H : Subgroup (Equiv.Perm ℚ)} (hdeep : DeepBranchCommunication H)
    {u : List Bool} (hu : true ∈ u) (ws : List (List Bool))
    (hws : ∀ w ∈ ws, false ∈ w ∧ true ∈ w) :
    ∃ N : ℕ, ∀ w ∈ ws, ∀ s : List Bool, N ≤ s.length →
      ZeroExtensionRelated H u (w ++ s) := by
  induction ws with
  | nil => exact ⟨0, by simp⟩
  | cons w ws ih =>
    obtain ⟨N, hN⟩ := hdeep.eventually_zeroExtension hu (hws w List.mem_cons_self)
    obtain ⟨M, hM⟩ := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
    refine ⟨max N M, ?_⟩
    intro v hv s hs
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hN s ((le_max_left N M).trans hs)
    · exact hM v hv s ((le_max_right N M).trans hs)

namespace HasBranch

theorem left_endpoint {f : Equiv.Perm ℚ} {u v : List Bool}
    (h : HasBranch f u v) : f (chart u 0) = chart v 0 :=
  h 0 ⟨le_rfl, zero_le_one⟩

theorem right_endpoint {f : Equiv.Perm ℚ} {u v : List Bool}
    (h : HasBranch f u v) : f (chart u 1) = chart v 1 :=
  h 1 ⟨zero_le_one, le_rfl⟩

theorem zero_tails_left_endpoint {f : Equiv.Perm ℚ} {u v : List Bool} {n m : ℕ}
    (h : HasBranch f (u ++ List.replicate n false) (v ++ List.replicate m false)) :
    f (chart u 0) = chart v 0 := by
  simpa only [chart_append, chart_replicate_false, zero_div] using h.left_endpoint

/-- Two maps having the same branch agree on its whole closed interval. -/
theorem eqOn_of_same_branch {f g : Equiv.Perm ℚ} {u v : List Bool}
    (hf : HasBranch f u v) (hg : HasBranch g u v) :
    EqOn f g (Icc (chart u 0) (chart u 1)) := by
  intro t ht
  let r : ℚ := (chartPerm u)⁻¹ t
  have hrchart : chart u r = t := by
    simpa only [chartPerm_apply] using perm_apply_inv_self (chartPerm u) t
  have hr0 : 0 ≤ r := (chart_strictMono u).le_iff_le.mp (by rw [hrchart]; exact ht.1)
  have hr1 : r ≤ 1 := (chart_strictMono u).le_iff_le.mp (by rw [hrchart]; exact ht.2)
  calc
    f t = f (chart u r) := congrArg f hrchart.symm
    _ = chart v r := hf r ⟨hr0, hr1⟩
    _ = g (chart u r) := (hg r ⟨hr0, hr1⟩).symm
    _ = g t := congrArg g hrchart

/-- Iterating a one-sided branch shift removes successive trailing zeros. -/
theorem pow_zero_shift {h : Equiv.Perm ℚ} {u : List Bool}
    (hshift : HasBranch h (u ++ [false]) u) (n : ℕ) :
    HasBranch (h ^ n) (u ++ List.replicate n false) u := by
  induction n with
  | zero => simpa using HasBranch.one u
  | succ n ih =>
    have hs := (hshift.append (List.replicate n false)).mul ih
    simpa only [List.append_assoc, List.singleton_append, List.replicate_succ,
      pow_succ] using hs

/-- A suitable integer power changes any zero tail to any other zero tail. -/
theorem exists_zpow_zero_shift {h : Equiv.Perm ℚ} {u : List Bool}
    (hshift : HasBranch h (u ++ [false]) u) (n m : ℕ) :
    ∃ j : ℤ, HasBranch (h ^ j)
      (u ++ List.replicate n false) (u ++ List.replicate m false) := by
  have hforward : ∀ n m : ℕ, m ≤ n →
      HasBranch (h ^ (n - m)) (u ++ List.replicate n false)
        (u ++ List.replicate m false) := by
    intro n m hmn
    have hs := (hshift.pow_zero_shift (n - m)).append (List.replicate m false)
    simpa only [List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel hmn] using hs
  rcases le_total m n with hmn | hnm
  · exact ⟨(n - m : ℕ), by simpa using hforward n m hmn⟩
  · exact ⟨-((m - n : ℕ) : ℤ), by simpa using (hforward m n hnm).inv⟩

end HasBranch

/-- The subgroup fixing the whole binary interval `u` pointwise. -/
def wordFixer (H : Subgroup (Equiv.Perm ℚ)) (u : List Bool) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ H ∧ HasBranch f u u}
  one_mem' := ⟨H.one_mem, HasBranch.one u⟩
  mul_mem' := fun hf hg => ⟨H.mul_mem hf.1 hg.1, hg.2.mul hf.2⟩
  inv_mem' := fun hf => ⟨H.inv_mem hf.1, hf.2.inv⟩

/-- Pointwise identity is retained by every integer power of a permutation. -/
theorem eqOn_id_zpow {X : Type*} {h : Equiv.Perm X} {U : Set X}
    (hfix : EqOn h id U) (j : ℤ) : EqOn (h ^ j) id U := by
  intro x hx
  have hpow : ∀ n : ℕ, (h ^ n) x = x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, hfix hx]
      exact ih
  cases j with
  | ofNat n => simpa using hpow n
  | negSucc n =>
    rw [zpow_negSucc]
    exact Equiv.Perm.inv_eq_iff_eq.mpr (hpow (n + 1)).symm

/-- Conjugating a power transports both its branch and its pointwise fixed set. -/
theorem exists_transported_zero_shift
    {H : Subgroup (Equiv.Perm ℚ)} {h q : Equiv.Perm ℚ} {u w : List Bool}
    (hh : h ∈ H) (hq : q ∈ H)
    (hshift : HasBranch h (u ++ [false]) u)
    {U V : Set ℚ} (hfix : EqOn h id U) (hcover : MapsTo ⇑(q⁻¹) V U)
    {k : ℕ} (hbranch : HasBranch q (u ++ List.replicate k false) w)
    (n m : ℕ) :
    ∃ j : ℤ, ∃ g ∈ H, g = q * h ^ j * q⁻¹ ∧
      HasBranch g (w ++ List.replicate n false) (w ++ List.replicate m false) ∧
      EqOn g id V := by
  obtain ⟨j, hj⟩ := hshift.exists_zpow_zero_shift (k + n) (k + m)
  refine ⟨j, q * h ^ j * q⁻¹,
    H.mul_mem (H.mul_mem hq (H.zpow_mem hh j)) (H.inv_mem hq), rfl, ?_, ?_⟩
  · have hstart := hbranch.inv.append (List.replicate n false)
    have hend := hbranch.append (List.replicate m false)
    have hj' : HasBranch (h ^ j)
        ((u ++ List.replicate k false) ++ List.replicate n false)
        ((u ++ List.replicate k false) ++ List.replicate m false) := by
      simpa only [List.append_assoc, ← List.replicate_add] using hj
    simpa only [mul_assoc] using (hstart.mul hj').mul hend
  · intro x hx
    simp only [Equiv.Perm.mul_apply]
    have hfixed : (h ^ j) (q⁻¹ x) = q⁻¹ x := eqOn_id_zpow hfix j (hcover hx)
    rw [hfixed]
    exact Equiv.apply_symm_apply q x

/-- The orbital motion of the interval fixer transports the one-sided shift
while preserving any prescribed preceding interval. This is the local
correction step, with the orbital hypothesis recorded as a real-cut condition. -/
theorem exists_zero_shift_fixing_left
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    {h : Equiv.Perm ℚ} (hh : h ∈ H) {u w : List Bool}
    (hshift : HasBranch h (u ++ [false]) u)
    {α : ℚ} (hα : α < chart u 0) (hfix : EqOn h id (Icc α (chart u 0)))
    (hcuts : NoInvariantRealCut (wordFixer H u) 0 (chart u 0))
    (hw : ZeroExtensionRelated H u w) {a : ℚ}
    (ha : 0 < a) (n m : ℕ) :
    ∃ j : ℤ, ∃ q ∈ H,
      HasBranch (q * h ^ j * q⁻¹)
        (w ++ List.replicate n false) (w ++ List.replicate m false) ∧
      EqOn (q * h ^ j * q⁻¹) id (Icc a (chart w 0)) := by
  obtain ⟨k, f, hf, hfb⟩ := hw
  have hfmono := compactF_strictMono (hH hf)
  have hfinvmono := strictMono_perm_inv hfmono
  have hf0 : f 0 = 0 := compactF_fix_nonpos (hH hf) le_rfl
  have hfβ : f (chart u 0) = chart w 0 := by
    simpa only [chart_append, chart_replicate_false, zero_div] using hfb.left_endpoint
  have hfi0 : f⁻¹ 0 = 0 := Equiv.Perm.inv_eq_iff_eq.mpr hf0.symm
  have hfiβ : f⁻¹ (chart w 0) = chart u 0 := by rw [← hfβ]; simp
  have hx0 : 0 < f⁻¹ a := by simpa only [hfi0] using hfinvmono ha
  have hmonoK : ∀ g ∈ wordFixer H u, StrictMono g :=
    fun g hg => compactF_strictMono (hH hg.1)
  obtain ⟨g, hg, hmove⟩ := rational_exists_moves_past (wordFixer H u) hmonoK hcuts hx0 hα
  have hgβ : g (chart u 0) = chart u 0 := hg.2.left_endpoint
  let q : Equiv.Perm ℚ := f * g⁻¹
  have hq : q ∈ H := H.mul_mem hf (H.inv_mem hg.1)
  have hqb : HasBranch q (u ++ List.replicate k false) w :=
    (hg.2.inv.append (List.replicate k false)).mul hfb
  have hcover : MapsTo ⇑(q⁻¹) (Icc a (chart w 0)) (Icc α (chart u 0)) := by
    intro t ht
    have hlo : α ≤ g (f⁻¹ t) :=
      hmove.le.trans ((hmonoK g hg).monotone (hfinvmono.monotone ht.1))
    have hfi : f⁻¹ t ≤ chart u 0 := by
      rw [← hfiβ]
      exact hfinvmono.monotone ht.2
    have hhi : g (f⁻¹ t) ≤ chart u 0 := by
      simpa only [hgβ] using (hmonoK g hg).monotone hfi
    simpa only [q, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, Set.mem_Icc] using And.intro hlo hhi
  obtain ⟨j, z, _, rfl, hzb, hzf⟩ :=
    exists_transported_zero_shift hh hq hshift hfix hcover hqb n m
  exact ⟨j, q, hq, hzb, hzf⟩

/-- Correct the two zero-tail lengths of an existing branch while retaining
the map on the preceding interval. Both corrections are conjugates of powers
of the specified one-sided shift. -/
theorem exists_corrected_zero_branch
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    {h g : Equiv.Perm ℚ} (hh : h ∈ H) (hg : g ∈ H) {u w₁ w₂ : List Bool}
    (hshift : HasBranch h (u ++ [false]) u)
    {α : ℚ} (hα : α < chart u 0) (hfix : EqOn h id (Icc α (chart u 0)))
    (hcuts : NoInvariantRealCut (wordFixer H u) 0 (chart u 0))
    (hw₁ : ZeroExtensionRelated H u w₁) (hw₂ : ZeroExtensionRelated H u w₂)
    {m₁ m₂ : ℕ} (hbranch : HasBranch g
      (w₁ ++ List.replicate m₁ false) (w₂ ++ List.replicate m₂ false))
    {a : ℚ} (ha : 0 < a) (n₁ n₂ : ℕ) :
    ∃ j₁ : ℤ, ∃ q₁ ∈ H, ∃ j₂ : ℤ, ∃ q₂ ∈ H,
      HasBranch ((q₂ * h ^ j₂ * q₂⁻¹) * g * (q₁ * h ^ j₁ * q₁⁻¹))
        (w₁ ++ List.replicate n₁ false) (w₂ ++ List.replicate n₂ false) ∧
      EqOn ((q₂ * h ^ j₂ * q₂⁻¹) * g * (q₁ * h ^ j₁ * q₁⁻¹)) g
        (Icc a (chart w₁ 0)) := by
  obtain ⟨j₁, q₁, hq₁, hlbranch, hlfix⟩ :=
    exists_zero_shift_fixing_left hH hh hshift hα hfix hcuts hw₁ ha n₁ m₁
  have hgmono := compactF_strictMono (hH hg)
  have hg0 : g 0 = 0 := compactF_fix_nonpos (hH hg) le_rfl
  have hga : 0 < g a := by simpa only [hg0] using hgmono ha
  obtain ⟨j₂, q₂, hq₂, hrbranch, hrfix⟩ :=
    exists_zero_shift_fixing_left hH hh hshift hα hfix hcuts hw₂ hga m₂ n₂
  refine ⟨j₁, q₁, hq₁, j₂, q₂, hq₂, ?_, ?_⟩
  · simpa only [mul_assoc] using (hlbranch.mul hbranch).mul hrbranch
  · intro t ht
    have hlt : (q₁ * h ^ j₁ * q₁⁻¹) t = t := hlfix ht
    change (q₂ * h ^ j₂ * q₂⁻¹) (g ((q₁ * h ^ j₁ * q₁⁻¹) t)) = g t
    rw [hlt]
    apply hrfix
    refine ⟨hgmono.monotone ht.1, ?_⟩
    simpa only [hbranch.zero_tails_left_endpoint] using hgmono.monotone ht.2

/-- Endpoint characters of conjugated powers depend only on the original
element and its exponent. -/
theorem endpointCharacter_conjugate_zpow (h q : F) (j : ℤ) :
    endpointCharacter (q * h ^ j * q⁻¹) = endpointCharacter h ^ j := by
  simp only [map_mul, map_zpow, map_inv]
  simp [mul_assoc]

/-- At a matching dyadic left endpoint, a PL map has a branch between suitable
zero extensions of the two specified binary intervals. This supplies the next
branch needed by the finite interpolation induction. -/
theorem exists_zero_branch_of_left_endpoint
    {g : Equiv.Perm ℚ} (hg : g ∈ PLGroup 2 (powSlopes 0)) {u v : List Bool}
    (hendpoint : g (chart u 0) = chart v 0) :
    ∃ n m : ℕ, HasBranch g (u ++ List.replicate n false) (v ++ List.replicate m false) := by
  let p : Equiv.Perm ℚ := (chartPerm v)⁻¹ * g * chartPerm u
  have hp : p ∈ PLGroup 2 (powSlopes 0) :=
    (PLGroup 2 (powSlopes 0)).mul_mem
      ((PLGroup 2 (powSlopes 0)).mul_mem
        ((PLGroup 2 (powSlopes 0)).inv_mem (chartPerm_mem v)) hg) (chartPerm_mem u)
  have hp0 : p 0 = 0 := by
    change (chartPerm v)⁻¹ (g (chartPerm u 0)) = 0
    rw [chartPerm_apply, hendpoint, ← chartPerm_apply v 0, perm_inv_apply_self]
  obtain ⟨N, B, hA⟩ := hp.2.1
  obtain ⟨s, ⟨z, rfl⟩, _, haff⟩ := hA.slope 0
  have haff' : ∀ t : ℚ, 0 ≤ t → t ≤ 1 / 2 ^ N → p t = (2 : ℚ) ^ z * t := by
    intro t ht0 ht1
    have h := haff t (by simpa [gridPt] using ht0) (by simpa [gridPt] using ht1)
    simpa [gridPt, hp0] using h
  let n : ℕ := N + z.toNat
  let m : ℕ := N + (-z).toNat
  have hexponent : (n : ℤ) = (m : ℤ) + z := by
    dsimp [n, m]
    have h := Int.toNat_sub_toNat_neg z
    omega
  have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ m * (2 : ℚ) ^ z := by
    rw [← zpow_natCast, hexponent, zpow_add₀ (by norm_num)]
    simp only [zpow_natCast]
  have hden : (2 : ℚ) ^ N ≤ (2 : ℚ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (by dsimp [n]; omega)
  refine ⟨n, m, ?_⟩
  intro t ht
  have harg0 : 0 ≤ t / (2 : ℚ) ^ n := div_nonneg ht.1 (by positivity)
  have harg1 : t / (2 : ℚ) ^ n ≤ 1 / 2 ^ N := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [ht.2, pow_pos (show (0 : ℚ) < 2 by norm_num) N]
  have hpvalue : p (t / (2 : ℚ) ^ n) = t / (2 : ℚ) ^ m := by
    rw [haff' _ harg0 harg1, hpow]
    have hz : (2 : ℚ) ^ z ≠ 0 := zpow_ne_zero _ (by norm_num)
    field_simp
  have hvalue := congrArg (chartPerm v) hpvalue
  change chartPerm v ((chartPerm v)⁻¹ (g (chartPerm u (t / (2 : ℚ) ^ n)))) =
    chartPerm v (t / (2 : ℚ) ^ m) at hvalue
  simpa only [chart_append, chart_replicate_false, perm_apply_inv_self,
    chartPerm_apply] using hvalue

/-- A conjugate fixing the interpolation region cancels the two
endpoint characters simultaneously. The retained map then lies in the compact
core. -/
theorem exists_core_adjustment_of_compression
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    {h g : Equiv.Perm ℚ} (hh : h ∈ H) (hg : g ∈ H) {U V : Set ℚ}
    (hfix : EqOn h id U) {j : ℤ}
    (hcharacter : endpointCharacter ⟨g, hH hg⟩ = endpointCharacter ⟨h, hH hh⟩ ^ j)
    (hcompress : ∃ q ∈ H, MapsTo q V U) :
    ∃ k ∈ H, k ∈ compactCore 0 ∧ EqOn k g V := by
  obtain ⟨q, hq, hqmap⟩ := hcompress
  let hF : F := ⟨h, hH hh⟩
  let gF : F := ⟨g, hH hg⟩
  let qF : F := ⟨q, hH hq⟩
  let kF : F := gF * (qF⁻¹ * hF ^ (-j) * qF)
  have hkH : kF.1 ∈ H :=
    H.mul_mem hg (H.mul_mem (H.mul_mem (H.inv_mem hq) (H.zpow_mem hh (-j))) hq)
  have hkchar : endpointCharacter kF = 1 := by
    change endpointCharacter (gF * (qF⁻¹ * hF ^ (-j) * qF)) = 1
    rw [map_mul]
    have hconj : endpointCharacter (qF⁻¹ * hF ^ (-j) * qF) = endpointCharacter hF ^ (-j) := by
      simpa only [inv_inv] using endpointCharacter_conjugate_zpow hF qF⁻¹ (-j)
    rw [hconj]
    change endpointCharacter ⟨g, hH hg⟩ * endpointCharacter ⟨h, hH hh⟩ ^ (-j) = 1
    rw [hcharacter, zpow_neg, mul_inv_cancel]
  refine ⟨kF.1, hkH, (mem_endpointCharacter_ker_iff kF).mp hkchar, ?_⟩
  intro t ht
  change g (q⁻¹ ((h ^ (-j)) (q t))) = g t
  have hht : (h ^ (-j)) (q t) = q t := eqOn_id_zpow hfix (-j) (hqmap ht)
  rw [hht]
  simp

/-- Extend an existing interpolation across a finite paired binary partition.
At each step only the next right-hand germ is adjusted. The endpoint character
remains an integer power of the distinguished shift's character. -/
theorem exists_branch_partition_extension
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    {h : Equiv.Perm ℚ} (hh : h ∈ H) {u : List Bool}
    (hshift : HasBranch h (u ++ [false]) u)
    {α : ℚ} (hα : α < chart u 0) (hfix : EqOn h id (Icc α (chart u 0)))
    (hcuts : NoInvariantRealCut (wordFixer H u) 0 (chart u 0))
    {start : ℚ} (hstart : 0 < start) (f : F)
    {a b c d : ℚ} {us vs : List (List Bool)}
    (hu : WordPartition a b us) (hv : WordPartition c d vs)
    (hlen : us.length = vs.length)
    (hbranches : ∀ U V, (U, V) ∈ us.zip vs → HasBranch f.1 U V)
    (hus : ∀ U ∈ us, ZeroExtensionRelated H u U)
    (hvs : ∀ V ∈ vs, ZeroExtensionRelated H u V)
    (hstarta : start ≤ a) (g : Equiv.Perm ℚ) (hg : g ∈ H)
    (heq : EqOn g f.1 (Icc start a)) (j : ℤ)
    (hcharacter : endpointCharacter ⟨g, hH hg⟩ = endpointCharacter ⟨h, hH hh⟩ ^ j) :
    ∃ k : ℤ, ∃ z : Equiv.Perm ℚ, ∃ hz : z ∈ H,
      endpointCharacter ⟨z, hH hz⟩ = endpointCharacter ⟨h, hH hh⟩ ^ k ∧
      EqOn z f.1 (Icc start b) := by
  induction hu generalizing c d vs g j with
  | nil a =>
    have hvsnil : vs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst vs
    cases hv
    exact ⟨j, g, hg, hcharacter, heq⟩
  | @cons a b e U us hlu hru htu ih =>
    cases vs with
    | nil => simp at hlen
    | cons V vs =>
      cases hv with
      | @cons _ _ e' _ _ hlv hrv htv =>
        have hlen' : us.length = vs.length := by simpa using hlen
        have hfirst : HasBranch f.1 U V := hbranches U V (by simp)
        have hleft : g (chart U 0) = chart V 0 := by
          calc
            g (chart U 0) = g a := congrArg g hlu
            _ = f.1 a := heq ⟨hstarta, le_rfl⟩
            _ = f.1 (chart U 0) := congrArg f.1 hlu.symm
            _ = chart V 0 := hfirst.left_endpoint
        obtain ⟨m₁, m₂, hgb⟩ := exists_zero_branch_of_left_endpoint (hH hg).1 hleft
        obtain ⟨j₁, q₁, hq₁, j₂, q₂, hq₂, hzb, hzg⟩ :=
          exists_corrected_zero_branch hH hh hg hshift hα hfix hcuts
            (hus U List.mem_cons_self) (hvs V List.mem_cons_self) hgb hstart 0 0
        let z : Equiv.Perm ℚ := (q₂ * h ^ j₂ * q₂⁻¹) * g * (q₁ * h ^ j₁ * q₁⁻¹)
        have hzH : z ∈ H := H.mul_mem
          (H.mul_mem (H.mul_mem (H.mul_mem hq₂ (H.zpow_mem hh j₂)) (H.inv_mem hq₂)) hg)
          (H.mul_mem (H.mul_mem hq₁ (H.zpow_mem hh j₁)) (H.inv_mem hq₁))
        have hzb' : HasBranch z U V := by simpa only [List.replicate_zero, List.append_nil] using hzb
        have hzg' : EqOn z g (Icc start a) := by simpa only [hlu] using hzg
        have hzf : EqOn z f.1 (Icc start e) := by
          intro t ht
          by_cases hta : t ≤ a
          · exact (hzg' ⟨ht.1, hta⟩).trans (heq ⟨ht.1, hta⟩)
          · apply hzb'.eqOn_of_same_branch hfirst
            exact ⟨hlu ▸ (le_of_not_ge hta), hru ▸ ht.2⟩
        have hze : start ≤ e := by
          have hue : a < e := by simpa only [hlu, hru] using chart_zero_lt_one U
          exact hstarta.trans hue.le
        have hzchar : endpointCharacter ⟨z, hH hzH⟩ =
            endpointCharacter ⟨h, hH hh⟩ ^ (j₂ + j + j₁) := by
          let hF : F := ⟨h, hH hh⟩
          let gF : F := ⟨g, hH hg⟩
          let q₁F : F := ⟨q₁, hH hq₁⟩
          let q₂F : F := ⟨q₂, hH hq₂⟩
          change endpointCharacter ((q₂F * hF ^ j₂ * q₂F⁻¹) * gF *
            (q₁F * hF ^ j₁ * q₁F⁻¹)) = endpointCharacter hF ^ (j₂ + j + j₁)
          rw [map_mul, map_mul, endpointCharacter_conjugate_zpow,
            endpointCharacter_conjugate_zpow]
          change endpointCharacter hF ^ j₂ * endpointCharacter ⟨g, hH hg⟩ *
            endpointCharacter hF ^ j₁ = endpointCharacter hF ^ (j₂ + j + j₁)
          rw [hcharacter, ← zpow_add, ← zpow_add]
        have hbtail : ∀ U' V', (U', V') ∈ us.zip vs → HasBranch f.1 U' V' := by
          intro U' V' huv
          apply hbranches U' V'
          simpa only [List.zip_cons_cons] using (List.mem_cons_of_mem (U, V) huv)
        exact ih htv hlen' hbtail
          (fun U' hU' => hus U' (List.mem_cons_of_mem U hU'))
          (fun V' hV' => hvs V' (List.mem_cons_of_mem V hV'))
          hze z hzH hzf (j₂ + j + j₁) hzchar

/-- Prepared finite branch data yield a genuine compact-core interpolant in
`H`. The proof first constructs the branches, then cancels both endpoint
characters using a conjugate that fixes the whole interpolation interval. -/
theorem exists_core_interpolant_of_wordPartitions
    {H : Subgroup (Equiv.Perm ℚ)} (hH : H ≤ compactF 0 1)
    {h : Equiv.Perm ℚ} (hh : h ∈ H) {u : List Bool}
    (hshift : HasBranch h (u ++ [false]) u)
    {α : ℚ} (hα : α < chart u 0) (hfix : EqOn h id (Icc α (chart u 0)))
    (hcuts : NoInvariantRealCut (wordFixer H u) 0 (chart u 0))
    (f : F) {a b c d : ℚ} {us vs : List (List Bool)}
    (ha : 0 < a) (hfa : f.1 a = a)
    (hu : WordPartition a b us) (hv : WordPartition c d vs)
    (hlen : us.length = vs.length)
    (hbranches : ∀ U V, (U, V) ∈ us.zip vs → HasBranch f.1 U V)
    (hus : ∀ U ∈ us, ZeroExtensionRelated H u U)
    (hvs : ∀ V ∈ vs, ZeroExtensionRelated H u V)
    (hcompress : ∃ q ∈ H, MapsTo q (Icc a b) (Icc α (chart u 0))) :
    ∃ k ∈ H, k ∈ compactCore 0 ∧ EqOn k f.1 (Icc a b) := by
  have hone : EqOn (⇑(1 : Equiv.Perm ℚ)) f.1 (Icc a a) := by
    intro t ht
    have hta : t = a := le_antisymm ht.2 ht.1
    subst t
    exact hfa.symm
  have honechar : endpointCharacter ⟨1, hH H.one_mem⟩ =
      endpointCharacter ⟨h, hH hh⟩ ^ (0 : ℤ) := by
    change endpointCharacter (1 : F) = _
    simp
  obtain ⟨j, g, hg, hgchar, hgf⟩ := exists_branch_partition_extension
    hH hh hshift hα hfix hcuts ha f hu hv hlen hbranches hus hvs
    le_rfl 1 H.one_mem hone 0 honechar
  obtain ⟨k, hk, hkcore, hkg⟩ := exists_core_adjustment_of_compression
    hH hh hg hfix hgchar hcompress
  exact ⟨k, hk, hkcore, fun t ht => (hkg ht).trans (hgf ht)⟩

#audit_axioms exists_transported_zero_shift
#audit_axioms exists_zero_shift_fixing_left
#audit_axioms exists_corrected_zero_branch
#audit_axioms exists_zero_branch_of_left_endpoint
#audit_axioms exists_core_adjustment_of_compression
#audit_axioms exists_branch_partition_extension
#audit_axioms exists_core_interpolant_of_wordPartitions

end Kourovka.P21_38
