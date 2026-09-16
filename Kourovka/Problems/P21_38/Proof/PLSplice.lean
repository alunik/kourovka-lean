import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.PLMoves

/-!
# Gluing increasing dyadic piecewise-linear permutations

Two increasing permutations with the same value at a dyadic cut can be
joined there. The inverse is joined at their common image. All regularity
claims concern the actual rational permutation.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

def spliceFun (f g : ℚ → ℚ) (a t : ℚ) : ℚ := if t ≤ a then f t else g t

theorem spliceFun_left (f g : ℚ → ℚ) {a t : ℚ} (ht : t ≤ a) :
    spliceFun f g a t = f t := ite_eq_left ht

theorem spliceFun_right {f g : ℚ → ℚ} {a t : ℚ}
    (ha : f a = g a) (ht : a ≤ t) : spliceFun f g a t = g t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [spliceFun, ha]
  · exact ite_eq_right (not_le.mpr ht)

theorem spliceFun_strictMono {f g : ℚ → ℚ} {a : ℚ}
    (hf : StrictMono f) (hg : StrictMono g) (ha : f a = g a) :
    StrictMono (spliceFun f g a) := by
  intro x y hxy
  by_cases hy : y ≤ a
  · rw [spliceFun_left f g hy, spliceFun_left f g (hxy.le.trans hy)]
    exact hf hxy
  · by_cases hx : x ≤ a
    · rw [spliceFun_left f g hx, spliceFun_right ha (le_of_not_ge hy)]
      exact (hf.monotone hx).trans_lt (ha ▸ hg (lt_of_not_ge hy))
    · rw [spliceFun_right ha (le_of_not_ge hx), spliceFun_right ha (le_of_not_ge hy)]
      exact hg hxy

theorem spliceFun_inverse {f g : Equiv.Perm ℚ} {a : ℚ}
    (hf : StrictMono f) (hg : StrictMono g) (ha : f a = g a) (t : ℚ) :
    spliceFun (⇑(f⁻¹)) (⇑(g⁻¹)) (f a) (spliceFun f g a t) = t := by
  by_cases ht : t ≤ a
  · rw [spliceFun_left f g ht,
      spliceFun_left (⇑(f⁻¹)) (⇑(g⁻¹)) (hf.monotone ht)]
    exact f.symm_apply_apply t
  · rw [spliceFun_right ha (le_of_not_ge ht), spliceFun, ite_eq_right]
    · exact g.symm_apply_apply t
    · rw [ha]
      exact not_le.mpr (hg (lt_of_not_ge ht))

/-- Join two increasing permutations which agree at the cut. -/
def splicePerm (f g : Equiv.Perm ℚ) (a : ℚ)
    (hf : StrictMono f) (hg : StrictMono g) (ha : f a = g a) : Equiv.Perm ℚ where
  toFun := spliceFun f g a
  invFun := spliceFun (⇑(f⁻¹)) (⇑(g⁻¹)) (f a)
  left_inv := spliceFun_inverse hf hg ha
  right_inv t := by
    have hia : f⁻¹ (f a) = g⁻¹ (f a) := by
      calc f⁻¹ (f a) = a := f.symm_apply_apply a
           _ = g⁻¹ (f a) := by rw [ha]; exact (g.symm_apply_apply a).symm
    have hi := spliceFun_inverse (strictMono_perm_inv hf) (strictMono_perm_inv hg) hia t
    simpa using hi

@[simp] theorem splicePerm_apply (f g : Equiv.Perm ℚ) (a : ℚ)
    (hf : StrictMono f) (hg : StrictMono g) (ha : f a = g a) (t : ℚ) :
    splicePerm f g a hf hg ha t = spliceFun f g a t := rfl

/-- Different grid witnesses can be refined to one grid before gluing. -/
theorem exists_gridAffine_splice {m : ℕ} [Fact (1 < m)] {Ω : Submonoid ℚ}
    {f g : ℚ → ℚ} {a : ℚ}
    (hf : ∃ N B, GridAffine m Ω f N B)
    (hg : ∃ N B, GridAffine m Ω g N B)
    (ha : ∃ N, a ∈ Grid m N) (heq : f a = g a) :
    ∃ N B, GridAffine m Ω (spliceFun f g a) N B := by
  obtain ⟨Nf, Bf, hf⟩ := hf
  obtain ⟨Ng, Bg, hg⟩ := hg
  obtain ⟨Na, ha⟩ := ha
  let N := max (max Nf Ng) Na
  have hNf : Nf ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hNg : Ng ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have hNa : Na ≤ N := le_max_right _ _
  let B := max (Bf + N) (Bg + N)
  have hf' : GridAffine m Ω f N B :=
    (hf.mono_level hNf).mono_bound (le_max_left _ _)
  have hg' : GridAffine m Ω g N B :=
    (hg.mono_level hNg).mono_bound (le_max_right _ _)
  exact ⟨N, B, hf'.glue hg' (grid_mono hNa ha)
    (fun _ ht => spliceFun_left f g ht) (fun _ ht => spliceFun_right heq ht)⟩

theorem splicePerm_mem_PLGroup {m : ℕ} [Fact (1 < m)] {Ω : Submonoid ℚ}
    {f g : Equiv.Perm ℚ} {a : ℚ}
    (hf : f ∈ PLGroup m Ω) (hg : g ∈ PLGroup m Ω)
    (ha : ∃ N, a ∈ Grid m N) (heq : f a = g a) :
    splicePerm f g a hf.1 hg.1 heq ∈ PLGroup m Ω := by
  have himage : ∃ N, f a ∈ Grid m N := by
    obtain ⟨Nf, Bf, hfg⟩ := hf.2.1
    obtain ⟨Na, ha⟩ := ha
    exact ⟨_, hfg.mapsGrid ha⟩
  have hia : f⁻¹ (f a) = g⁻¹ (f a) := by
    calc f⁻¹ (f a) = a := f.symm_apply_apply a
         _ = g⁻¹ (f a) := by rw [heq]; exact (g.symm_apply_apply a).symm
  exact ⟨spliceFun_strictMono hf.1 hg.1 heq,
    exists_gridAffine_splice hf.2.1 hg.2.1 ha heq,
    exists_gridAffine_splice hf.2.2 hg.2.2 himage hia⟩

#audit_axioms splicePerm_mem_PLGroup

end Kourovka.P21_38
