import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimension subadditivity for actual first group cohomology.

The short-exact bound follows from mathlib's long exact cohomology sequence.
The invariant-submodule adapter constructs its actual inclusion and quotient
maps. The filtration theorem iterates actual short exact sequences; it assumes
no cohomological exactness, splitting, weight calculation or vanishing result.
Strict compilation and ownership-audit evidence are recorded separately.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CohomologyH1FiltrationBound

open CategoryTheory

variable {k G : Type u} [Field k] [Group G]

/-- Finite coefficients and a finite group give finite-dimensional actual H1. -/
theorem finiteDimensional_H1 [Finite G] (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (groupCohomology A 1) := by
  exact FiniteDimensional.of_surjective (groupCohomology.H1π A).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- The elementary dimension inequality for an exact pair of linear maps. -/
theorem finrank_middle_le (S : ShortComplex (ModuleCat.{u} k))
    [FiniteDimensional k S.X₁] [FiniteDimensional k S.X₂]
    [FiniteDimensional k S.X₃] (hS : S.Exact) :
    Module.finrank k S.X₂ ≤ Module.finrank k S.X₁ + Module.finrank k S.X₃ := by
  have hdim := S.g.hom.finrank_range_add_finrank_ker
  have hf := S.f.hom.finrank_range_le
  have hg := Submodule.finrank_le (LinearMap.range S.g.hom)
  rw [← hS.moduleCat_range_eq_ker] at hdim
  omega

/-- Subadditivity for an actual short exact sequence of representations. -/
theorem finrank_H1_le_of_shortExact [Finite G]
    (X : ShortComplex (Rep k G)) (hX : X.ShortExact)
    [FiniteDimensional k X.X₁] [FiniteDimensional k X.X₂]
    [FiniteDimensional k X.X₃] :
    Module.finrank k (groupCohomology X.X₂ 1) ≤
      Module.finrank k (groupCohomology X.X₁ 1) +
        Module.finrank k (groupCohomology X.X₃ 1) := by
  let : FiniteDimensional k (groupCohomology.mapShortComplex₂ X 1).X₁ :=
    finiteDimensional_H1 X.X₁
  let : FiniteDimensional k (groupCohomology.mapShortComplex₂ X 1).X₂ :=
    finiteDimensional_H1 X.X₂
  let : FiniteDimensional k (groupCohomology.mapShortComplex₂ X 1).X₃ :=
    finiteDimensional_H1 X.X₃
  exact finrank_middle_le (groupCohomology.mapShortComplex₂ X 1)
    (groupCohomology.mapShortComplex₂_exact hX 1)

section InvariantSubmodule

variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (W : Submodule k V)
variable (hW : ∀ g, W ≤ W.comap (ρ g))

/-- The actual inclusion of an invariant submodule. -/
def invariantInclusion : Rep.of (ρ.subrepresentation W hW) ⟶ Rep.of ρ :=
  Rep.ofHom ⟨W.subtype, by intro g; ext v; rfl⟩

/-- The actual quotient map by an invariant submodule. -/
def invariantQuotientMap : Rep.of ρ ⟶ Rep.of (ρ.quotient W hW) :=
  Rep.ofHom ⟨W.mkQ, by intro g; ext v; rfl⟩

/-- The actual invariant-submodule sequence. -/
def invariantComplex : ShortComplex (Rep k G) :=
  ShortComplex.mk (invariantInclusion ρ W hW) (invariantQuotientMap ρ W hW) (by
    ext v
    change W.mkQ (v : V) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr v.property)

/-- Exactness is derived from the actual submodule inclusion and quotient. -/
theorem invariantComplex_shortExact : (invariantComplex ρ W hW).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((invariantComplex ρ W hW).exact_map_iff_of_faithful
      (forget₂ (Rep k G) (ModuleCat k))).mp
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range W.subtype = LinearMap.ker W.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  · apply (Rep.mono_iff_injective _).mpr
    exact Subtype.val_injective
  · apply (Rep.epi_iff_surjective _).mpr
    exact W.mkQ_surjective

/-- H1 of an invariant extension is bounded by H1 of its actual two factors. -/
theorem finrank_H1_le_sub_add_quotient [Finite G] [FiniteDimensional k V] :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤
      Module.finrank k (groupCohomology (Rep.of (ρ.subrepresentation W hW)) 1) +
        Module.finrank k (groupCohomology (Rep.of (ρ.quotient W hW)) 1) := by
  let : FiniteDimensional k (invariantComplex ρ W hW).X₁ :=
    inferInstanceAs (FiniteDimensional k W)
  let : FiniteDimensional k (invariantComplex ρ W hW).X₂ :=
    inferInstanceAs (FiniteDimensional k V)
  let : FiniteDimensional k (invariantComplex ρ W hW).X₃ :=
    inferInstanceAs (FiniteDimensional k (V ⧸ W))
  exact finrank_H1_le_of_shortExact (invariantComplex ρ W hW)
    (invariantComplex_shortExact ρ W hW)

end InvariantSubmodule

/-- Iteration along a finite initial segment of an actual invariant filtration.
`A i` is the ith layer and `Q i` its actual next factor; their inclusion and
quotient maps form short exact sequences. No factor splitting is needed. -/
theorem finrank_H1_filtration [Finite G]
    (A Q : ℕ → Rep k G)
    [∀ i, FiniteDimensional k (A i)] [∀ i, FiniteDimensional k (Q i)]
    (f : ∀ i, A i ⟶ A (i + 1)) (g : ∀ i, A (i + 1) ⟶ Q i)
    (hfg : ∀ i, f i ≫ g i = 0)
    (n : ℕ) (hshort : ∀ i < n, (ShortComplex.mk (f i) (g i) (hfg i)).ShortExact) :
    Module.finrank k (groupCohomology (A n) 1) ≤
      Module.finrank k (groupCohomology (A 0) 1) +
        ∑ i ∈ Finset.range n, Module.finrank k (groupCohomology (Q i) 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun i hi => hshort i (Nat.lt_succ_of_lt hi))
    have hstep := finrank_H1_le_of_shortExact
      (ShortComplex.mk (f n) (g n) (hfg n)) (hshort n (Nat.lt_succ_self n))
    change Module.finrank k (groupCohomology (A (n + 1)) 1) ≤
      Module.finrank k (groupCohomology (A n) 1) +
        Module.finrank k (groupCohomology (Q n) 1) at hstep
    rw [Finset.sum_range_succ]
    omega

/-- A practical numerical bound from the H1 dimensions of the successive factors. -/
theorem finrank_H1_filtration_le [Finite G]
    (A Q : ℕ → Rep k G)
    [∀ i, FiniteDimensional k (A i)] [∀ i, FiniteDimensional k (Q i)]
    (f : ∀ i, A i ⟶ A (i + 1)) (g : ∀ i, A (i + 1) ⟶ Q i)
    (hfg : ∀ i, f i ≫ g i = 0)
    (n : ℕ) (hshort : ∀ i < n, (ShortComplex.mk (f i) (g i) (hfg i)).ShortExact)
    (hzero : Module.finrank k (groupCohomology (A 0) 1) = 0)
    (b : ℕ → ℕ) (hb : ∀ i < n, Module.finrank k (groupCohomology (Q i) 1) ≤ b i) :
    Module.finrank k (groupCohomology (A n) 1) ≤ ∑ i ∈ Finset.range n, b i := by
  have h := finrank_H1_filtration A Q f g hfg n hshort
  rw [hzero, zero_add] at h
  exact h.trans (Finset.sum_le_sum fun i hi => hb i (Finset.mem_range.mp hi))

end Kourovka2135.CohomologyH1FiltrationBound
