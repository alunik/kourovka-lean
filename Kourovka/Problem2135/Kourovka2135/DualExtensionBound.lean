import Kourovka2135.CohomologyCenterBound
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The actual dual short exact sequence of a module with a pointwise fixed
submodule, and the resulting bound on that submodule's dimension. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open CategoryTheory
variable {k G M : Type u} [Field k] [Group G] [AddCommGroup M] [Module k M]

theorem fixedSubmoduleInvariant (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) : ∀ g, W ≤ W.comap (ρ g) := by
  intro g x hx
  change ρ g x ∈ W
  rw [hW g x hx]
  exact hx

noncomputable def dualExtensionInclusion
    (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) :
    Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W hW)).dual ⟶ Rep.of ρ.dual :=
  Rep.ofHom ⟨W.mkQ.dualMap, by
    intro g
    ext ell x
    rfl⟩

noncomputable def dualExtensionRestriction
    (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) :
    Rep.of ρ.dual ⟶ Rep.trivial k G (Module.Dual k W) :=
  Rep.ofHom ⟨W.dualRestrict, by
    intro g
    ext ell x
    change ell (ρ g⁻¹ (x : M)) = ell x
    rw [hW g⁻¹ x x.property]⟩

noncomputable def dualExtensionComplex
    (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) : ShortComplex (Rep k G) :=
  ShortComplex.mk (dualExtensionInclusion ρ W hW) (dualExtensionRestriction ρ W hW) (by
    ext ell x
    change ell (W.mkQ (x : M)) = 0
    have hx : W.mkQ (x : M) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr x.property
    rw [hx, map_zero])

theorem dualExtensionComplex_shortExact
    (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) :
    (dualExtensionComplex ρ W hW).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((dualExtensionComplex ρ W hW).exact_map_iff_of_faithful
      (forget₂ (Rep k G) (ModuleCat k))).mp
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range W.mkQ.dualMap = LinearMap.ker W.dualRestrict
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.ker_mkQ,
      Submodule.dualRestrict_ker_eq_dualAnnihilator]
  · apply (Rep.mono_iff_injective _).mpr
    exact LinearMap.dualMap_injective_of_surjective W.mkQ_surjective
  · apply (Rep.epi_iff_surjective _).mpr
    exact Subspace.dualRestrict_surjective

theorem fixed_submodule_finrank_le_h1_dual_quotient
    (ρ : Representation k G M) (W : Submodule k M)
    (hW : ∀ g x, x ∈ W → ρ g x = x) (hρ : ρ.dual.invariants = ⊥)
    [FiniteDimensional k W]
    [FiniteDimensional k (groupCohomology
      (Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W hW)).dual) 1)] :
    Module.finrank k W ≤ Module.finrank k (groupCohomology
      (Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W hW)).dual) 1) := by
  let : (dualExtensionComplex ρ W hW).X₃.ρ.IsTrivial :=
    inferInstanceAs (Representation.IsTrivial (Representation.trivial k G (Module.Dual k W)))
  let : FiniteDimensional k (groupCohomology (dualExtensionComplex ρ W hW).X₁ 1) :=
    inferInstanceAs (FiniteDimensional k (groupCohomology
      (Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W hW)).dual) 1))
  have hh := GroupCohomology.trivial_quotient_finrank_le_h1
    (dualExtensionComplex_shortExact ρ W hW) hρ
  change Module.finrank k (Module.Dual k W) ≤ Module.finrank k (groupCohomology
    (Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W hW)).dual) 1) at hh
  simpa only [Subspace.dual_finrank_eq] using hh

end Kourovka2135
