import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Restricting a bilinear form to a subspace loses at most twice the
codimension in rank. No symmetry assumption is needed. -/
set_option autoImplicit false
universe u v w t
namespace Kourovka2135
variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {U : Type w} [AddCommGroup U] [Module k U]
variable {Z : Type t} [AddCommGroup Z] [Module k Z]

/-- Restriction of a linear map to a subspace loses at most its codimension. -/
theorem linearMap_finrank_range_add_subspace_le [FiniteDimensional k V]
    (f : V →ₗ[k] U) (W : Submodule k V) :
    Module.finrank k f.range + Module.finrank k W ≤
      Module.finrank k (f.comp W.subtype).range + Module.finrank k V := by
  let j : (f.comp W.subtype).ker →ₗ[k] f.ker := {
    toFun x := ⟨(x.1 : V), x.2⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : V)) h
  have hker := LinearMap.finrank_le_finrank_of_injective hj
  have hfull := f.finrank_range_add_finrank_ker
  have hres := (f.comp W.subtype).finrank_range_add_finrank_ker
  omega

/-- Postcomposition loses no more rank than the dimension of the second map's kernel. -/
theorem linearMap_finrank_range_le_comp_add_ker [FiniteDimensional k V]
    (f : U →ₗ[k] V) (g : V →ₗ[k] Z) :
    Module.finrank k f.range ≤
      Module.finrank k (g.comp f).range + Module.finrank k g.ker := by
  have h := linearMap_finrank_range_add_subspace_le g f.range
  have heq : (g.comp f.range.subtype).range = (g.comp f).range := by
    simp only [LinearMap.range_comp, Submodule.range_subtype]
  rw [heq] at h
  have hg := g.finrank_range_add_finrank_ker
  omega

/-- Additive form of the bilinear restriction rank bound. -/
theorem bilinear_finrank_range_add_twice_subspace_le [FiniteDimensional k V]
    (B : V →ₗ[k] V →ₗ[k] k) (W : Submodule k V) :
    Module.finrank k B.range + 2 * Module.finrank k W ≤
      Module.finrank k (B.compl₁₂ W.subtype W.subtype).range + 2 * Module.finrank k V := by
  have hpre : Module.finrank k B.range + Module.finrank k W ≤
      Module.finrank k (B.comp W.subtype).range + Module.finrank k V :=
    linearMap_finrank_range_add_subspace_le B W
  have hpost : Module.finrank k (B.comp W.subtype).range ≤
      Module.finrank k (B.compl₁₂ W.subtype W.subtype).range +
        Module.finrank k W.dualAnnihilator := by
    have hh := linearMap_finrank_range_le_comp_add_ker
      (B.comp W.subtype) W.dualRestrict
    have heq : W.dualRestrict.comp (B.comp W.subtype) = B.compl₁₂ W.subtype W.subtype := rfl
    rwa [heq, W.dualRestrict_ker_eq_dualAnnihilator] at hh
  have hann : Module.finrank k W + Module.finrank k W.dualAnnihilator =
      Module.finrank k V := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

/-- Restricting both arguments loses at most twice the subspace codimension. -/
theorem bilinear_finrank_range_le_restrict_add_twice_codim [FiniteDimensional k V]
    (B : V →ₗ[k] V →ₗ[k] k) (W : Submodule k V) :
    Module.finrank k B.range ≤
      Module.finrank k (B.compl₁₂ W.subtype W.subtype).range +
        2 * (Module.finrank k V - Module.finrank k W) := by
  have h := bilinear_finrank_range_add_twice_subspace_le B W
  have hW := W.finrank_le
  omega

/-- A rank threshold with the codimension loss included survives restriction. -/
theorem bilinear_restrict_finrank_ge_twice [FiniteDimensional k V]
    (B : V →ₗ[k] V →ₗ[k] k) (W : Submodule k V) (d : ℕ)
    (h : 2 * d + 2 * (Module.finrank k V - Module.finrank k W) ≤
      Module.finrank k B.range) :
    2 * d ≤ Module.finrank k (B.compl₁₂ W.subtype W.subtype).range := by
  have hr := bilinear_finrank_range_le_restrict_add_twice_codim B W
  omega

end Kourovka2135
