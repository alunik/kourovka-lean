import Kourovka2135.BilinearRestrictionRank

/-! Rank loss under an injective linear change to a smaller domain. -/
set_option autoImplicit false
namespace Kourovka2135
variable {k V U Z : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup U] [Module k U] [FiniteDimensional k U]
variable [AddCommGroup Z] [Module k Z]

theorem linearMap_finrank_range_add_domain_le_of_injective
    (f : V →ₗ[k] Z) (i : U →ₗ[k] V) (hi : Function.Injective i) :
    Module.finrank k f.range + Module.finrank k U ≤
      Module.finrank k (f.comp i).range + Module.finrank k V := by
  let j : (f.comp i).ker →ₗ[k] f.ker := {
    toFun x := ⟨i x, x.property⟩
    map_add' := fun x y => Subtype.ext (map_add i (x : U) (y : U))
    map_smul' := fun a x => Subtype.ext (map_smul i a (x : U)) }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg (fun z : f.ker => (z : V)) h
  have hker := LinearMap.finrank_le_finrank_of_injective hj
  have hf := f.finrank_range_add_finrank_ker
  have hfi := (f.comp i).finrank_range_add_finrank_ker
  omega

theorem bilinear_finrank_range_le_embedding_add_twice_codim
    (B : V →ₗ[k] V →ₗ[k] k) (i : U →ₗ[k] V) (hi : Function.Injective i) :
    Module.finrank k B.range ≤ Module.finrank k (B.compl₁₂ i i).range +
      2 * (Module.finrank k V - Module.finrank k U) := by
  have hpre : Module.finrank k B.range + Module.finrank k U ≤
      Module.finrank k (B.comp i).range + Module.finrank k V :=
    linearMap_finrank_range_add_domain_le_of_injective B i hi
  have hpost : Module.finrank k (B.comp i).range ≤
      Module.finrank k (B.compl₁₂ i i).range + Module.finrank k i.dualMap.ker := by
    have hh := linearMap_finrank_range_le_comp_add_ker (B.comp i) i.dualMap
    have heq : i.dualMap.comp (B.comp i) = B.compl₁₂ i i := rfl
    rwa [heq] at hh
  have hdual := i.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective hi),
    finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at hdual
  have hiDim := LinearMap.finrank_le_finrank_of_injective hi
  omega

theorem bilinear_embedding_finrank_ge_twice
    (B : V →ₗ[k] V →ₗ[k] k) (i : U →ₗ[k] V) (hi : Function.Injective i) (d : ℕ)
    (hrank : 2 * d + 2 * (Module.finrank k V - Module.finrank k U) ≤
      Module.finrank k B.range) :
    2 * d ≤ Module.finrank k (B.compl₁₂ i i).range := by
  have h := bilinear_finrank_range_le_embedding_add_twice_codim B i hi
  omega

end Kourovka2135
