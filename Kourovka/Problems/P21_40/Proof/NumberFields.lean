import Kourovka.Problems.P21_40.Statement
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Quot

/-!
# Restriction of scalars to the rationals

A subgroup of a general linear group over a number field embeds in a rational
matrix group. Isomorphic groups have the same finiteness property for their
full abstract automorphism orbits. Thus the rational structural theorem implies
a torsion-free virtually nilpotent conclusion over every number field.

The rational theorem is an explicit parameter here to avoid an import cycle;
the public solution discharges that parameter with its proved rational theorem.
-/

namespace Kourovka.P21_40

/-- Finiteness of full abstract automorphism orbits is invariant under group isomorphism. -/
theorem hasFiniteAutomorphismOrbits_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : HasFiniteAutomorphismOrbits G) : HasFiniteAutomorphismOrbits H := by
  let : Finite (MulAction.orbitRel.Quotient (MulAut G) G) := hG
  have he : ∀ ⦃a b : G⦄, MulAction.orbitRel (MulAut G) G a b →
      MulAction.orbitRel (MulAut H) H (e a) (e b) := by
    rintro a b ⟨α, hα⟩
    refine ⟨MulAut.congr e α, ?_⟩
    change e (α (e.symm (e b))) = e a
    change α b = a at hα
    rw [e.symm_apply_apply, hα]
  exact Finite.of_surjective (Quotient.map e he)
    (Quotient.map_surjective he e.surjective)

/-- Restriction of scalars extends the rational structural conclusion to every number field. -/
theorem numberField_structure_of_rational_structure
    (hq : ∀ (m : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℚ)),
      HasFiniteAutomorphismOrbits H → StructuralConclusion H)
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hG : HasFiniteAutomorphismOrbits G) :
    ∃ N : Subgroup G, N.FiniteIndex ∧ Group.IsNilpotent N ∧
      (∀ g : N, IsOfFinOrder g → g = 1) := by
  let V := Fin n → K
  let r : Module.End K V →+* Module.End ℚ V :=
    { toFun := LinearMap.restrictScalars ℚ
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have hr : Function.Injective (Units.map r.toMonoidHom) := by
    intro x y hxy
    apply Units.ext
    exact LinearMap.restrictScalars_injective ℚ (congrArg Units.val hxy)
  let b := Module.finBasis ℚ V
  let e₁ : Matrix.GeneralLinearGroup (Fin n) K ≃* LinearMap.GeneralLinearGroup K V :=
    Matrix.GeneralLinearGroup.toLin
  let e₂ := (Matrix.GeneralLinearGroup.toLin' b).symm
  let f := e₂.toMonoidHom.comp ((Units.map r.toMonoidHom).comp e₁.toMonoidHom)
  have hf : Function.Injective f := e₂.injective.comp (hr.comp e₁.injective)
  let fG := f.comp G.subtype
  have hfG : Function.Injective fG := hf.comp G.subtype_injective
  let H := fG.range
  let e : G ≃* H := MonoidHom.ofInjective hfG
  have hH : HasFiniteAutomorphismOrbits H :=
    hasFiniteAutomorphismOrbits_of_mulEquiv e hG
  obtain ⟨N, _, hNfin, _, hNnil, _, hNtor, _⟩ := hq _ H hH
  let M := N.map e.symm.toMonoidHom
  let eN : N ≃* M := e.symm.subgroupMap N
  have hMfin : M.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    change (N.map e.symm.toMonoidHom).index ≠ 0
    rw [Subgroup.index_map_of_bijective (f := e.symm.toMonoidHom) e.symm.bijective N]
    exact hNfin.index_ne_zero
  let : Group.IsNilpotent N := hNnil
  refine ⟨M, hMfin, Group.nilpotent_of_mulEquiv eN, ?_⟩
  intro g hg
  apply eN.symm.injective
  rw [map_one]
  exact hNtor (eN.symm g) (eN.symm.toMonoidHom.isOfFinOrder hg)

/-- Virtual nilpotence over number fields, as a projection of the stronger conclusion. -/
theorem numberField_virtuallyNilpotent_of_rational_structure
    (hq : ∀ (m : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℚ)),
      HasFiniteAutomorphismOrbits H → StructuralConclusion H)
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hG : HasFiniteAutomorphismOrbits G) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨N, hfin, hnil, _⟩ := numberField_structure_of_rational_structure hq n G hG
  exact ⟨N, hnil, hfin⟩

end Kourovka.P21_40
