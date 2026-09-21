import Kourovka2135.BinaryTensorSLTwoRestriction
import Kourovka2135.BinaryAdditiveCohomologyDimension

/-! Actual subgroup and coefficient transport for tensor SL2 cohomology.

The root-subgroup comparison, its torus equivariance, and positive-degree
finite-dimensionality are constructed from ordinary cohomology functoriality
and the proved coordinate injection. This module does not use binary torus
fixed-space bounds.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryTensorSLTwoCohomology

open CategoryTheory BinaryTensorSLTwoRestriction BinaryAdditiveCohomology

/-- The additive parameter is genuinely isomorphic to the root subgroup. -/
def unipotentEquiv (F : Type u) [Field F] : Multiplicative F ≃* SLTwo.Unip F :=
  MonoidHom.ofInjective (SLTwo.uniHom_injective (K := F))

@[simp] theorem unipotentEquiv_apply {F : Type u} [Field F] (g : Multiplicative F) :
    (unipotentEquiv F g).val = SLTwo.uniHom F g := rfl

@[simp] theorem unipotentEquiv_symm_apply {F : Type u} [Field F] (g : SLTwo.Unip F) :
    SLTwo.uniHom F ((unipotentEquiv F).symm g) = g.val :=
  MonoidHom.apply_ofInjective_symm (SLTwo.uniHom_injective (K := F)) g

/-- An actual diagonal element, regarded as an element of the root normalizer. -/
def torusNormalizer {F : Type u} [Field F] (r : Fˣ) :
    Subgroup.normalizer (SLTwo.Unip F : Set (SLTwo.SL2 F)) :=
  ⟨SLTwo.tor r, SLTwo.torus_le_normalizer ⟨r, rfl⟩⟩

/-- The same element belongs to the entire torus used in the restriction bound. -/
def torusMember {F : Type u} [Field F] (r : Fˣ) : SLTwo.torusInNormalizer F :=
  ⟨torusNormalizer r, by
    change SLTwo.tor r ∈ SLTwo.Torus F
    exact ⟨r, rfl⟩⟩

/-- Inverse torus conjugation is precisely inverse squared-parameter scaling. -/
theorem normalizerInverse_parameter {F : Type u} [Field F] (r : Fˣ)
    (g : Multiplicative F) :
    GroupCohomology.normalizerInverseConjugation (SLTwo.Unip F) (torusNormalizer r)
        (unipotentEquiv F g) =
      unipotentEquiv F (BinaryAdditiveTorusAction.parameter r⁻¹ g) := by
  apply Subtype.ext
  change (SLTwo.tor r)⁻¹ * SLTwo.uni g.toAdd * SLTwo.tor r =
    SLTwo.uni (((r⁻¹ : Fˣ) : F) ^ 2 * g.toAdd)
  simpa only [SLTwo.tor_inv, inv_inv] using SLTwo.tor_conj_uni r⁻¹ g.toAdd

set_option backward.isDefEq.respectTransparency false in
/-- A commuting group-and-coefficient square induces the corresponding actual cohomology square. -/
theorem cohomology_map_square {K G H : Type u} [CommRing K] [Group G] [Group H]
    {A : Rep K G} {B : Rep K H} (e : H →* G) (c : Rep.res e A ⟶ B)
    (s : G →* G) (ψ : Rep.res s A ⟶ A) (t : H →* H) (φ : Rep.res t B ⟶ B)
    (hgroup : s.comp e = e.comp t)
    (hcoeff : ∀ v : A, c.hom (ψ.hom v) = φ.hom (c.hom v)) (n : ℕ) :
    groupCohomology.map s ψ n ≫ groupCohomology.map e c n =
      groupCohomology.map e c n ≫ groupCohomology.map t φ n := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr hgroup
  apply LinearMap.ext
  exact hcoeff

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- The coefficient morphism accompanying pullback from the actual subgroup. -/
def unipotentCoefficient :
    Rep.res (unipotentEquiv F).toMonoidHom
        (Rep.res (SLTwo.Unip F).subtype (ambient k I σ)) ⟶
      coefficientRepresentation k I σ hcard :=
  (coefficientIso k I σ hcard).hom

/-- Genuine ordinary cohomology transport from the root subgroup to its parameter group. -/
def cohomologyIso (n : ℕ) :
    groupCohomology (Rep.res (SLTwo.Unip F).subtype (ambient k I σ)) n ≅
      groupCohomology (coefficientRepresentation k I σ hcard) n := by
  refine groupCohomology.mapIso (unipotentEquiv F).symm
    (coefficientLinearEquiv k I σ hcard).symm ?_ n
  intro g
  apply LinearMap.ext
  intro v
  change (coefficientLinearEquiv k I σ hcard).symm
      (BinaryTensorSLTwo.representation k σ I g.val v) =
    (coefficientRepresentation k I σ hcard).ρ ((unipotentEquiv F).symm g)
      ((coefficientLinearEquiv k I σ hcard).symm v)
  have h := coefficientLinearEquiv_symm_action k I σ hcard
    ((unipotentEquiv F).symm g) v
  simpa only [unipotentEquiv_symm_apply] using h

/-- The comparison homomorphism is actual functorial pullback, with its coefficient map. -/
theorem cohomologyIso_hom (n : ℕ) :
    (cohomologyIso k I σ hcard n).hom =
      groupCohomology.map (unipotentEquiv F).toMonoidHom
        (unipotentCoefficient k I σ hcard) n := by
  apply groupCohomology.map_congr rfl
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
/-- The actual subgroup normalizer action becomes the actual additive cohomology map. -/
theorem cohomologyIso_normalizer (r : Fˣ) (n : ℕ)
    (v : groupCohomology (Rep.res (SLTwo.Unip F).subtype (ambient k I σ)) n) :
    (cohomologyIso k I σ hcard n).hom.hom
        (GroupCohomology.normalizerConjugation (SLTwo.Unip F) (ambient k I σ)
          (torusNormalizer r) n v) =
      (BinaryAdditiveTorusAction.cohomologyMap k I σ hcard r n).hom
        ((cohomologyIso k I σ hcard n).hom.hom v) := by
  have h :
      groupCohomology.map
          (GroupCohomology.normalizerInverseConjugation (SLTwo.Unip F) (torusNormalizer r))
          (GroupCohomology.conjugationCoefficient (ambient k I σ) (SLTwo.Unip F).subtype
            (GroupCohomology.normalizerInverseConjugation (SLTwo.Unip F) (torusNormalizer r))
            (SLTwo.tor r) (fun _ => rfl)) n ≫ (cohomologyIso k I σ hcard n).hom =
        (cohomologyIso k I σ hcard n).hom ≫
          BinaryAdditiveTorusAction.cohomologyMap k I σ hcard r n := by
    rw [cohomologyIso_hom]
    apply cohomology_map_square
    · apply MonoidHom.ext
      intro g
      exact normalizerInverse_parameter r g
    · intro x
      change (coefficientIso k I σ hcard).hom.hom ((ambient k I σ).ρ (SLTwo.tor r) x) =
        BinaryAdditiveTorusAction.coefficientLinear k I σ hcard r
          ((coefficientIso k I σ hcard).hom.hom x)
      exact coefficientIso_torus k I σ hcard r x
  exact congrArg (fun p => p.hom v) h

include hcard in
/-- Finite-dimensionality of subgroup cohomology comes from its concrete coordinate injection. -/
theorem finiteDimensional_unipotent (n : ℕ) :
    FiniteDimensional k
      (groupCohomology (Rep.res (SLTwo.Unip F).subtype (ambient k I σ)) (n + 1)) := by
  have := BinaryAdditiveCohomologyDimension.finiteDimensional_groupCohomology k I σ hcard n
  exact FiniteDimensional.of_injective (cohomologyIso k I σ hcard (n + 1)).hom.hom
    (cohomologyIso k I σ hcard (n + 1)).toLinearEquiv.injective

include hcard in
/-- Odd-index restriction also proves finite-dimensionality of actual positive SL2 cohomology. -/
theorem finiteDimensional_ambient (n : ℕ) :
    FiniteDimensional k (groupCohomology (ambient k I σ) (n + 1)) := by
  have : CharP F 2 := (σ.charP_iff_charP 2).mpr inferInstance
  have := finiteDimensional_unipotent k I σ hcard n
  exact FiniteDimensional.of_injective
    (groupCohomology.map (SLTwo.Unip F).subtype (𝟙 (Rep.res (SLTwo.Unip F).subtype
      (ambient k I σ))) (n + 1)).hom
    (GroupCohomology.restriction_injective_of_odd_index (SLTwo.Unip F) (ambient k I σ)
      (n + 1) SLTwo.odd_index_unip)

/-- Whole-torus fixed classes inject into the fixed space of any chosen torus element. -/
def fixedToKernel (r : Fˣ) (n : ℕ) :
    GroupCohomology.normalizerFixedSubmodule (SLTwo.Unip F) (ambient k I σ)
        (SLTwo.torusInNormalizer F) n →ₗ[k]
      ((BinaryAdditiveTorusAction.cohomologyMap k I σ hcard r n).hom - LinearMap.id).ker :=
  (((cohomologyIso k I σ hcard n).hom.hom).comp
    (GroupCohomology.normalizerFixedSubmodule (SLTwo.Unip F) (ambient k I σ)
      (SLTwo.torusInNormalizer F) n).subtype).codRestrict _ (by
        intro v
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        change (BinaryAdditiveTorusAction.cohomologyMap k I σ hcard r n).hom
            ((cohomologyIso k I σ hcard n).hom.hom v.val) =
          (cohomologyIso k I σ hcard n).hom.hom v.val
        rw [← cohomologyIso_normalizer]
        exact congrArg ((cohomologyIso k I σ hcard n).hom.hom) (v.property (torusMember r)))

theorem fixedToKernel_injective (r : Fˣ) (n : ℕ) :
    Function.Injective (fixedToKernel k I σ hcard r n) := by
  intro x y h
  apply Subtype.ext
  apply (cohomologyIso k I σ hcard n).toLinearEquiv.injective
  exact congrArg Subtype.val h

/-- Odd-index restriction followed by the constructed comparison bounds actual SL2 cohomology. -/
theorem finrank_le_fixed (r : Fˣ) (n : ℕ) (hn : n + 1 = 1 ∨ n + 1 = 2) :
    Module.finrank k (groupCohomology (ambient k I σ) (n + 1)) ≤
      Module.finrank k
        ((BinaryAdditiveTorusAction.cohomologyMap k I σ hcard r (n + 1)).hom - LinearMap.id).ker := by
  have : CharP F 2 := (σ.charP_iff_charP 2).mpr inferInstance
  have := finiteDimensional_unipotent k I σ hcard n
  have := BinaryAdditiveCohomologyDimension.finiteDimensional_groupCohomology k I σ hcard n
  calc
    _ ≤ Module.finrank k (GroupCohomology.normalizerFixedSubmodule (SLTwo.Unip F)
        (ambient k I σ) (SLTwo.torusInNormalizer F) (n + 1)) :=
      SLTwo.finrank_le_torusFixed_of_charTwo (ambient k I σ) (n + 1) hn
    _ ≤ _ := LinearMap.finrank_le_finrank_of_injective (fixedToKernel_injective k I σ hcard r (n + 1))

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
/-- The original tensor-space representation has the same actual ordinary cohomology. -/
def tensorCohomologyIso (n : ℕ) :
    groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ I)) n ≅
      groupCohomology (ambient k I σ) n := by
  refine groupCohomology.mapIso (MulEquiv.refl (SLTwo.SL2 F))
    (BinaryTensorSLTwo.tensorEquiv k I) ?_ n
  intro g
  apply LinearMap.ext
  intro v
  change BinaryTensorSLTwo.tensorEquiv k I
      (BinaryTensorSLTwo.tensorRepresentation k σ I g v) =
    BinaryTensorSLTwo.representation k σ I g (BinaryTensorSLTwo.tensorEquiv k I v)
  exact (BinaryTensorSLTwo.representation_tensorEquiv k σ I g v).symm

include hcard in
/-- Finite-dimensionality also holds on the original tensor-space presentation. -/
theorem finiteDimensional_tensor (n : ℕ) :
    FiniteDimensional k
      (groupCohomology (Rep.of (BinaryTensorSLTwo.tensorRepresentation k σ I)) (n + 1)) := by
  have := finiteDimensional_ambient k I σ hcard n
  exact FiniteDimensional.of_injective (tensorCohomologyIso k I σ (n + 1)).hom.hom
    (tensorCohomologyIso k I σ (n + 1)).toLinearEquiv.injective

end Kourovka2135.BinaryTensorSLTwoCohomology
