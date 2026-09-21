import Kourovka2135.BinaryExteriorScaling
import Kourovka2135.BinaryAdditiveResolution
import Kourovka2135.ResolutionConjugation
import Kourovka2135.BinaryAdditiveTorusAction

/-! Actual diagonal semilinear maps on the binary exterior resolution.

The exponent weight and algebra automorphism are both constructed. Their
compatibility with lowering proves the chain-map equation; no differential
or augmentation compatibility is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Kourovka2135.BinaryResolutionScaling
open CategoryTheory BinaryExteriorAlgebra BinaryExteriorScaling
open BinaryExteriorAugmentation PeriodicResolution
open scoped IsMulCommutative ModuleCat.Algebra

/-- Bundle a map whose source and target each have their own native coordinates. -/
def coordinateMorphism {K G W : Type*} [CommRing K] [Group G]
    [AddCommGroup W] [Module K W] (A B : Rep K G)
    (eA : A ≃ₗ[K] W) (eB : B ≃ₗ[K] W) (T : Module.End K W)
    (hT : ∀ g v, eB.symm (T (eA (A.ρ g v))) = B.ρ g (eB.symm (T (eA v)))) :
    A ⟶ B :=
  Rep.ofHom { toLinearMap := (eB.symm.toLinearMap ∘ₗ T ∘ₗ eA.toLinearMap)
              isIntertwining' := fun g => LinearMap.ext (hT g) }

/-- Evaluation uses the exact target representation, without a restriction-carrier cast. -/
theorem coordinateMorphism_apply {K G W : Type*} [CommRing K] [Group G]
    [AddCommGroup W] [Module K W] (A B : Rep K G)
    (eA : A ≃ₗ[K] W) (eB : B ≃ₗ[K] W) (T : Module.End K W)
    (hT : ∀ g v, eB.symm (T (eA (A.ρ g v))) = B.ρ g (eB.symm (T (eA v)))) (v : A) :
    eB ((coordinateMorphism A B eA eB T hT).hom v) = T (eA v) :=
  eB.apply_symm_apply _

section Generic
variable (k : Type u) [CommRing k] (f : ℕ)

/-- The product of the actual diagonal generator weights with their exponents. -/
def exponentWeight (c : Fin f → kˣ) (a : Fin f →₀ ℕ) : kˣ :=
  ∏ i : Fin f, c i ^ a i

@[simp] theorem exponentWeight_zero (c : Fin f → kˣ) :
    exponentWeight k f c 0 = 1 := by simp [exponentWeight]

theorem exponentWeight_add (c : Fin f → kˣ) (a b : Fin f →₀ ℕ) :
    exponentWeight k f c (a + b) = exponentWeight k f c a * exponentWeight k f c b := by
  simp only [exponentWeight, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

@[simp] theorem exponentWeight_single_one (c : Fin f → kˣ) (i : Fin f) :
    exponentWeight k f c (Finsupp.single i 1) = c i := by
  classical
  simp [exponentWeight, Finsupp.single_apply]

/-- Lowering an active exponent removes precisely one copy of its weight. -/
theorem exponentWeight_lower (c : Fin f → kˣ) {n : ℕ}
    (a : DegreeIndex (Fin f) (n + 1)) (i : Fin f) (hi : a.val i ≠ 0) :
    exponentWeight k f c (lowerIndex i a hi).val * c i = exponentWeight k f c a.val := by
  have h := exponentWeight_add k f c (a.val - Finsupp.single i 1) (Finsupp.single i 1)
  rw [Finsupp.sub_add_single_one_cancel hi, exponentWeight_single_one] at h
  exact h.symm

variable [CharP k 2]

/-- Actual scaling of a degree module, linear over the ground ring. -/
def degreeScale (c : Fin f → kˣ) (n : ℕ) :
    DegreeSpace (Fin f) (Carrier k f) n →ₗ[k] DegreeSpace (Fin f) (Carrier k f) n :=
  Finsupp.lsum k fun a =>
    (Finsupp.lsingle a).comp
      ((exponentWeight k f c a.val : k) • (scale k f c).toLinearMap)

@[simp] theorem degreeScale_single (c : Fin f → kˣ) (n : ℕ)
    (a : DegreeIndex (Fin f) n) (v : Carrier k f) :
    degreeScale k f c n (Finsupp.single a v) =
      Finsupp.single a ((exponentWeight k f c a.val : k) • scale k f c v) := by
  simp only [degreeScale, Finsupp.lsum_single, LinearMap.comp_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply, AlgEquiv.toLinearMap_apply]

/-- The unit basis column exposes the exact factor used in the induced Hom action. -/
theorem degreeScale_single_one (c : Fin f → kˣ) (n : ℕ)
    (a : DegreeIndex (Fin f) n) :
    degreeScale k f c n (Finsupp.single a 1) =
      (exponentWeight k f c a.val : k) • Finsupp.single a 1 := by
  rw [degreeScale_single, map_one, Finsupp.smul_single]

/-- The map is semilinear over the actual exterior-algebra automorphism. -/
theorem degreeScale_smul (c : Fin f → kˣ) (n : ℕ) (b : Carrier k f)
    (v : DegreeSpace (Fin f) (Carrier k f) n) :
    degreeScale k f c n (b • v) = scale k f c b • degreeScale k f c n v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  | single a v =>
      simp only [Finsupp.smul_single, degreeScale_single, smul_eq_mul, map_mul]
      congr 1
      exact (mul_smul_comm _ _ _).symm

/-- The lowering column commutes with scaling, including its inactive case. -/
theorem degreeScale_gradedLower (c : Fin f → kˣ) (n : ℕ) (i : Fin f)
    (v : DegreeSpace (Fin f) (Carrier k f) (n + 1)) :
    degreeScale k f c n (gradedLower (generator k f) i n v) =
      gradedLower (generator k f) i n (degreeScale k f c (n + 1) v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single a v =>
      by_cases hi : a.val i = 0
      · simp [gradedLower_single, hi]
      · have hw := congrArg (fun z : kˣ => (z : k)) (exponentWeight_lower k f c a i hi)
        simp only [Units.val_mul] at hw
        simp only [gradedLower_single, hi, dite_false, degreeScale_single,
          map_mul, scale_generator]
        congr 1
        rw [mul_smul_comm, smul_smul, hw, smul_mul_assoc]

/-- Compatibility with the actual sum of all lowering columns. -/
theorem degreeScale_gradedDifferential (c : Fin f → kˣ) (n : ℕ)
    (v : DegreeSpace (Fin f) (Carrier k f) (n + 1)) :
    degreeScale k f c n (gradedDifferential (generator k f) Finset.univ n v) =
      gradedDifferential (generator k f) Finset.univ n (degreeScale k f c (n + 1) v) := by
  simp only [gradedDifferential, LinearMap.sum_apply, map_sum, degreeScale_gradedLower]

/-- The algebra scaling preserves the actual residue map. -/
theorem augmentation_scale (c : Fin f → kˣ) (v : Carrier k f) :
    augmentation k f (scale k f c v) = augmentation k f v := by
  have h : (augmentation k f).comp (scale k f c).toAlgHom = augmentation k f := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro w
    simp [augmentation, scale_apply_ι, ExteriorAlgebra.lift_ι_apply]
  exact congrArg (fun h : Carrier k f →ₐ[k] k => h v) h

/-- Degree-zero scaling preserves the actual augmentation of the resolution. -/
theorem augmentation_degreeScale (c : Fin f → kˣ)
    (v : DegreeSpace (Fin f) (Carrier k f) 0) :
    (BinaryExteriorResolution.augmentationMap k f).hom (degreeScale k f c 0 v) =
      (BinaryExteriorResolution.augmentationMap k f).hom v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single a v =>
      have ha : a.val = 0 := (Finsupp.degree_eq_zero_iff a.val).mp a.property
      simp only [degreeScale_single, ha, exponentWeight_zero, Units.val_one, one_smul]
      have had : a = default := Subsingleton.elim _ _
      subst a
      change augmentation k f ((Finsupp.single default (scale k f c v)) default) =
        augmentation k f ((Finsupp.single default v) default)
      simpa only [Finsupp.single_eq_same] using augmentation_scale k f c v

end Generic

section Representation
open BinaryAdditiveResolution
variable (k : Type u) [Field k] [CharP k 2] (f : ℕ)
variable {F : Type u} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

/-- Transport changes the scalar-action presentation, but not the degree vectors. -/
def degreeLinearEquiv (n : ℕ) :
    (projectiveResolution k f σ hcard).complex.X n ≃ₗ[k]
      DegreeSpace (Fin f) (Carrier k f) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r v := by
    change (monoidEquivalence k f σ hcard
      (algebraMap k (MonoidAlgebra k (Multiplicative F)) r)) •
        (show DegreeSpace (Fin f) (Carrier k f) n from v) =
      r • (show DegreeSpace (Fin f) (Carrier k f) n from v)
    rw [(monoidEquivalence k f σ hcard).commutes]
    exact algebraMap_smul (Carrier k f) r
      (show DegreeSpace (Fin f) (Carrier k f) n from v)

/-- Native coordinates for the exact restricted target degree. -/
def restrictedDegreeLinearEquiv (r : Fˣ) (n : ℕ) :
    Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X n) ≃ₗ[k]
      DegreeSpace (Fin f) (Carrier k f) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a v := by
    change (monoidEquivalence k f σ hcard
      (algebraMap k (MonoidAlgebra k (Multiplicative F)) a)) •
        (show DegreeSpace (Fin f) (Carrier k f) n from v) =
      a • (show DegreeSpace (Fin f) (Carrier k f) n from v)
    rw [(monoidEquivalence k f σ hcard).commutes]
    exact algebraMap_smul (Carrier k f) a
      (show DegreeSpace (Fin f) (Carrier k f) n from v)

/-- The group action on every transported free term is multiplication by the actual character. -/
theorem degree_action (n : ℕ) (g : Multiplicative F)
    (v : (projectiveResolution k f σ hcard).complex.X n) :
    degreeLinearEquiv k f σ hcard n
        (((projectiveResolution k f σ hcard).complex.X n).ρ g v) =
      BinaryExteriorCharacter.character k f (σ g.toAdd) • degreeLinearEquiv k f σ hcard n v := by
  change (monoidEquivalence k f σ hcard (MonoidAlgebra.single g 1)) •
      (show DegreeSpace (Fin f) (Carrier k f) n from v) = _
  simp only [monoidEquivalence_single, one_smul]
  rfl

/-- The transported differential retains the actual lowering formula. -/
theorem degree_differential (n : ℕ)
    (v : (projectiveResolution k f σ hcard).complex.X (n + 1)) :
    degreeLinearEquiv k f σ hcard n
        (((projectiveResolution k f σ hcard).complex.d (n + 1) n).hom v) =
      gradedDifferential (generator k f) Finset.univ n
        (degreeLinearEquiv k f σ hcard (n + 1) v) := by
  change ((BinaryExteriorResolution.complex k f).d (n + 1) n).hom
      (show DegreeSpace (Fin f) (Carrier k f) (n + 1) from v) = _
  rw [BinaryExteriorResolution.complex_d]
  rfl

/-- The transported augmentation is the same concrete residue map. -/
theorem degree_augmentation
    (v : (projectiveResolution k f σ hcard).complex.X 0) :
    ((projectiveResolution k f σ hcard).π.f 0).hom v =
      (BinaryExteriorResolution.augmentationMap k f).hom
        (degreeLinearEquiv k f σ hcard 0 v) := by
  rfl

/-- The restricted action in its own native coordinates. -/
theorem restricted_degree_action (r : Fˣ) (n : ℕ) (g : Multiplicative F)
    (v : Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X n)) :
    restrictedDegreeLinearEquiv k f σ hcard r n
      ((Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
        ((projectiveResolution k f σ hcard).complex.X n)).ρ g v) =
      BinaryExteriorCharacter.character k f
        (σ (BinaryAdditiveTorusAction.parameter r g).toAdd) •
          restrictedDegreeLinearEquiv k f σ hcard r n v := by
  change (monoidEquivalence k f σ hcard
      (MonoidAlgebra.single (BinaryAdditiveTorusAction.parameter r g) 1)) •
      (show DegreeSpace (Fin f) (Carrier k f) n from v) = _
  simp only [monoidEquivalence_single, one_smul]
  rfl

/-- The restricted differential in exact target coordinates. -/
theorem restricted_degree_differential (r : Fˣ) (n : ℕ)
    (v : Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X (n + 1))) :
    restrictedDegreeLinearEquiv k f σ hcard r n
      (((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).map
        ((projectiveResolution k f σ hcard).complex.d (n + 1) n)).hom v) =
      gradedDifferential (generator k f) Finset.univ n
        (restrictedDegreeLinearEquiv k f σ hcard r (n + 1) v) := by
  change ((BinaryExteriorResolution.complex k f).d (n + 1) n).hom
      (show DegreeSpace (Fin f) (Carrier k f) (n + 1) from v) = _
  rw [BinaryExteriorResolution.complex_d]
  rfl

/-- The restricted augmentation in exact target coordinates. -/
theorem restricted_degree_augmentation (r : Fˣ)
    (v : Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X 0)) :
    (((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).map
      ((projectiveResolution k f σ hcard).π.f 0)).hom v) =
      (BinaryExteriorResolution.augmentationMap k f).hom
        (restrictedDegreeLinearEquiv k f σ hcard r 0 v) := by
  rfl

/-- Native scaling intertwines the source and exact restricted target action. -/
theorem torusLinear_intertwines (r : Fˣ) (n : ℕ) (g : Multiplicative F)
    (v : (projectiveResolution k f σ hcard).complex.X n) :
    (restrictedDegreeLinearEquiv k f σ hcard r n).symm
        (degreeScale k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) n
          (degreeLinearEquiv k f σ hcard n
            (((projectiveResolution k f σ hcard).complex.X n).ρ g v))) =
      (Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
        ((projectiveResolution k f σ hcard).complex.X n)).ρ g
        ((restrictedDegreeLinearEquiv k f σ hcard r n).symm
          (degreeScale k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) n
            (degreeLinearEquiv k f σ hcard n v))) := by
  apply (restrictedDegreeLinearEquiv k f σ hcard r n).injective
  rw [LinearEquiv.apply_symm_apply, degree_action, restricted_degree_action,
    LinearEquiv.apply_symm_apply, degreeScale_smul]
  congr 1
  change torusScale k f (Units.map σ.toMonoidHom r)
    (BinaryExteriorCharacter.character k f (σ g.toAdd)) = _
  rw [torusScale_character]
  congr 1
  change σ (r : F) ^ 2 * σ g.toAdd = σ ((r : F) ^ 2 * g.toAdd)
  simp only [map_mul, map_pow]

/-- The actual semilinear component for forward parameter scaling by `r²`. -/
def torusComponent (r : Fˣ) (n : ℕ) :
    (projectiveResolution k f σ hcard).complex.X n ⟶
      Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
        ((projectiveResolution k f σ hcard).complex.X n) :=
  coordinateMorphism ((projectiveResolution k f σ hcard).complex.X n)
    (Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X n))
    (degreeLinearEquiv k f σ hcard n)
    (restrictedDegreeLinearEquiv k f σ hcard r n)
    (degreeScale k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) n)
    (torusLinear_intertwines k f σ hcard r n)

@[simp] theorem torusComponent_apply (r : Fˣ) (n : ℕ)
    (v : (projectiveResolution k f σ hcard).complex.X n) :
    restrictedDegreeLinearEquiv k f σ hcard r n
      ((torusComponent k f σ hcard r n).hom v) =
      degreeScale k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) n
        (degreeLinearEquiv k f σ hcard n v) := by
  exact coordinateMorphism_apply
    ((projectiveResolution k f σ hcard).complex.X n)
    (Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
      ((projectiveResolution k f σ hcard).complex.X n))
    (degreeLinearEquiv k f σ hcard n)
    (restrictedDegreeLinearEquiv k f σ hcard r n)
    (degreeScale k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) n)
    (torusLinear_intertwines k f σ hcard r n) v

/-- The actual target-representation basis column has its constructed exponent weight. -/
theorem torusComponent_single_one (r : Fˣ) (n : ℕ) (a : DegreeIndex (Fin f) n) :
    (torusComponent k f σ hcard r n).hom (Finsupp.single a 1) =
      @SMul.smul k (Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
        ((projectiveResolution k f σ hcard).complex.X n))
        (inferInstanceAs (SMul k
          (Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
            ((projectiveResolution k f σ hcard).complex.X n))))
        (exponentWeight k f (torusCoefficients k f (Units.map σ.toMonoidHom r)) a.val : k)
        (Finsupp.single a 1) := by
  apply (restrictedDegreeLinearEquiv k f σ hcard r n).injective
  rw [torusComponent_apply]
  exact (degreeScale_single_one k f
    (torusCoefficients k f (Units.map σ.toMonoidHom r)) n a).trans
      ((restrictedDegreeLinearEquiv k f σ hcard r n).map_smul _
        (show Rep.res (BinaryAdditiveTorusAction.parameter r).toMonoidHom
          ((projectiveResolution k f σ hcard).complex.X n) from Finsupp.single a 1)).symm

/-- A genuine semilinear chain map on the actual additive-group projective resolution.
Its specialization at `r⁻¹` covers inverse conjugation for the cohomology action. -/
def torusChainMap (r : Fˣ) :
    (projectiveResolution k f σ hcard).complex ⟶
      ((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).mapProjectiveResolution
        (projectiveResolution k f σ hcard)).complex where
  f n := torusComponent k f σ hcard r n
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply Rep.hom_ext
    ext v
    apply (restrictedDegreeLinearEquiv k f σ hcard r j).injective
    change restrictedDegreeLinearEquiv k f σ hcard r j
        (((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).map
          ((projectiveResolution k f σ hcard).complex.d (j + 1) j)).hom
          ((torusComponent k f σ hcard r (j + 1)).hom v)) =
      restrictedDegreeLinearEquiv k f σ hcard r j
        ((torusComponent k f σ hcard r j).hom
          (((projectiveResolution k f σ hcard).complex.d (j + 1) j).hom v))
    rw [restricted_degree_differential, torusComponent_apply, torusComponent_apply,
      degree_differential]
    exact (degreeScale_gradedDifferential k f
      (torusCoefficients k f (Units.map σ.toMonoidHom r)) j _).symm

/-- The actual resolution scaling preserves augmentation to the trivial representation. -/
theorem torusChainMap_π (r : Fˣ) :
    torusChainMap k f σ hcard r ≫
      ((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).mapProjectiveResolution
        (projectiveResolution k f σ hcard)).π =
    (projectiveResolution k f σ hcard).π ≫
      (ChainComplex.single₀ (Rep k (Multiplicative F))).map
        (ResolutionConjugation.trivialRestriction
          (BinaryAdditiveTorusAction.parameter r).toMonoidHom) := by
  apply ((projectiveResolution k f σ hcard).complex.toSingle₀Equiv _).injective
  apply Subtype.ext
  change (torusChainMap k f σ hcard r ≫
      ((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).mapProjectiveResolution
        (projectiveResolution k f σ hcard)).π).f 0 =
    ((projectiveResolution k f σ hcard).π ≫
      (ChainComplex.single₀ (Rep k (Multiplicative F))).map
        (ResolutionConjugation.trivialRestriction
          (BinaryAdditiveTorusAction.parameter r).toMonoidHom)).f 0
  simp only [HomologicalComplex.comp_f, Functor.mapProjectiveResolution_π,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    ChainComplex.single₀_map_f_zero]
  apply Rep.hom_ext
  ext v
  change (((Rep.resFunctor (BinaryAdditiveTorusAction.parameter r).toMonoidHom).map
      ((projectiveResolution k f σ hcard).π.f 0)).hom
      ((torusComponent k f σ hcard r 0).hom v)) =
    ((projectiveResolution k f σ hcard).π.f 0).hom v
  rw [restricted_degree_augmentation, degree_augmentation, torusComponent_apply]
  exact augmentation_degreeScale k f
    (torusCoefficients k f (Units.map σ.toMonoidHom r)) _

end Representation

end Kourovka2135.BinaryResolutionScaling
