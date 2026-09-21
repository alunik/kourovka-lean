import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
Direct comparison of semilinear actions on projective resolutions.

The action on a Hom complex is the actual map `c ↦ τ ≫ F(c) ≫ φ`.
Two resolution actions lifting the same augmentation map are compared by
`ProjectiveResolution.liftHomotopy`, without a naturality assertion about Ext.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Kourovka2135.ResolutionConjugation
open CategoryTheory
universe u v w

section HomComplex
variable (k : Type u) [CommRing k]
variable {C : Type v} [Category.{w} C] [Abelian C] [Linear k C]

/-- Precomposition on the actual linear Yoneda complex. -/
def homPrecomp {P Q : ChainComplex C ℕ} (c : P ⟶ Q) (A : C) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    (((((linearYoneda k C).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map c).op)

@[simp] theorem homPrecomp_apply {P Q : ChainComplex C ℕ} (c : P ⟶ Q)
    (A : C) (n : ℕ) (a : Q.X n ⟶ A) :
    (homPrecomp k c A).f n a = c.f n ≫ a := rfl

@[simp] theorem homPrecomp_id (P : ChainComplex C ℕ) (A : C) :
    homPrecomp k (𝟙 P) A = 𝟙 (P.linearYonedaObj k A) := by
  ext n a
  change (𝟙 (P.X n)) ≫ a = a
  exact Category.id_comp a

@[simp] theorem homPrecomp_comp {P Q R : ChainComplex C ℕ}
    (c : P ⟶ Q) (d : Q ⟶ R) (A : C) :
    homPrecomp k (c ≫ d) A = homPrecomp k d A ≫ homPrecomp k c A := by
  ext n a
  change (c.f n ≫ d.f n) ≫ a = c.f n ≫ d.f n ≫ a
  exact Category.assoc _ _ _

/-- Contravariant Hom takes a chain homotopy to a cochain homotopy. -/
def homPrecompHomotopy {P Q : ChainComplex C ℕ} {c d : P ⟶ Q}
    (h : Homotopy c d) (A : C) :
    Homotopy (homPrecomp k c A) (homPrecomp k d A) :=
  (((linearYoneda k C).obj A).rightOp.mapHomotopy h).unop

/-- A comparison equivalence of resolutions gives a direct Hom-complex equivalence. -/
def homPrecompHomotopyEquiv {P Q : ChainComplex C ℕ}
    (h : HomotopyEquiv P Q) (A : C) :
    HomotopyEquiv (Q.linearYonedaObj k A) (P.linearYonedaObj k A) where
  hom := homPrecomp k h.hom A
  inv := homPrecomp k h.inv A
  homotopyHomInvId := by
    rw [← homPrecomp_comp, ← homPrecomp_id]
    exact homPrecompHomotopy k h.homotopyInvHomId A
  homotopyInvHomId := by
    rw [← homPrecomp_comp, ← homPrecomp_id]
    exact homPrecompHomotopy k h.homotopyHomInvId A

/-- Postcomposition by the actual coefficient map. -/
def homPostcomp (P : ChainComplex C ℕ) {A B : C} (φ : A ⟶ B) :
    P.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f n := ModuleCat.ofHom (Linear.rightComp k (P.X n) φ)
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Category.assoc _ _ _).symm

@[simp] theorem homPostcomp_apply (P : ChainComplex C ℕ) {A B : C}
    (φ : A ⟶ B) (n : ℕ) (a : P.X n ⟶ A) :
    (homPostcomp k P φ).f n a = a ≫ φ := rfl

variable (F : C ⥤ C) [F.Additive] [F.Linear k]

/-- The actual functor map on every Hom space, compatible with its differential. -/
def homMapFunctor (P : ChainComplex C ℕ) (A : C) :
    P.linearYonedaObj k A ⟶
      ChainComplex.linearYonedaObj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P) k (F.obj A) where
  f _ := ModuleCat.ofHom (F.mapLinearMap k)
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (F.map_comp _ a).symm

@[simp] theorem homMapFunctor_apply (P : ChainComplex C ℕ) (A : C)
    (n : ℕ) (a : P.X n ⟶ A) :
    (homMapFunctor k F P A).f n a = F.map a := rfl

/-- The Hom action induced by a semilinear resolution map and a coefficient map. -/
def semilinearHom (P : ChainComplex C ℕ) (A : C)
    (τ : P ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P)
    (φ : F.obj A ⟶ A) : P.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  homMapFunctor k F P A ≫ homPrecomp k τ (F.obj A) ≫ homPostcomp k P φ

@[simp] theorem semilinearHom_apply (P : ChainComplex C ℕ) (A : C)
    (τ : P ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P)
    (φ : F.obj A ⟶ A) (n : ℕ) (a : P.X n ⟶ A) :
    (semilinearHom k F P A τ φ).f n a = τ.f n ≫ F.map a ≫ φ := by
  change (τ.f n ≫ F.map a) ≫ φ = τ.f n ≫ F.map a ≫ φ
  exact Category.assoc _ _ _

end HomComplex

section ResolutionComparison
variable {C : Type v} [Category.{w} C] [Abelian C]
variable (F : C ⥤ C) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
variable {X : C} (P Q : ProjectiveResolution X)

/-- A comparison commuting with augmentation still does so after applying the functor. -/
theorem map_comparison_π (c : P.complex ⟶ Q.complex) (hc : c ≫ Q.π = P.π) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map c ≫
      (F.mapProjectiveResolution Q).π = (F.mapProjectiveResolution P).π := by
  simp only [Functor.mapProjectiveResolution_π, ← Category.assoc, ← Functor.map_comp, hc]

/-- The only compatibility inputs are the two actual augmentation equations. -/
def resolutionActionHomotopy (ι : X ⟶ F.obj X)
    (τP : P.complex ⟶ (F.mapProjectiveResolution P).complex)
    (τQ : Q.complex ⟶ (F.mapProjectiveResolution Q).complex)
    (hP : τP ≫ (F.mapProjectiveResolution P).π =
      P.π ≫ (ChainComplex.single₀ C).map ι)
    (hQ : τQ ≫ (F.mapProjectiveResolution Q).π =
      Q.π ≫ (ChainComplex.single₀ C).map ι) :
    Homotopy
      (τP ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.homotopyEquiv P Q).hom)
      ((ProjectiveResolution.homotopyEquiv P Q).hom ≫ τQ) := by
  apply ProjectiveResolution.liftHomotopy (P := P) (Q := F.mapProjectiveResolution Q) ι
  · rw [Category.assoc, map_comparison_π F P Q _
      (ProjectiveResolution.homotopyEquiv_hom_π P Q), hP]
  · rw [Category.assoc, hQ, ← Category.assoc,
      ProjectiveResolution.homotopyEquiv_hom_π]

variable (k : Type u) [CommRing k] [Linear k C] [F.Linear k]

/-- The comparison isomorphism is equivariant on cohomology, obtained from a chain homotopy. -/
theorem homology_semilinear_comparison (A : C) (ι : X ⟶ F.obj X)
    (τP : P.complex ⟶ (F.mapProjectiveResolution P).complex)
    (τQ : Q.complex ⟶ (F.mapProjectiveResolution Q).complex)
    (hP : τP ≫ (F.mapProjectiveResolution P).π =
      P.π ≫ (ChainComplex.single₀ C).map ι)
    (hQ : τQ ≫ (F.mapProjectiveResolution Q).π =
      Q.π ≫ (ChainComplex.single₀ C).map ι)
    (φ : F.obj A ⟶ A) (n : ℕ) :
    HomologicalComplex.homologyMap
      (homPrecomp k (ProjectiveResolution.homotopyEquiv P Q).hom A) n ≫
      HomologicalComplex.homologyMap (semilinearHom k F P.complex A τP φ) n =
    HomologicalComplex.homologyMap (semilinearHom k F Q.complex A τQ φ) n ≫
      HomologicalComplex.homologyMap
        (homPrecomp k (ProjectiveResolution.homotopyEquiv P Q).hom A) n := by
  let c := (ProjectiveResolution.homotopyEquiv P Q).hom
  have h := ((homPrecompHomotopy k (resolutionActionHomotopy F P Q ι τP τQ hP hQ)
    (F.obj A)).compLeft (homMapFunctor k F Q.complex A)).compRight
      (homPostcomp k P.complex φ)
  have hleft : homMapFunctor k F Q.complex A ≫
      homPrecomp k (τP ≫ (F.mapHomologicalComplex (ComplexShape.down ℕ)).map c)
        (F.obj A) ≫ homPostcomp k P.complex φ =
      homPrecomp k c A ≫ semilinearHom k F P.complex A τP φ := by
    ext i a
    change ((τP.f i ≫ F.map (c.f i)) ≫ F.map a) ≫ φ =
      (τP.f i ≫ F.map (c.f i ≫ a)) ≫ φ
    simp only [F.map_comp, Category.assoc]
  have hright : homMapFunctor k F Q.complex A ≫
      homPrecomp k (c ≫ τQ) (F.obj A) ≫ homPostcomp k P.complex φ =
      semilinearHom k F Q.complex A τQ φ ≫ homPrecomp k c A := by
    ext i a
    change ((c.f i ≫ τQ.f i) ≫ F.map a) ≫ φ =
      c.f i ≫ (τQ.f i ≫ F.map a) ≫ φ
    simp only [Category.assoc]
  have heq : HomologicalComplex.homologyMap
      (homPrecomp k c A ≫ semilinearHom k F P.complex A τP φ) n =
    HomologicalComplex.homologyMap
      (semilinearHom k F Q.complex A τQ φ ≫ homPrecomp k c A) n := by
    rw [← hleft, ← hright]
    exact h.homologyMap_eq n
  simpa only [HomologicalComplex.homologyMap_comp] using heq

end ResolutionComparison

section Bar
variable {k G : Type u} [CommRing k] [Group G]

/-- Applying the group map to the tuple and to its translating group element. -/
def barMapComponent (f : G →* G) (n : ℕ) :
    Rep.free k G (Fin n → G) ⟶ Rep.res f (Rep.free k G (Fin n → G)) :=
  Rep.freeLift k G _ (fun z => Finsupp.single (f ∘ z) (MonoidAlgebra.single 1 1))

@[simp] theorem barMapComponent_single (f : G →* G) (n : ℕ)
    (z : Fin n → G) (g : G) (r : k) :
    (barMapComponent (k := k) f n).hom (Finsupp.single z (MonoidAlgebra.single g r)) =
      Finsupp.single (f ∘ z) (MonoidAlgebra.single (f g) r) := by
  simp [barMapComponent]

theorem barMapComponent_d (f : G →* G) (n : ℕ) :
    Rep.barComplex.d k G n ≫ barMapComponent f n =
      barMapComponent f (n + 1) ≫ (Rep.resFunctor f).map (Rep.barComplex.d k G n) := by
  apply Rep.free_ext k G _ _ _
  intro z
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [Rep.barComplex.d_single, map_add, map_sum, barMapComponent_single]
  rw [barMapComponent_single, map_one, Rep.resMap_hom_apply, Rep.barComplex.d_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [barMapComponent_single, map_one, Fin.comp_contractNth (· * ·) (· * ·) f.map_mul]

/-- The actual semilinear bar chain map associated with a group homomorphism. -/
def barMap (f : G →* G) : Rep.barComplex k G ⟶
    ((Rep.resFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex k G) where
  f n := barMapComponent f n
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    change barMapComponent f (j + 1) ≫ (Rep.resFunctor f).map
      ((Rep.barComplex k G).d (j + 1) j) =
      (Rep.barComplex k G).d (j + 1) j ≫ barMapComponent f j
    rw [Rep.barComplex.d_def]
    exact (barMapComponent_d (k := k) f j).symm

/-- On actual inhomogeneous cochains, the bar action is exactly mathlib's map. -/
theorem barMap_cochainsMap (f : G →* G) (A : Rep k G) (φ : Rep.res f A ⟶ A) :
    (groupCohomology.inhomogeneousCochainsIso A).hom ≫
      semilinearHom k (Rep.resFunctor f) (Rep.barComplex k G) A (barMap f) φ =
    groupCohomology.cochainsMap f φ ≫
      (groupCohomology.inhomogeneousCochainsIso A).hom := by
  ext n c
  apply Rep.free_ext k G _ _ _
  intro z
  change φ.hom ((Rep.freeLift k G A c).hom
      ((barMapComponent (k := k) f n).hom (Finsupp.single z (MonoidAlgebra.single 1 1)))) =
    (Rep.freeLift k G A (fun z => φ.hom (c (f ∘ z)))).hom
      (Finsupp.single z (MonoidAlgebra.single 1 1))
  rw [barMapComponent_single, map_one]
  simp

/-- Restriction along a group automorphism is an actual equivalence of representation categories. -/
def resEquivalence (f : G ≃* G) : Rep k G ≌ Rep k G where
  functor := Rep.resFunctor f.toMonoidHom
  inverse := Rep.resFunctor f.symm.toMonoidHom
  unitIso := NatIso.ofComponents (fun A =>
    Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k A) (by
      intro g
      ext a
      simp))) (by intros; ext; rfl)
  counitIso := NatIso.ofComponents (fun A =>
    Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k A) (by
      intro g
      ext a
      simp))) (by intros; ext; rfl)
  functor_unitIso_comp _ := by ext; rfl

instance resFunctorIsEquivalence (f : G ≃* G) :
    (Rep.resFunctor (k := k) f.toMonoidHom).IsEquivalence :=
  (resEquivalence (k := k) f).isEquivalence_functor

/-- The identity on the trivial coefficient module, regarded as a restriction map. -/
def trivialRestriction (f : G →* G) :
    Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k G k) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- The tuple map preserves the actual bar augmentation. -/
theorem barMap_π (f : G ≃* G) :
    barMap (k := k) f.toMonoidHom ≫
      ((Rep.resFunctor f.toMonoidHom).mapProjectiveResolution (Rep.barResolution k G)).π =
    (Rep.barResolution k G).π ≫
      (ChainComplex.single₀ (Rep k G)).map (trivialRestriction f.toMonoidHom) := by
  apply ((Rep.barComplex k G).toSingle₀Equiv _).injective
  apply Subtype.ext
  change (barMap (k := k) f.toMonoidHom ≫
    ((Rep.resFunctor f.toMonoidHom).mapProjectiveResolution (Rep.barResolution k G)).π).f 0 =
    ((Rep.barResolution k G).π ≫
      (ChainComplex.single₀ (Rep k G)).map (trivialRestriction f.toMonoidHom)).f 0
  simp only [HomologicalComplex.comp_f, Functor.mapProjectiveResolution_π,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    ChainComplex.single₀_map_f_zero]
  apply Rep.free_ext k G _ _ _
  intro z
  have hz : f.toMonoidHom ∘ z = z := funext (fun i => Fin.elim0 i)
  change ((Rep.barResolution k G).π.f 0).hom
      ((barMapComponent (k := k) f.toMonoidHom 0).hom
        (Finsupp.single z (MonoidAlgebra.single 1 1))) =
    ((Rep.barResolution k G).π.f 0).hom (Finsupp.single z (MonoidAlgebra.single 1 1))
  rw [barMapComponent_single, map_one, hz]

/-- A direct cohomology isomorphism, chosen by comparing the actual bar resolution with `P`. -/
def groupCohomologyIso (A : Rep k G)
    (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
    (groupCohomology.inhomogeneousCochainsIso A) ≪≫
  (homPrecompHomotopyEquiv k
    (ProjectiveResolution.homotopyEquiv P (Rep.barResolution k G)) A).toHomologyIso n

/-- Ordinary group-cohomology functoriality agrees with an actual augmented semilinear
resolution action. There is no action-comparison hypothesis. -/
theorem groupCohomologyIso_naturality (f : G ≃* G) (A : Rep k G)
    (P : ProjectiveResolution (Rep.trivial k G k))
    (τ : P.complex ⟶ ((Rep.resFunctor f.toMonoidHom).mapProjectiveResolution P).complex)
    (hτ : τ ≫ ((Rep.resFunctor f.toMonoidHom).mapProjectiveResolution P).π =
      P.π ≫ (ChainComplex.single₀ (Rep k G)).map (trivialRestriction f.toMonoidHom))
    (φ : Rep.res f.toMonoidHom A ⟶ A) (n : ℕ) :
    (groupCohomologyIso A P n).hom ≫
      HomologicalComplex.homologyMap
        (semilinearHom k (Rep.resFunctor f.toMonoidHom) P.complex A τ φ) n =
    groupCohomology.map f.toMonoidHom φ n ≫ (groupCohomologyIso A P n).hom := by
  have h := homology_semilinear_comparison (Rep.resFunctor f.toMonoidHom) P
    (Rep.barResolution k G) k A (trivialRestriction f.toMonoidHom)
      τ (barMap f.toMonoidHom) hτ (barMap_π f) φ n
  have hb := congrArg (fun c => HomologicalComplex.homologyMap c n)
    (barMap_cochainsMap f.toMonoidHom A φ)
  simp only [HomologicalComplex.homologyMap_comp] at hb
  change HomologicalComplex.homologyMap
      (homPrecomp k (ProjectiveResolution.homotopyEquiv P (Rep.barResolution k G)).hom A) n ≫
      HomologicalComplex.homologyMap
        (semilinearHom k (Rep.resFunctor f.toMonoidHom) P.complex A τ φ) n =
    HomologicalComplex.homologyMap
        (semilinearHom k (Rep.resFunctor f.toMonoidHom) (Rep.barComplex k G) A
          (barMap f.toMonoidHom) φ) n ≫
      HomologicalComplex.homologyMap
        (homPrecomp k (ProjectiveResolution.homotopyEquiv P (Rep.barResolution k G)).hom A) n at h
  change (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
    HomologicalComplex.homologyMap
      (homPrecomp k (ProjectiveResolution.homotopyEquiv P (Rep.barResolution k G)).hom A) n) ≫ _ =
    _ ≫ (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      HomologicalComplex.homologyMap
        (homPrecomp k (ProjectiveResolution.homotopyEquiv P (Rep.barResolution k G)).hom A) n)
  rw [Category.assoc, h, ← Category.assoc, hb]
  rfl

end Bar

end Kourovka2135.ResolutionConjugation
