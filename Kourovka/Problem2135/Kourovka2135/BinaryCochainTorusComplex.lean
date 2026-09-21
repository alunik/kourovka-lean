import Kourovka2135.BinaryCochainTorusGraded
import Kourovka2135.BinaryCochainDimension
import Kourovka2135.HomologyCoordinateEquivariance

/-! The concrete graded diagonal induces an automorphism of the actual
cochain complex and its categorical homology. The previously constructed
homology-coordinate injection intertwines this action with the explicit
block weights. No identification with a group-normalizer action is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryCochainTorusComplex

open CategoryTheory BinaryCochainGraded BinaryCochainComplex
open scoped IsMulCommutative

variable (k : Type u) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- The concrete graded diagonal is an automorphism of the actual cochain complex. -/
def diagonalIso (ell : kˣ) (c : Fin f → kˣ) : complex k I ≅ complex k I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (BinaryCochainTorusGraded.diagonalEquiv k I ell c n).toModuleIso)
    (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change differential k I n
          ((BinaryCochainTorusGraded.diagonalEquiv k I ell c n).toLinearMap v) =
        (BinaryCochainTorusGraded.diagonalEquiv k I ell c (n + 1)).toLinearMap
          (differential k I n v)
      rw [BinaryCochainTorusGraded.diagonalEquiv_toLinearMap,
        BinaryCochainTorusGraded.diagonalEquiv_toLinearMap]
      exact (BinaryCochainTorusGraded.diagonal_differential k I ell c n v).symm)

@[simp] theorem diagonalIso_hom_f_hom (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    ((diagonalIso k I ell c).hom.f n).hom =
      BinaryCochainTorusGraded.diagonal k I ell c n :=
  BinaryCochainTorusGraded.diagonalEquiv_toLinearMap k I ell c n

/-- The homology automorphism is induced by the actual complex automorphism. -/
def homologyIso (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (complex k I).homology n ≅ (complex k I).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
    (diagonalIso k I ell c)

/-- Its underlying ground-ring linear automorphism. -/
def homologyAction (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (complex k I).homology n ≃ₗ[k] (complex k I).homology n :=
  (homologyIso k I ell c n).toLinearEquiv

/-- The explicit diagonal on the surviving coordinate space. -/
def survivorDiagonal (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (SurvivorIndex I n → k) ≃ₗ[k] (SurvivorIndex I n → k) :=
  LinearEquiv.piCongrRight fun a =>
    LinearEquiv.smulOfUnit (R := k) (M := k)
      (BinaryCochainTorus.blockWeight k I ell c a.val.val)

omit [CharP k 2] in
@[simp] theorem survivorDiagonal_apply (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (v : SurvivorIndex I n → k) (a : SurvivorIndex I n) :
    survivorDiagonal k I ell c n v a =
      (BinaryCochainTorus.blockWeight k I ell c a.val.val : k) * v a := rfl

/-- The induced map on the actual adjacent-degree short complex. -/
def shortMap (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    BinaryCochainDimension.degreeShortComplex k I n ⟶
      BinaryCochainDimension.degreeShortComplex k I n :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat k) (ComplexShape.up ℕ)
    n (n + 1) (n + 2)).map (diagonalIso k I ell c).hom

@[simp] theorem shortMap_τ₂_hom (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (shortMap k I ell c n).τ₂.hom = BinaryCochainTorusGraded.diagonal k I ell c (n + 1) :=
  diagonalIso_hom_f_hom k I ell c (n + 1)

/-- The cochain coordinate identity descends through the actual homology quotient. -/
theorem shortHomologyCoordinate_equivariance (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (BinaryCochainDimension.shortHomologyCoordinate k I n).comp
        (ShortComplex.homologyMap (shortMap k I ell c n)).hom =
      (survivorDiagonal k I ell c (n + 1)).toLinearMap.comp
        (BinaryCochainDimension.shortHomologyCoordinate k I n) := by
  apply HomologyCoordinateEquivariance.homologyCoordinate_equivariance
  rw [shortMap_τ₂_hom]
  apply LinearMap.ext
  intro v
  funext a
  exact BinaryCochainTorusGraded.survivorMap_diagonal_apply k I ell c (n + 1) v a

set_option backward.isDefEq.respectTransparency false in
/-- The established comparison with short-complex homology is natural for this action. -/
theorem homologyShortIso_naturality (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (homologyIso k I ell c (n + 1)).hom ≫
        (BinaryCochainDimension.homologyShortIso k I n).hom =
      (BinaryCochainDimension.homologyShortIso k I n).hom ≫
        ShortComplex.homologyMap (shortMap k I ell c n) := by
  have hsc := (HomologicalComplex.natIsoSc' (ModuleCat k) (ComplexShape.up ℕ)
    n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality (diagonalIso k I ell c).hom
  have hh := congrArg (fun τ => ShortComplex.homologyMap τ) hsc
  dsimp only [homologyIso, BinaryCochainDimension.homologyShortIso,
    HomologicalComplex.homologyIsoSc', Functor.mapIso, HomologicalComplex.homologyFunctor,
    HomologicalComplex.homologyMap, ShortComplex.homologyMapIso, shortMap,
    HomologicalComplex.isoSc', Iso.app]
  simpa only [ShortComplex.homologyMap_comp] using hh

/-- The existing homology-coordinate injection intertwines the actual homology action. -/
theorem homologyCoordinate_equivariance (ell : kˣ) (c : Fin f → kˣ) (n : ℕ) :
    (BinaryCochainDimension.homologyCoordinate k I n).comp
        (homologyAction k I ell c (n + 1)).toLinearMap =
      (survivorDiagonal k I ell c (n + 1)).toLinearMap.comp
        (BinaryCochainDimension.homologyCoordinate k I n) := by
  have hnat : (BinaryCochainDimension.homologyShortIso k I n).hom.hom.comp
        (homologyIso k I ell c (n + 1)).hom.hom =
      (ShortComplex.homologyMap (shortMap k I ell c n)).hom.comp
        (BinaryCochainDimension.homologyShortIso k I n).hom.hom :=
    congrArg ModuleCat.Hom.hom (homologyShortIso_naturality k I ell c n)
  change (BinaryCochainDimension.shortHomologyCoordinate k I n).comp
      ((BinaryCochainDimension.homologyShortIso k I n).hom.hom.comp
        (homologyIso k I ell c (n + 1)).hom.hom) = _
  rw [hnat, ← LinearMap.comp_assoc, shortHomologyCoordinate_equivariance]
  rfl

/-- Explicit block character on every surviving homology coordinate. -/
theorem homologyCoordinate_action_apply (ell : kˣ) (c : Fin f → kˣ) (n : ℕ)
    (x : (complex k I).homology (n + 1)) (a : SurvivorIndex I (n + 1)) :
    BinaryCochainDimension.homologyCoordinate k I n
        (homologyAction k I ell c (n + 1) x) a =
      (BinaryCochainTorus.blockWeight k I ell c a.val.val : k) *
        BinaryCochainDimension.homologyCoordinate k I n x a :=
  congrFun (LinearMap.congr_fun (homologyCoordinate_equivariance k I ell c n) x) a


end Kourovka2135.BinaryCochainTorusComplex
