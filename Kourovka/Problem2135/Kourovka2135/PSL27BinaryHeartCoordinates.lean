import Kourovka2135.OddPSLTwoPermutationHeart
import Kourovka2135.PSL27BinaryHeartData
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Intertwining

/-! Actual coordinates on the binary projective permutation heart of PSL2(7).

The affine chart is 0,...,6, with `none` representing infinity. A class is
normalized by subtracting its value at 6. Its representative has value zero
at 6 and value equal to the sum of its first six coordinates at infinity.
The linear equivalence is constructed through the actual constant-line
quotient. The group representation is transported from the genuine PSL2
projective action, and its two matrices are checked against the finite data.
No exceptional group isomorphism or presentation is used.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace Kourovka2135.PSL27BinaryHeartCoordinates

open scoped Matrix LinearAlgebra.Projectivization
open OddPSLTwoProjectiveChart

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev F := ZMod 7
abbrev k := ZMod 2
abbrev X := Option F
abbrev G := Q F
abbrev V := Fin 6 → k

theorem odd_card : Odd (Fintype.card F) := by decide +kernel

abbrev Space := FinitePermutationAugmentation.Space k X
abbrev constantLine := FinitePermutationHeart.constantLine k X
  (OddPSLTwoPermutationHeart.card_points_cast_zero F k odd_card)
abbrev Heart := OddPSLTwoPermutationHeart.Heart F k odd_card
abbrev heartRepresentation := OddPSLTwoPermutationHeart.heartRepresentation F k odd_card

/-- The actual six affine coordinates, after removing the value at 6. -/
def rawCoordinates (f : X → k) (i : Fin 6) : k :=
  f (some (i.val : F)) - f (some 6)

/-- The normalized augmentation representative of six coordinates. -/
def rawExtend (v : V) : X → k
  | none => ∑ i, v i
  | some z => if h : z.val < 6 then v ⟨z.val, h⟩ else 0

private theorem rawExtend_sum : ∀ v : V, ∑ x : X, rawExtend v x = 0 := by
  decide +kernel

private theorem rawCoordinates_extend : ∀ v : V,
    rawCoordinates (rawExtend v) = v := by
  decide +kernel

private theorem rawExtend_coordinates : ∀ f : X → k,
    (∑ x : X, f x) = 0 →
      rawExtend (rawCoordinates f) = fun x => f x - f (some 6) := by
  decide +kernel

def coordinatesOnSpace : Space →ₗ[k] V where
  toFun f := rawCoordinates f.val
  map_add' f h := by
    funext i
    change (f.val (some (i.val : F)) + h.val (some (i.val : F))) -
      (f.val (some 6) + h.val (some 6)) = _
    simp only [rawCoordinates, Pi.add_apply]
    abel
  map_smul' c f := by
    funext i
    change c * f.val (some (i.val : F)) - c * f.val (some 6) =
      c * (f.val (some (i.val : F)) - f.val (some 6))
    exact (mul_sub _ _ _).symm

def extend : V →ₗ[k] Space where
  toFun v := ⟨rawExtend v, rawExtend_sum v⟩
  map_add' v w := by
    apply Subtype.ext
    funext x
    cases x with
    | none =>
        change (∑ i : Fin 6, (v i + w i)) = (∑ i : Fin 6, v i) + ∑ i : Fin 6, w i
        exact Finset.sum_add_distrib
    | some z =>
        change (if h : z.val < 6 then (v + w) ⟨z.val, h⟩ else 0) = _
        by_cases h : z.val < 6 <;> simp [rawExtend, h]
  map_smul' c v := by
    apply Subtype.ext
    funext x
    cases x with
    | none =>
        change (∑ i : Fin 6, c • v i) = c • ∑ i : Fin 6, v i
        exact Finset.smul_sum.symm
    | some z =>
        change (if h : z.val < 6 then (c • v) ⟨z.val, h⟩ else 0) = _
        by_cases h : z.val < 6 <;> simp [rawExtend, h]

theorem constantLine_le_ker : constantLine ≤ LinearMap.ker coordinatesOnSpace := by
  rintro f ⟨c, rfl⟩
  apply funext
  intro i
  exact sub_self c

/-- Coordinates descend through the actual constant submodule. -/
def coordinates : Heart →ₗ[k] V := constantLine.liftQ coordinatesOnSpace constantLine_le_ker

def sectionMap : V →ₗ[k] Heart := constantLine.mkQ.comp extend

@[simp] theorem coordinates_mkQ (f : Space) :
    coordinates (constantLine.mkQ f) = rawCoordinates f.val := rfl

@[simp] theorem coordinates_section (v : V) : coordinates (sectionMap v) = v :=
  rawCoordinates_extend v

theorem section_coordinates (v : Heart) : sectionMap (coordinates v) = v := by
  obtain ⟨f, rfl⟩ := constantLine.mkQ_surjective v
  have he : extend (coordinatesOnSpace f) = f -
      FinitePermutationHeart.constants k X
        (OddPSLTwoPermutationHeart.card_points_cast_zero F k odd_card) (f.val (some 6)) := by
    apply Subtype.ext
    exact rawExtend_coordinates f.val f.property
  change constantLine.mkQ (extend (coordinatesOnSpace f)) = constantLine.mkQ f
  rw [he, map_sub]
  have hc : constantLine.mkQ
      (FinitePermutationHeart.constants k X
        (OddPSLTwoPermutationHeart.card_points_cast_zero F k odd_card) (f.val (some 6))) = 0 :=
    (Submodule.Quotient.mk_eq_zero constantLine).mpr ⟨f.val (some 6), rfl⟩
  rw [hc, sub_zero]

/-- Actual linear equivalence from the projective permutation heart. -/
def coordinateEquiv : Heart ≃ₗ[k] V where
  toLinearMap := coordinates
  invFun := sectionMap
  left_inv := section_coordinates
  right_inv := coordinates_section

@[simp] theorem coordinateEquiv_mkQ (f : Space) :
    coordinateEquiv (constantLine.mkQ f) = rawCoordinates f.val := rfl

@[simp] theorem coordinateEquiv_symm (v : V) :
    coordinateEquiv.symm v = constantLine.mkQ (extend v) := rfl

/-- A representation of every element of the actual PSL2 quotient. -/
def representation : Representation k G V :=
  coordinateEquiv.conjRingEquiv.toMonoidHom.comp heartRepresentation

theorem representation_coordinateEquiv (g : G) (v : Heart) :
    representation g (coordinateEquiv v) = coordinateEquiv (heartRepresentation g v) := by
  change coordinateEquiv (heartRepresentation g (coordinateEquiv.symm (coordinateEquiv v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The coordinate identification is equivariant for every group element. -/
def heartEquiv : heartRepresentation.Equiv representation :=
  Representation.Equiv.mk coordinateEquiv (fun g => LinearMap.ext (fun v =>
    (representation_coordinateEquiv g v).symm))

/-- This formula uses the inverse point permutation, as a genuine left action does. -/
theorem representation_apply (g : G) (v : V) (i : Fin 6) :
    representation g v i = rawExtend v (g⁻¹ • some (i.val : F)) -
      rawExtend v (g⁻¹ • some 6) := rfl

def U : G := quotient F (SLTwo.uni 1)
def weyl : SLTwo.SL2 F := ⟨!![0, -1; 1, 0], by decide +kernel⟩
def W : G := quotient F weyl

def uPoint : X → X
  | none => none
  | some x => some (x + 1)

def uInversePoint : X → X
  | none => none
  | some x => some (x - 1)

def wPoint : X → X
  | none => some 0
  | some x => if x = 0 then none else some (-x⁻¹)

def wScale : X → F
  | none => 1
  | some x => if x = 0 then -1 else x

private theorem uPoint_inverse : ∀ x : X, uPoint (uInversePoint x) = x := by
  decide +kernel

private theorem wPoint_involutive : Function.Involutive wPoint := by
  change ∀ x : X, wPoint (wPoint x) = x
  decide +kernel

/-- An eight-point certificate in the native two-dimensional columns. -/
private theorem weyl_representative : ∀ x : X,
    wScale x • representative F (wPoint x) = weyl.val.mulVec (representative F x) := by
  decide +kernel

theorem U_smul (x : X) : U • x = uPoint x := by
  cases x with
  | none => exact uni_smul_none F 1
  | some x => exact uni_smul_some F 1 x

theorem W_smul (x : X) : W • x = wPoint x := by
  apply point_injective F
  rw [point_smul]
  change Projectivization.mk F (weyl.val.mulVec (representative F x)) _ =
    Projectivization.mk F (representative F (wPoint x)) _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨wScale x, weyl_representative x⟩

theorem U_inv_smul (x : X) : U⁻¹ • x = uInversePoint x := by
  apply (MulAction.bijective U).injective
  change U • (U⁻¹ • x) = U • uInversePoint x
  rw [smul_inv_smul, U_smul, uPoint_inverse]

theorem W_inv_smul (x : X) : W⁻¹ • x = wPoint x := by
  apply (MulAction.bijective W).injective
  change W • (W⁻¹ • x) = W • wPoint x
  rw [smul_inv_smul, W_smul, wPoint_involutive]

private theorem matrix_U_checked : ∀ i j : Fin 6,
    rawCoordinates (fun x => rawExtend (Pi.single j 1) (uInversePoint x)) i =
      PSL27BinaryHeartData.heartU i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem matrix_W_checked : ∀ i j : Fin 6,
    rawCoordinates (fun x => rawExtend (Pi.single j 1) (wPoint x)) i =
      PSL27BinaryHeartData.heartW i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem toMatrix_U : LinearMap.toMatrix' (representation U) = PSL27BinaryHeartData.heartU := by
  ext i j
  change representation U (Pi.single j 1) i = _
  rw [representation_apply, U_inv_smul, U_inv_smul]
  exact matrix_U_checked i j

theorem toMatrix_W : LinearMap.toMatrix' (representation W) = PSL27BinaryHeartData.heartW := by
  ext i j
  change representation W (Pi.single j 1) i = _
  rw [representation_apply, W_inv_smul, W_inv_smul]
  exact matrix_W_checked i j

/-- The quotient construction has precisely six dimensions. -/
theorem finrank_heart : Module.finrank k Heart = 6 := by
  rw [coordinateEquiv.finrank_eq]
  simp [V]

end Kourovka2135.PSL27BinaryHeartCoordinates
