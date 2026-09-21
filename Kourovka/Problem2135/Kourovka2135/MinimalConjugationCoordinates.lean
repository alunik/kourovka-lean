import Kourovka2135.MinimalConjugationModule
import Kourovka2135.TrivialTargetHomIsotypic
import Kourovka2135.MinimalCenterSelfDual

/-! Actual quotient-equivariant coordinates for the faithful conjugation kernel.

The action on the kernel is identified using the actual extension inclusion,
and the coordinates intertwine it with inverse precomposition on N/Z(N).
Consequently this individual kernel module is semisimple and isotypic, by
an actual injective map into the actual Hom representation. No semisimple
ambient group algebra or module-classification hypothesis is imposed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalConjugationCoordinates

open scoped IsMulCommutative MonoidAlgebra

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)

omit [Finite G] in
/-- The actual ambient action lands in automorphisms fixing the whole center pointwise. -/
def ambientCenterFixer : G →* CentralAutomorphismCoordinate.fixesCenterSubgroup N where
  toFun g := ⟨MulAut.conjNormal g,
    NormalConjugationEmbedding.conjNormal_fixes_center N
      (minimal_noncentral_center_le N hnonabelian hmin) g⟩
  map_one' := Subtype.ext ((MulAut.conjNormal : G →* MulAut N).map_one)
  map_mul' a b := Subtype.ext ((MulAut.conjNormal : G →* MulAut N).map_mul a b)

variable [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)]
variable [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

local notation "K" => MinimalConjugationModule.Kernel N R
local notation "C" => MinimalConjugationModule.Centralizer N
local notation "V" => Additive (N ⧸ Subgroup.center N)
local notation "Z" => Additive (CentralAutomorphismTorsion.centerTorsion N 2)
local notation "ρ" => minimalCenterRepresentation N hN hmin R hR
local notation "τ" => MinimalConjugationModule.representation N hN hmin hnonabelian R hR
local notation "j" => MinimalConjugationModule.kernelToCentralAut N hN hmin hnonabelian R hR
local notation "L" => MinimalConjugationModule.linearCoordinate N hN hmin hnonabelian R hR

omit [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
/-- The kernel embedding intertwines actual quotient action and actual automorphism conjugation. -/
theorem kernelToCentralAut_representation (g : G) (k : K) :
    j ((τ (QuotientGroup.mk' R g) (Additive.ofMul k)).toMul) =
      CentralAutomorphismEquivariance.conjugation N (MulAut.conjNormal g) (j k) := by
  have hk := MinimalConjugationModule.representation_mk_inl N hN hmin hnonabelian R hR g k
  change ((τ (QuotientGroup.mk' R g) (Additive.ofMul k)).toMul : G ⧸ C) =
    QuotientGroup.mk' C g * (k : G ⧸ C) * (QuotientGroup.mk' C g)⁻¹ at hk
  apply Subtype.ext
  change NormalConjugationEmbedding.quotientConjugation N
      ((τ (QuotientGroup.mk' R g) (Additive.ofMul k)).toMul : G ⧸ C) =
    (MulAut.conjNormal g : MulAut N) *
      NormalConjugationEmbedding.quotientConjugation N (k : G ⧸ C) *
      (MulAut.conjNormal g : MulAut N)⁻¹
  rw [hk]
  simp only [map_mul, map_inv, NormalConjugationEmbedding.quotientConjugation_mk]

omit [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)] in
/-- The inverse automorphism action is exactly the actual minimal-center representation at q⁻¹. -/
theorem quotientInverse_eq (g : G) :
    (((characteristicQuotientAut (Subgroup.center N)
      (MulAut.conjNormal g : MulAut N)⁻¹).toMonoidHom.toAdditive).toZModLinearMap 2) =
      ρ ((QuotientGroup.mk' R g)⁻¹) := by
  rw [← map_inv (MulAut.conjNormal : G →* MulAut N) g,
    ← map_inv (QuotientGroup.mk' R) g]
  rfl

/-- Actual kernel coordinates transform by the checked inverse-precomposition formula. -/
theorem linearCoordinate_mk (g : G) (w : Additive K) :
    L (τ (QuotientGroup.mk' R g) w) =
      (L w).comp (ρ ((QuotientGroup.mk' R g)⁻¹)) := by
  change CentralAutomorphismTorsion.linearCoordinate N 2
      (Additive.ofMul (j ((τ (QuotientGroup.mk' R g) w).toMul))) =
    (CentralAutomorphismTorsion.linearCoordinate N 2 (Additive.ofMul (j w.toMul))).comp
      (ρ ((QuotientGroup.mk' R g)⁻¹))
  have hk := kernelToCentralAut_representation N hN hmin hnonabelian R hR g w.toMul
  simp only [ofMul_toMul] at hk
  rw [hk]
  have h := CentralAutomorphismEquivariance.linearCoordinate_conjugation N 2
    (ambientCenterFixer N hmin hnonabelian g) (j w.toMul)
  change CentralAutomorphismTorsion.linearCoordinate N 2
      (Additive.ofMul (CentralAutomorphismEquivariance.conjugation N
        (MulAut.conjNormal g) (j w.toMul))) =
    (CentralAutomorphismTorsion.linearCoordinate N 2 (Additive.ofMul (j w.toMul))).comp
      (((characteristicQuotientAut (Subgroup.center N)
        (MulAut.conjNormal g : MulAut N)⁻¹).toMonoidHom.toAdditive).toZModLinearMap 2) at h
  rw [quotientInverse_eq N hN hmin R hR g] at h
  exact h

/-- The concrete linear coordinate is an actual Q-intertwiner into the standard Hom representation. -/
def intertwiner : Representation.IntertwiningMap τ
    (TrivialTargetHomIsotypic.homRepresentation ρ Z) where
  toLinearMap := L
  isIntertwining' q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R q
    apply LinearMap.ext
    intro w
    change L (τ (QuotientGroup.mk' R g) w) =
      (L w).comp (ρ ((QuotientGroup.mk' R g)⁻¹))
    exact linearCoordinate_mk N hN hmin hnonabelian R hR g w

/-- Injectivity of the actual intertwiner is the previously proved injectivity of its coordinates. -/
theorem intertwiner_injective :
    Function.Injective (intertwiner N hN hmin hnonabelian R hR) :=
  MinimalConjugationModule.linearCoordinate_injective N hN hmin hnonabelian R hR

/-- Semisimplicity of this actual kernel module follows from its actual Hom embedding. -/
theorem isSemisimpleModule : IsSemisimpleModule (ZMod 2)[G ⧸ R] (τ).asModule := by
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  exact TrivialTargetHomIsotypic.isSemisimpleModule_of_injective ρ Z τ
    (intertwiner N hN hmin hnonabelian R hR)
    (intertwiner_injective N hN hmin hnonabelian R hR)

/-- Every simple constituent of the actual kernel is of actual dual-center type. -/
theorem isIsotypicOfType_dual :
    IsIsotypicOfType (ZMod 2)[G ⧸ R] (τ).asModule (Representation.dual ρ).asModule := by
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  exact TrivialTargetHomIsotypic.isIsotypicOfType_of_injective ρ Z τ
    (intertwiner N hN hmin hnonabelian R hR)
    (intertwiner_injective N hN hmin hnonabelian R hR)

omit [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)] in
/-- The proved self-duality is also an actual group-algebra linear equivalence of coefficient types. -/
def dualTypeEquiv : (Representation.dual ρ).asModule ≃ₗ[(ZMod 2)[G ⧸ R]] (ρ).asModule := by
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let e := minimalCenterSelfDual N hN hmin R hR hnonabelian
  let f := Representation.IntertwiningMap.equivLinearMapAsModule (Representation.dual ρ) ρ
    e.symm.toIntertwiningMap
  exact LinearEquiv.ofBijective f e.symm.toLinearEquiv.bijective

/-- Thus the kernel is actually isotypic of the original minimal-center representation. -/
theorem isIsotypicOfType :
    IsIsotypicOfType (ZMod 2)[G ⧸ R] (τ).asModule (ρ).asModule :=
  (isIsotypicOfType_dual N hN hmin hnonabelian R hR).of_linearEquiv_type
    (dualTypeEquiv N hN hmin hnonabelian R hR)

end Kourovka2135.MinimalConjugationCoordinates
