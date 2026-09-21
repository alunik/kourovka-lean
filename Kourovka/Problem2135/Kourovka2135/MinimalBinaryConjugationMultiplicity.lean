import Kourovka2135.MinimalConjugationCoordinates
import Kourovka2135.MinimalBinaryNonNaturalFiber
import Kourovka2135.IsotypicFrattiniMultiplicity
import Kourovka2135.IrreducibleExtensionKernel
import Kourovka2135.BinaryCentralRemainder

/-! A nonspecial minimal noncentral kernel over binary SL2 forces the
actual faithful conjugation kernel to be one simple copy. Consequently
R = N C_G(N). Every module, action and cohomology bound used here is
constructed from the given finite group; none is an additional premise.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalBinaryConjugationMultiplicity

open scoped IsMulCommutative MonoidAlgebra

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) [IsSimpleGroup (G ⧸ R)]
variable (hNR : N ≤ R) (hRΦ : R ≤ frattini G)
variable (hnonspecial : Subgroup.center N ≠ commutator N)
variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable (e : SLTwo.SL2 F ≃* (G ⧸ R))
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)

variable [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)]
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

local notation "K" => MinimalConjugationModule.Kernel N R
local notation "C" => MinimalConjugationModule.Centralizer N
local notation "ρ" => minimalCenterRepresentation N hN hmin R hR
local notation "τ" => MinimalConjugationModule.representation N hN hmin hnonabelian R hR
local notation "S" => MinimalConjugationModule.extension N hN hmin hnonabelian R hR

/-- The actual kernel is one copy of the actual minimal-center representation. -/
def equiv : Representation.Equiv τ ρ := by
  let : Nontrivial K := MinimalConjugationModule.kernel_nontrivial N hnonabelian R hNR
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let : IsSemisimpleModule (ZMod 2)[G ⧸ R] (τ).asModule :=
    MinimalConjugationCoordinates.isSemisimpleModule N hN hmin hnonabelian R hR
  have hH1 := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hmin R hR hnonabelian hRΦ hnonspecial
  have hH2 := BinarySLTwoGroupEquivCohomology.finrank_H2_le_endDegree_of_finrank_H1_ne_zero
    ρ e f hcard hf hH1
  exact IsotypicFrattiniMultiplicity.equivOfIsotypicFrattiniH2Bound τ ρ S
    (MinimalConjugationModule.compatibleAction N hN hmin hnonabelian R hR)
    (MinimalConjugationCoordinates.isIsotypicOfType N hN hmin hnonabelian R hR)
    (MinimalConjugationModule.extension_range_le_frattini N hN hmin hnonabelian R hR hRΦ)
    hH2

include hNR hRΦ hnonspecial e f hcard hf in
/-- Irreducibility is transported through the actual single-copy equivalence. -/
theorem isIrreducible : Representation.IsIrreducible τ := by
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let a := equiv N hN hmin hnonabelian R hR hNR hRΦ hnonspecial e f hcard hf
  let m := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ a.toIntertwiningMap
  let b := LinearEquiv.ofBijective m a.toLinearEquiv.bijective
  let : IsSimpleModule (ZMod 2)[G ⧸ R] (τ).asModule := IsSimpleModule.congr b
  exact (Representation.irreducible_iff_isSimpleModule_asModule τ).mpr inferInstance

include hN hmin hnonabelian hR hNR hRΦ hnonspecial e f hcard hf in
/-- The image of N is the entire actual faithful conjugation kernel. -/
theorem images_eq : N.map (QuotientGroup.mk' C) = R.map (QuotientGroup.mk' C) := by
  let : Representation.IsIrreducible τ :=
    isIrreducible N hN hmin hnonabelian R hR hNR hRΦ hnonspecial e f hcard hf
  have hle : N.map (QuotientGroup.mk' C) ≤ (S).inl.range := by
    change N.map (QuotientGroup.mk' C) ≤
      (NestedNormalExtension.extension C R
        (MinimalConjugationModule.centralizer_le N hN hmin hnonabelian R hR)).inl.range
    rw [NestedNormalExtension.extension_inl_range]
    exact Subgroup.map_mono hNR
  have hne : N.map (QuotientGroup.mk' C) ≠ ⊥ := by
    let : Nontrivial (MinimalConjugationModule.Kernel N N) :=
      MinimalConjugationModule.kernel_nontrivial N hnonabelian N le_rfl
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have h := IrreducibleExtensionKernel.eq_range_of_ne_bot 2 S τ
    (MinimalConjugationModule.compatibleAction N hN hmin hnonabelian R hR)
    (N.map (QuotientGroup.mk' C)) hle hne
  change N.map (QuotientGroup.mk' C) =
    (NestedNormalExtension.extension C R
      (MinimalConjugationModule.centralizer_le N hN hmin hnonabelian R hR)).inl.range at h
  rwa [NestedNormalExtension.extension_inl_range] at h

omit [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
include hN hmin hnonabelian hR hNR hRΦ hnonspecial e f hcard hf in
/-- The group-theoretic factorization has no module structure in its hypotheses. -/
theorem sup_centralizer_eq : N ⊔ C = R := by
  let : IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R) :=
    MinimalConjugationModule.kernel_isElementaryAbelian N hN hmin hnonabelian R hR
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  exact sup_eq_of_quotient_images_eq N R C
    (MinimalConjugationModule.centralizer_le N hN hmin hnonabelian R hR)
    (images_eq N hN hmin hnonabelian R hR hNR hRΦ hnonspecial e f hcard hf)

omit [IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
include hN hmin hnonabelian hR hNR hRΦ hnonspecial e f hcard hf in
/-- If its centralizer is central, this minimal subgroup is the whole radical. -/
theorem eq_of_centralizer_le_center (hC : C ≤ Subgroup.center G) : R = N :=
  normal_two_subgroup_eq_of_central_factor N R C hR
    (sup_centralizer_eq N hN hmin hnonabelian R hR hNR hRΦ hnonspecial e f hcard hf)
    hC F f hcard hf e

end Kourovka2135.MinimalBinaryConjugationMultiplicity
