import Kourovka2135.OddPSLTwoGeneratingPowerBound
import Kourovka2135.OddPSLTwoSplitClassBound
import Kourovka2135.MinimalBinaryCorrectionBound
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-! Actual minimal nonabelian binary-kernel fibers over odd PSL2.
The general case uses generating conjugate-power witnesses for the output;
the split order-three case uses its actual torus calculation. The scalar
field, dual-cohomology equality and elementary-abelian structures are derived
from the given finite group and its minimal kernel. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open scoped IsMulCommutative
open OddPSLTwoProjectiveChart IrreducibleEndCohomology

variable (F : Type) [Field F] [Fintype F]
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
variable (e : (G ⧸ R) ≃* Q F)

include hN hmin hnonabelian hR hRΦ e

theorem exists_paperCommutator_mul_eq_of_minimal_odd_pslTwo_generating_powers
    (hodd : Odd (Fintype.card F)) (hsize : 17 ≤ Fintype.card F)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1)
    (α β : Q F) (hpair : Subgroup.closure ({α, β} : Set (Q F)) = ⊤)
    (m n : ℕ)
    (hα : IsConj α (e (QuotientGroup.mk' R (paperCommutator a b)) ^ m))
    (hβ : IsConj β (e (QuotientGroup.mk' R (paperCommutator a b)) ^ n))
    (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsPerfect (Q F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (Q F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [Nat.card_eq_fintype_card]
    omega)
  let : IsSimpleGroup (G ⧸ R) := e.isSimpleGroup
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let σ : Representation (ZMod 2) (Q F) (Additive (N ⧸ Subgroup.center N)) :=
    ρ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e.symm
  have hd := BinaryRepresentationCorrection.dual_finrank_eq_of_comp ρ e.symm
    (minimalCenterDualCohomology_finrank_eq N hN hmin R hR hnonabelian 1)
  have hs := OddPSLTwoGeneratingPowerBound.finite_bound F σ hd hodd hsize
    α β (e (QuotientGroup.mk' R (paperCommutator a b))) hpair m n hα hβ
  have hbnd := BinaryRepresentationCorrection.of_comp ρ e.symm
    (QuotientGroup.mk' R (paperCommutator a b)) hs
  exact exists_paperCommutator_mul_eq_of_minimal_binary_bound
    N hN hmin hnonabelian R hR hRΦ a b hgen hc hbnd t

theorem exists_paperCommutator_mul_eq_of_minimal_odd_pslTwo_split_three
    (hodd : Odd (Fintype.card F)) (hsize : 7 < Fintype.card F)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1)
    (r : Fˣ) (hr : orderOf r = 3)
    (hconj : IsConj (e (QuotientGroup.mk' R (paperCommutator a b)))
      (OddPSLTwoTorusMovingRank.projectiveTorusHom F r)) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Group.IsPerfect (Q F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (Q F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [Nat.card_eq_fintype_card]
    omega)
  let : IsSimpleGroup (G ⧸ R) := e.isSimpleGroup
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let σ : Representation (ZMod 2) (Q F) (Additive (N ⧸ Subgroup.center N)) :=
    ρ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e.symm
  have hd := BinaryRepresentationCorrection.dual_finrank_eq_of_comp ρ e.symm
    (minimalCenterDualCohomology_finrank_eq N hN hmin R hR hnonabelian 1)
  have hs : BinaryRepresentationCorrection.Bound σ
      (e (QuotientGroup.mk' R (paperCommutator a b))) := by
    apply BinaryRepresentationCorrection.of_closed σ _ hd
    exact OddPSLTwoSplitClassBound.alternative_of_isConj_order_three
      F (ClosedField σ) (extended σ) hodd hsize r hr _ hconj
  have hbnd := BinaryRepresentationCorrection.of_comp ρ e.symm
    (QuotientGroup.mk' R (paperCommutator a b)) hs
  exact exists_paperCommutator_mul_eq_of_minimal_binary_bound
    N hN hmin hnonabelian R hR hRΦ a b hgen hc hbnd t

end Kourovka2135
