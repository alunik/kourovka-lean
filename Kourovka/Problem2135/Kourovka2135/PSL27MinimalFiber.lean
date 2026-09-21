import Kourovka2135.PSL27CohomologySupport
import Kourovka2135.BinaryAlternatingThree
import Kourovka2135.MinimalCenterSelfDual
import Kourovka2135.MinimalH1VanishFiber
import Kourovka2135.MinimalFaithful
import Kourovka2135.RepresentationGroupEquiv
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-! Full minimal nonabelian binary-kernel fibers for an actual PSL2(7) quotient.

The scalar commutator pairing is nondegenerate alternating, so its coefficient
space cannot have dimension three. The actual PSL2(7) H1 support theorem then
forces H1 to vanish. Actual self-duality supplies the required dual-H1
vanishing, and the checked minimal-kernel correction theorem fills every
commutator fiber. No good-class, central-cover or module-classification
hypothesis is supplied.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

include hN hmin in
/-- The actual nondegenerate scalar commutator pairing excludes dimension three. -/
theorem minimal_binary_center_finrank_ne_three (hnonabelian : ¬ IsMulCommutative N) :
    Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≠ 3 := by
  let : Group.IsNilpotent N := hN.isNilpotent
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  have hDne : commutator N ≠ ⊥ := by
    intro hbot
    exact hnonabelian ((commutator_eq_bot_iff N).mp hbot)
  let : Nontrivial (commutator N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
  obtain ⟨t, ht⟩ := exists_ne (1 : commutator N)
  obtain ⟨ell, hellt⟩ := exists_linear_functional_ne_zero (K := ZMod 2)
    (show Additive.ofMul t ≠ 0 from ht)
  have hell : ell ≠ 0 := by
    intro h
    exact hellt (congrArg (fun f : Module.Dual (ZMod 2) (Additive (commutator N)) =>
      f (Additive.ofMul t)) h)
  exact BinaryAlternatingThree.finrank_ne_three
    (scalarCommutatorForm (minimal_noncentral_commutator_le_internal_center N hmin) 2 ell)
    (scalarCommutatorForm_alternating _ 2 ell)
    (fun _ hx => minimal_noncentral_scalarCommutatorForm_nondegenerate N hmin 2 ell hell hx)

private theorem psl27_isSimpleGroup :
    IsSimpleGroup (OddPSLTwoProjectiveChart.Q (ZMod 7)) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' ⟨(2 : ZMod 7), by decide, by decide⟩

variable [Group.IsPerfect G]
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable (e : (G ⧸ R) ≃* OddPSLTwoProjectiveChart.Q (ZMod 7))

include hN hmin hR e

/-- The genuine quotient representation has vanishing dual H1 for PSL2(7). -/
theorem minimal_psl27_dual_h1_subsingleton (hnonabelian : ¬ IsMulCommutative N) :
    Subsingleton (groupCohomology
      (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1) := by
  let : IsSimpleGroup (OddPSLTwoProjectiveChart.Q (ZMod 7)) := psl27_isSimpleGroup
  let : IsSimpleGroup (G ⧸ R) := e.isSimpleGroup
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let σ : Representation (ZMod 2) (OddPSLTwoProjectiveChart.Q (ZMod 7))
      (Additive (N ⧸ Subgroup.center N)) := ρ.comp e.symm.toMonoidHom
  let : σ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e.symm
  have hfaith : Function.Injective σ :=
    (minimal_center_representation_injective_of_perfect N hN hmin hnonabelian R hR).comp
      e.symm.injective
  have hact : ¬ ∀ g : OddPSLTwoProjectiveChart.Q (ZMod 7), σ g = 1 := by
    intro h
    obtain ⟨g, hg⟩ := exists_ne (1 : OddPSLTwoProjectiveChart.Q (ZMod 7))
    apply hg
    apply hfaith
    rw [h g, map_one]
  have hglobal : σ.invariants = ⊥ :=
    PSL27CohomologySupport.invariants_eq_bot_of_nontrivial_action σ hact
  have hdim := minimal_binary_center_finrank_ne_three N hN hmin hnonabelian
  let : Subsingleton (groupCohomology (Rep.of σ) 1) := by
    apply not_nontrivial_iff_subsingleton.mp
    intro hn
    let := hn
    exact hdim (PSL27CohomologySupport.finrank_eq_three_of_H1_nontrivial σ hglobal)
  let c := RepresentationGroupEquiv.cohomologyIso ρ e.symm 1
  let : Subsingleton (groupCohomology (Rep.of ρ) 1) :=
    c.toLinearEquiv.symm.injective.subsingleton
  let d := minimalCenterSelfDualCohomologyIso N hN hmin R hR hnonabelian 1
  exact d.toLinearEquiv.symm.injective.subsingleton

/-- The actual minimal kernel is special, with no cohomology premise. -/
theorem minimal_psl27_center_eq_commutator (hnonabelian : ¬ IsMulCommutative N)
    (hRΦ : R ≤ frattini G) : Subgroup.center N = commutator N := by
  let := minimal_psl27_dual_h1_subsingleton N hN hmin R hR e hnonabelian
  exact minimal_center_eq_commutator_of_actual_dual_h1_vanishes
    N hN hnonabelian hmin R hR hRΦ

omit [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
/-- Every target in the actual nonabelian minimal commutator fiber is attained. -/
theorem exists_paperCommutator_mul_eq_of_minimal_psl27
    (hnonabelian : ¬ IsMulCommutative N) (hRΦ : R ≤ frattini G)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsSimpleGroup (OddPSLTwoProjectiveChart.Q (ZMod 7)) := psl27_isSimpleGroup
  let : IsSimpleGroup (G ⧸ R) := e.isSimpleGroup
  let := minimal_psl27_dual_h1_subsingleton N hN hmin R hR e hnonabelian
  exact exists_paperCommutator_mul_eq_of_minimal_actual_dual_h1_vanishes
    N hN hmin hnonabelian R hR hRΦ a b hgen hc t

omit [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
/-- The corresponding full generating-good-set preimage theorem. -/
theorem IsGeneratingGoodSet.preimage_quotient_of_minimal_psl27
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hRΦ : R ≤ frattini G) {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y)
    (hYnontrivial : ∀ t : G, QuotientGroup.mk' N t ∈ Y → QuotientGroup.mk' R t ≠ 1) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsSimpleGroup (OddPSLTwoProjectiveChart.Q (ZMod 7)) := psl27_isSimpleGroup
  let : IsSimpleGroup (G ⧸ R) := e.isSimpleGroup
  let := minimal_psl27_dual_h1_subsingleton N hN hmin R hR e hnonabelian
  exact IsGeneratingGoodSet.preimage_quotient_of_minimal_actual_dual_h1_vanishes
    N hN hmin hnonabelian hNΦ R hR hRΦ hY hYnontrivial

end Kourovka2135
