import Kourovka2135.MinimalQuotientModules
import Kourovka2135.DualExtensionBound

/-! The center-excess bound for the actual minimal-kernel module, after
factoring its action through a normal Frattini p-subgroup. The cohomology is
of the dual of (N/N')/(Z(N)/N'), represented as an actual module quotient. -/

set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hRΦ : R ≤ frattini G)
variable [IsElementaryAbelian p (N ⧸ commutator N)]

def minimalAbelianizationRepresentation :
    Representation (ZMod p) (G ⧸ R) (Additive (N ⧸ commutator N)) :=
  quotientRepresentation (normalQuotientRepresentation N (commutator N) p) R (by
    intro r x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (commutator N) x.toMul
    change normalQuotientRepresentation N (commutator N) p (r : G)
      (Additive.ofMul x.toMul) = Additive.ofMul x.toMul
    rw [← ha]
    exact minimal_abelianization_frattini_pSubgroup_action
      (Fact.out : p.Prime) N hN hnonabelian hmin R hR hRΦ r a)

theorem minimalAbelianizationRepresentation_center_fixed :
    ∀ g x, x ∈ centerImageSubmodule N (commutator N) p →
      minimalAbelianizationRepresentation N hN hnonabelian hmin R hR hRΦ g x = x := by
  intro g x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R g
  exact centerImageSubmodule_fixed N (commutator N)
    (minimal_noncentral_center_le N hnonabelian hmin) p a x hx

theorem minimalAbelianizationRepresentation_dual_invariants_eq_bot
    (hnoncentral : ¬ N ≤ Subgroup.center G) :
    (minimalAbelianizationRepresentation N hN hnonabelian hmin R hR hRΦ).dual.invariants = ⊥ := by
  apply quotientRepresentation_dual_invariants_eq_bot
  exact normal_quotient_dual_invariants_eq_bot N (commutator N)
    (commutator_eq_self_of_minimal_noncentral N hnoncentral hmin) p

theorem minimal_center_excess_finrank_le_h1
    (hnoncentral : ¬ N ≤ Subgroup.center G) :
    let ρ := minimalAbelianizationRepresentation N hN hnonabelian hmin R hR hRΦ
    let W := centerImageSubmodule N (commutator N) p
    Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (groupCohomology
      (Rep.of (ρ.quotient W (fixedSubmoduleInvariant ρ W
        (minimalAbelianizationRepresentation_center_fixed N hN hnonabelian hmin R hR hRΦ))).dual) 1) := by
  dsimp only
  let σ := minimalAbelianizationRepresentation N hN hnonabelian hmin R hR hRΦ
  let W := centerImageSubmodule N (commutator N) p
  let A := Rep.of (σ.quotient W (fixedSubmoduleInvariant σ W
    (minimalAbelianizationRepresentation_center_fixed N hN hnonabelian hmin R hR hRΦ))).dual
  let : Finite (Additive (N ⧸ commutator N) ⧸ W) :=
    Finite.of_surjective W.mkQ W.mkQ_surjective
  let : Finite A := Finite.of_injective
    (fun f : Module.Dual (ZMod p) (Additive (N ⧸ commutator N) ⧸ W) =>
      (fun x => f x)) DFunLike.coe_injective
  let : Finite (groupCohomology A 1) := GroupCohomology.finite_h1 A
  let : FiniteDimensional (ZMod p) (groupCohomology A 1) := inferInstance
  exact fixed_submodule_finrank_le_h1_dual_quotient _ _
    (minimalAbelianizationRepresentation_center_fixed N hN hnonabelian hmin R hR hRΦ)
    (minimalAbelianizationRepresentation_dual_invariants_eq_bot
      N hN hnonabelian hmin R hR hRΦ hnoncentral)

end Kourovka2135
