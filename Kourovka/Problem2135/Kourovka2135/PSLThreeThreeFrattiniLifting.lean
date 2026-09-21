import Kourovka2135.PSL33GoodSets
import Kourovka2135.PSLThreeThreeBinaryCentralKernel
import Kourovka2135.RepresentationGroupEquiv
import Kourovka2135.MinimalH1VanishFiber
import Kourovka2135.MinimalCenterSelfDual
import Kourovka2135.MinimalIrreducible
import Kourovka2135.MinimalMovingRankCriterion
import Kourovka2135.CoprimeFiber
import Kourovka2135.GoodSetEquiv
import Kourovka2135.MinimalNoncentral

/-! Conditional structural lifting for the binary PSL3(F3) branch.

Exactly one representation-theoretic boundary remains explicit:
`BinaryModuleBound`, on actual finite irreducible binary representations
of the actual projective group whose first cohomology has the same dimension
as that of the dual. The actual minimal-center representation satisfies this
equality by its proved self-duality. No center-field degree is assumed to be one.
The elementary group, cohomology-transport, correction, and Frattini-induction
arguments below are intended to discharge all other family obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeFrattiniLifting

open scoped IsMulCommutative
open PSL33GoodSets

/-- The sole outstanding representation input, under the numerical dual-H1
equality supplied by the actual minimal-center representation. The vanishing
alternative is actual subsingleton cohomology, and the rank alternative uses
the actual commuting-endomorphism space and actual dual first cohomology. -/
def BinaryModuleBound : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) Q V) [ρ.IsIrreducible],
    Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) →
    ∀ (g : Q), orderOf g = 13 →
    Subsingleton (groupCohomology (Rep.of ρ.dual) 1) ∨
      2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) +
        2 * Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) ≤
          Module.finrank (ZMod 2) (ρ g - LinearMap.id).range

/-- Every member of the actual good class has exact order thirteen. -/
theorem orderOf_mem_Y13 {g : Q} (hg : g ∈ Y13) : orderOf g = 13 := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨c, hc⟩ := isConj_iff.mp (ha : IsConj SL33Witnesses.a13 a)
  have hqc : q c * y13 = q a * q c := by
    change q c * q SL33Witnesses.a13 = q a * q c
    simpa only [map_mul] using congrArg q (mul_inv_eq_iff_eq_mul.mp hc)
  exact (SemiconjBy.orderOf_eq (q c) hqc).symm.trans order_y13

/-- Pulling back through a group equivalence commutes with the actual dual. -/
theorem dual_comp_equiv {H V : Type} [Group H] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) H V) (e : Q ≃* H) :
    Representation.dual (ρ.comp e.toMonoidHom) = ρ.dual.comp e.toMonoidHom := by
  ext g ell v
  change ell (ρ (e g⁻¹) v) = ell (ρ ((e g)⁻¹) v)
  rw [map_inv]

/-- The one explicit module bound transports to any actual isomorphic group. -/
theorem bound_of_equiv (hmodule : BinaryModuleBound)
    {H V : Type} [Group H] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) H V) [ρ.IsIrreducible]
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1)) (e : Q ≃* H)
    (g : H) (hg : orderOf g = 13) :
    Subsingleton (groupCohomology (Rep.of ρ.dual) 1) ∨
      2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) +
        2 * Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) ≤
          Module.finrank (ZMod 2) (ρ g - LinearMap.id).range := by
  let σ : Representation (ZMod 2) Q V := ρ.comp e.toMonoidHom
  let : σ.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ e
  have hg' : orderOf (e.symm g) = 13 := by rw [e.symm.orderOf_eq, hg]
  have hd : σ.dual = ρ.dual.comp e.toMonoidHom := dual_comp_equiv ρ e
  have hdual' : Module.finrank (ZMod 2) (groupCohomology (Rep.of σ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of σ) 1) := by
    calc
      _ = Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) := by
        rw [hd]
        exact RepresentationGroupEquiv.finrank_cohomology_comp ρ.dual e 1
      _ = Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) := hdual
      _ = _ := (RepresentationGroupEquiv.finrank_cohomology_comp ρ e 1).symm
  have hh := hmodule V σ hdual' (e.symm g) hg'
  rcases hh with hz | hr
  · left
    rw [hd] at hz
    let := hz
    exact (RepresentationGroupEquiv.cohomologyIso ρ.dual e 1).toLinearEquiv.symm.injective.subsingleton
  · right
    have he := RepresentationGroupEquiv.finrank_endomorphism_comp ρ e
    have hc := RepresentationGroupEquiv.finrank_cohomology_comp ρ.dual e 1
    change Module.finrank (ZMod 2) (σ.IntertwiningMap σ) = _ at he
    rw [hd, he, hc] at hr
    change _ ≤ Module.finrank (ZMod 2) (ρ (e (e.symm g)) - LinearMap.id).range at hr
    rwa [e.apply_symm_apply] at hr

section MinimalFiber
variable (hmodule : BinaryModuleBound)
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
variable [IsSimpleGroup (G ⧸ R)]
variable (e : (G ⧸ R) ≃* Q)

include hmodule hN hmin hnonabelian hR hRΦ e

/-- The module boundary implies the actual full correction fiber, including
nonspecial kernels and arbitrarily large commuting-endomorphism fields. -/
theorem full_fiber (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : orderOf (QuotientGroup.mk' R (paperCommutator a b)) = 13) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (h y.property) x)⟩⟩
  let : IsElementaryAbelian 2 (N ⧸ commutator N) :=
    minimal_noncentral_abelianization_isElementaryAbelian Nat.prime_two N hN hnc hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  have hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1) :=
    minimalCenterDualCohomology_finrank_eq N hN hmin R hR hnonabelian 1
  rcases bound_of_equiv hmodule ρ hdual e.symm
      (QuotientGroup.mk' R (paperCommutator a b)) hc with hz | hr
  · let := hz
    apply exists_paperCommutator_mul_eq_of_minimal_actual_dual_h1_vanishes
      N hN hmin hnonabelian R hR hRΦ a b hgen _ t
    intro he
    rw [he, orderOf_one] at hc
    omega
  · exact exists_paperCommutator_mul_eq_of_minimal_end_h1_rank
      N hN hmin hnonabelian R hR hRΦ a b hgen hr t

/-- The whole good-set preimage lifts through the actual minimal kernel. -/
theorem preimage_good (hNΦ : N ≤ frattini G)
    {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y)
    (hYorder : ∀ t : G, QuotientGroup.mk' N t ∈ Y →
      orderOf (QuotientGroup.mk' R t) = 13) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  let qN := QuotientGroup.mk' N
  intro t ht
  obtain ⟨α, hα, β, hβ, hαβ, hgen⟩ := hY (qN t) ht
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N α
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective N β
  change qN a = α at ha
  change qN b = β at hb
  have habgen : Subgroup.closure ({a, b} : Set G) = ⊤ := by
    apply closure_pair_eq_top_of_quotient_generation N hNΦ
    change Subgroup.closure ({qN a, qN b} : Set (G ⧸ N)) = ⊤
    rw [ha, hb]
    exact hgen
  have hc : qN (paperCommutator a b) = qN t := by
    simpa only [paperCommutator, map_mul, map_inv, ha, hb] using hαβ
  have hco := hYorder (paperCommutator a b) (hc.symm ▸ ht)
  have hr : (paperCommutator a b)⁻¹ * t ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change qN ((paperCommutator a b)⁻¹ * t) = 1
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  obtain ⟨u, v, huv⟩ := full_fiber hmodule N hN hmin hnonabelian R hR hRΦ e
    a b habgen hco (⟨(paperCommutator a b)⁻¹ * t, hr⟩ : N)
  have hqu : qN (u : G) = 1 := (QuotientGroup.eq_one_iff _).mpr u.property
  have hqv : qN (v : G) = 1 := (QuotientGroup.eq_one_iff _).mpr v.property
  have hau : qN (a * u) = α := by rw [map_mul, hqu, mul_one]; exact ha
  have hbv : qN (b * v) = β := by rw [map_mul, hqv, mul_one]; exact hb
  refine ⟨a * u, ?_, b * v, ?_, ?_, ?_⟩
  · change qN (a * u) ∈ Y
    rw [hau]
    exact hα
  · change qN (b * v) ∈ Y
    rw [hbv]
    exact hβ
  · simpa only [Subgroup.coe_mk, mul_inv_cancel_left] using huv
  · apply closure_pair_eq_top_of_quotient_generation N hNΦ
    change Subgroup.closure ({qN (a * u), qN (b * v)} : Set (G ⧸ N)) = ⊤
    rw [hau, hbv]
    exact hgen

end MinimalFiber

/-- Complete structural induction, conditional only on the displayed module
bound (and the actual simple-quotient structure used by the special fiber). -/
theorem preimage_Y13_good (hmodule : BinaryModuleBound) [IsSimpleGroup Q]
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hRΦ : pi.ker ≤ frattini G) :
    IsGeneratingGoodSet (pi ⁻¹' Y13) := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (A : Type) [Group A] [Finite A] [Group.IsPerfect A], Nat.card A = n →
      ∀ pi : A →* Q, Function.Surjective pi →
        IsPGroup 2 pi.ker → pi.ker ≤ frattini A → IsGeneratingGoodSet (pi ⁻¹' Y13)
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A _ _ _ hAcard pi hpi hR hRΦ
    let e := QuotientGroup.quotientKerEquivOfSurjective pi hpi
    let : IsSimpleGroup (A ⧸ pi.ker) := e.isSimpleGroup
    by_cases hcentral : pi.ker ≤ Subgroup.center A
    · have hbot := PSLThreeThreeBinaryCentralKernel.ker_eq_bot pi hpi hR hcentral
      exact good13.preimage_of_bijective pi
        ⟨(MonoidHom.ker_eq_bot_iff pi).mp hbot, hpi⟩
    obtain ⟨N, hNR, hnormal, hnc, hmin⟩ := exists_minimal_normal_noncentral pi.ker hcentral
    let : N.Normal := hnormal
    let qN := QuotientGroup.mk' N
    let pi' := QuotientGroup.lift N pi hNR
    have hpi' : Function.Surjective pi' :=
      QuotientGroup.lift_surjective_of_surjective N pi hpi hNR
    have hker : pi'.ker = pi.ker.map qN := QuotientGroup.ker_lift N pi hNR
    have hR' : IsPGroup 2 pi'.ker := by rw [hker]; exact hR.map qN
    have hΦ' : pi'.ker ≤ frattini (A ⧸ N) := by
      rw [hker]
      exact Subgroup.map_le_iff_le_comap.mpr
        (hRΦ.trans (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective N)))
    have hNne : N ≠ ⊥ := fun h => hnc (h ▸ bot_le)
    have hlt : Nat.card (A ⧸ N) < n := by
      rw [← hAcard]
      have hn : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
      have hpos : 0 < Nat.card (A ⧸ N) := Nat.card_pos
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A) (s := N)
      nlinarith
    have hi := ih (Nat.card (A ⧸ N)) hlt (A ⧸ N) rfl pi' hpi' hR' hΦ'
    change IsGeneratingGoodSet (qN ⁻¹' (pi' ⁻¹' Y13))
    by_cases hab : IsMulCommutative N
    · let := hab
      exact hi.preimage_quotient_of_abelian N (hNR.trans hRΦ)
        (commutator_eq_self_of_minimal_noncentral N hnc hmin)
    · apply preimage_good hmodule N (hR.to_le hNR) hmin hab pi.ker hR hRΦ e
        (hNR.trans hRΦ) hi
      intro t ht
      have horder := orderOf_mem_Y13 ht
      change orderOf (e (QuotientGroup.mk' pi.ker t)) = 13 at horder
      rwa [e.orderOf_eq] at horder
  exact main (Nat.card G) G rfl pi hpi hR hRΦ

end Kourovka2135.PSLThreeThreeFrattiniLifting
