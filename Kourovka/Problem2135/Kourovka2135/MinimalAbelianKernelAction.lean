import Kourovka2135.FrattiniModuleAction
import Kourovka2135.NormalPSubgroupRepresentation
import Kourovka2135.MinimalKernelAbelianization
import Kourovka2135.NormalQuotientRepresentation
import Mathlib.RepresentationTheory.Invariants
import Mathlib.FieldTheory.Finiteness

/-! Frattini p-subgroups centralize an abelian minimal noncentral p-kernel.

The actual module is Additive N, and its trivial submodule is the fixed space
of ambient conjugation: exactly N intersect Z(G).  It is not the internal
center of N, which is all of N in this case. Minimality makes the quotient
simple, the normal p-subgroup acts trivially on that quotient, and the
existing Frattini functional-stabilizer argument removes the remaining
central deviation. No splitting or representation-classification premise
is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalAbelianKernelAction

open scoped IsMulCommutative

section SimpleQuotient

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Finite M]

/-- A normal p-subgroup has only deviations in W when M/W is simple.
The quotient representation and its irreducibility are actually constructed. -/
theorem difference_mem_of_simple_quotient
    (ρ : Representation (ZMod p) G M) (W : Submodule (ZMod p) M)
    (hW : ∀ g, W ≤ W.comap (ρ g))
    (hirr : ∀ U : Submodule (ZMod p) M, W ≤ U →
      (∀ g x, x ∈ U → ρ g x ∈ U) → U = W ∨ U = ⊤)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (r : R) (x : M) :
    ρ (r : G) x - x ∈ W := by
  let : Finite (M ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  let σ := Representation.quotient ρ W hW
  have hσ : ∀ U : Submodule (ZMod p) (M ⧸ W),
      (∀ g y, y ∈ U → σ g y ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let U' := U.comap W.mkQ
    have hWU : W ≤ U' := W.le_comap_mkQ U
    have hU' : ∀ g y, y ∈ U' → ρ g y ∈ U' := by
      intro g y hy
      change σ g (W.mkQ y) ∈ U
      exact hU g (W.mkQ y) hy
    rcases hirr U' hWU hU' with heq | heq
    · left
      apply bot_unique
      intro y hy
      obtain ⟨a, rfl⟩ := W.mkQ_surjective y
      have ha : a ∈ U' := hy
      rw [heq] at ha
      change W.mkQ a = 0
      have hk : a ∈ LinearMap.ker W.mkQ := by
        simpa only [Submodule.ker_mkQ] using ha
      exact hk
    · right
      apply top_le_iff.mp
      intro y _
      obtain ⟨a, rfl⟩ := W.mkQ_surjective y
      have ha : a ∈ U' := by rw [heq]; trivial
      exact ha
  have hq : σ (r : G) (W.mkQ x) = W.mkQ x := by
    rcases subsingleton_or_nontrivial (M ⧸ W) with ht | ht
    · let := ht
      exact Subsingleton.elim _ _
    · let := ht
      let : Fintype (M ⧸ W) := Fintype.ofFinite _
      have hcard : p ∣ Nat.card (M ⧸ W) := by
        rw [Nat.card_eq_fintype_card,
          Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
        exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := M ⧸ W)).ne'
      exact normal_pSubgroup_acts_trivially_of_invariant_submodules
        (Fact.out : p.Prime) σ hσ hcard R hR r (W.mkQ x)
  have heq : W.mkQ (ρ (r : G) x) = W.mkQ x := hq
  have hk : ρ (r : G) x - x ∈ LinearMap.ker W.mkQ := by
    change W.mkQ (ρ (r : G) x - x) = 0
    rw [map_sub, heq, sub_self]
  simpa only [Submodule.ker_mkQ] using hk

end SimpleQuotient

section ActualConjugation

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
variable (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p N]

/-- The actual conjugation representation on the elementary abelian N itself. -/
def conjugationRepresentation : Representation (ZMod p) G (Additive N) where
  toFun g := ((MulAut.conjNormal g : MulAut N).toMonoidHom.toAdditive).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change (MulAut.conjNormal (1 : G) : MulAut N) x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change (MulAut.conjNormal (a * b) : MulAut N) x.toMul =
      MulAut.conjNormal a (MulAut.conjNormal b x.toMul)
    rw [map_mul]
    rfl

@[simp] theorem conjugationRepresentation_apply (g : G) (x : N) :
    conjugationRepresentation N p g (Additive.ofMul x) =
      Additive.ofMul (MulAut.conjNormal g x) := rfl

/-- The trivial submodule is the actual intersection with the ambient center. -/
def ambientFixedSubmodule : Submodule (ZMod p) (Additive N) :=
  Representation.invariants (conjugationRepresentation N p)

/-- Membership in the fixed submodule has the intended ambient-group meaning. -/
theorem mem_ambientFixedSubmodule_iff (x : N) :
    Additive.ofMul x ∈ ambientFixedSubmodule N p ↔
      (x : G) ∈ Subgroup.center G := by
  constructor
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro g
    have h : (MulAut.conjNormal g : MulAut N) x = x := hx g
    have he := congrArg Subtype.val h
    change g * (x : G) * g⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  · intro hx g
    change (MulAut.conjNormal g : MulAut N) x = x
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = x
    rw [Subgroup.mem_center_iff.mp hx g]
    simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Minimal noncentrality gives the exact simple-quotient criterion above N∩Z(G). -/
theorem invariant_submodule_eq_fixed_or_top
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (U : Submodule (ZMod p) (Additive N))
    (hWU : ambientFixedSubmodule N p ≤ U)
    (hU : ∀ g x, x ∈ U → conjugationRepresentation N p g x ∈ U) :
    U = ambientFixedSubmodule N p ∨ U = ⊤ := by
  let K : Subgroup N := U.toAddSubgroup.toSubgroup'
  let H : Subgroup G := K.map N.subtype
  have hnormal : H.Normal := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ g
    refine ⟨MulAut.conjNormal g x, ?_, rfl⟩
    exact hU g (Additive.ofMul x) hx
  have hHN : H ≤ N := Subgroup.map_subtype_le K
  by_cases heq : H = N
  · right
    apply top_le_iff.mp
    intro x _
    have hx : (x.toMul : G) ∈ H := by rw [heq]; exact x.toMul.property
    obtain ⟨a, ha, he⟩ := hx
    have hae : a = x.toMul := Subtype.ext he
    subst a
    exact ha
  · left
    apply le_antisymm ?_ hWU
    have hHC := hmin H hnormal (lt_of_le_of_ne hHN heq)
    intro x hx
    apply (mem_ambientFixedSubmodule_iff N p x.toMul).mpr
    exact hHC (Subgroup.mem_map_of_mem N.subtype hx)

end ActualConjugation

section MinimalKernel

variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

/-- The checked abelianization power theorem gives exponent p on an abelian N. -/
theorem isElementaryAbelian_of_minimal_noncentral
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hN : IsPGroup p N) (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G) :
    IsElementaryAbelian p N := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  have hx := minimal_noncentral_prime_power_mem_commutator hp N hN hnoncentral hmin x
  rw [commutator_eq_bot] at hx
  exact Subgroup.mem_bot.mp hx

/-- A normal Frattini p-subgroup centralizes the actual abelian minimal noncentral N.
All elementary-abelian, action, fixed-space and simple-quotient data are derived internally. -/
theorem frattini_pSubgroup_centralizes
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] [IsMulCommutative N]
    (hN : IsPGroup p N) (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hRΦ : R ≤ frattini G)
    (r : R) (x : N) : (MulAut.conjNormal (r : G) : MulAut N) x = x := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p N :=
    isElementaryAbelian_of_minimal_noncentral hp N hN hnoncentral hmin
  let ρ := conjugationRepresentation N p
  let W := ambientFixedSubmodule N p
  have hW : ∀ g y, y ∈ W → ρ g y = y := fun g y hy => hy g
  have hWstable : ∀ g, W ≤ W.comap (ρ g) := by
    intro g y hy
    change ρ g y ∈ W
    rw [hW g y hy]
    exact hy
  have hirr := invariant_submodule_eq_fixed_or_top N p hmin
  have hRdiff : ∀ (a : R) y, ρ (a : G) y - y ∈ W :=
    difference_mem_of_simple_quotient ρ W hWstable hirr R hR
  exact frattini_trivial_action_of_simple_quotient ρ W hW hirr R hRΦ hRdiff r
    (Additive.ofMul x)

end MinimalKernel

end Kourovka2135.MinimalAbelianKernelAction
