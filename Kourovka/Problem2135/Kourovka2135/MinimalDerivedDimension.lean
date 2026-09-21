import Kourovka2135.MinimalInvariantForms

/-! The dimension of the derived subgroup of a minimal nonabelian kernel
is at most that of the endomorphism space of its center quotient. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (p : ℕ) [Fact p.Prime]
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian p (commutator N)]

def scalarCommutatorIntertwinerMap :
    Module.Dual (ZMod p) (Additive (commutator N)) →ₗ[ZMod p]
      (normalQuotientRepresentation N (Subgroup.center N) p).IntertwiningMap
        (normalQuotientRepresentation N (Subgroup.center N) p).dual where
  toFun := minimalScalarCommutatorIntertwiner N hmin p
  map_add' f h := by
    ext x y
    rfl
  map_smul' a f := by
    ext x y
    rfl

theorem scalarCommutatorIntertwinerMap_injective (hnonabelian : ¬ IsMulCommutative N) :
    Function.Injective (scalarCommutatorIntertwinerMap N hmin p) := by
  have hzero : ∀ ell, scalarCommutatorIntertwinerMap N hmin p ell = 0 → ell = 0 := by
    intro ell hell
    by_contra hne
    have hex : ∃ a : N, a ∉ Subgroup.center N := by
      by_contra h
      push Not at h
      apply hnonabelian
      apply Subgroup.center_eq_top_iff.mp
      exact top_le_iff.mp (fun a _ => h a)
    obtain ⟨a, ha⟩ := hex
    have hz : Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) a) = 0 := by
      apply minimal_noncentral_scalarCommutatorForm_nondegenerate N hmin p ell hne
      intro y
      exact congrArg (fun f => f (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) a)) y) hell
    exact ha ((QuotientGroup.eq_one_iff _).mp hz)
  intro f h heq
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, heq, sub_self]

include hmin in
theorem minimal_derived_finrank_le_intertwiner_finrank [Finite G]
    (hnonabelian : ¬ IsMulCommutative N) :
    Module.finrank (ZMod p) (Additive (commutator N)) ≤
      Module.finrank (ZMod p)
        ((normalQuotientRepresentation N (Subgroup.center N) p).IntertwiningMap
          (normalQuotientRepresentation N (Subgroup.center N) p).dual) := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (scalarCommutatorIntertwinerMap_injective N hmin p hnonabelian)
  simpa only [Subspace.dual_finrank_eq] using hh

noncomputable def selfDualIntertwinerToEnd
    {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (e : ρ.Equiv ρ.dual) :
    ρ.IntertwiningMap ρ.dual →ₗ[k] ρ.IntertwiningMap ρ where
  toFun f := e.symm.toIntertwiningMap.comp f
  map_add' f h := by
    ext x
    exact map_add e.symm (f x) (h x)
  map_smul' a f := by
    ext x
    exact map_smul e.symm a (f x)

theorem selfDualIntertwinerToEnd_injective
    {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (e : ρ.Equiv ρ.dual) :
    Function.Injective (selfDualIntertwinerToEnd ρ e) := by
  intro f h he
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply e.symm.toLinearEquiv.injective
  exact congrArg (fun t : ρ.IntertwiningMap ρ => t x) he

include hmin in
theorem minimal_derived_finrank_le_endomorphism_finrank [Finite G]
    (hnonabelian : ¬ IsMulCommutative N) :
    Module.finrank (ZMod p) (Additive (commutator N)) ≤
      Module.finrank (ZMod p)
        ((normalQuotientRepresentation N (Subgroup.center N) p).IntertwiningMap
          (normalQuotientRepresentation N (Subgroup.center N) p)) := by
  have hDne : commutator N ≠ ⊥ := by
    intro hbot
    exact hnonabelian ((commutator_eq_bot_iff N).mp hbot)
  let : Nontrivial (commutator N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
  obtain ⟨t, ht⟩ := exists_ne (1 : commutator N)
  obtain ⟨ell, hellt⟩ := exists_linear_functional_ne_zero (K := ZMod p)
    (show Additive.ofMul t ≠ 0 from ht)
  have hell : ell ≠ 0 := by
    intro h
    exact hellt (congrArg (fun f : Module.Dual (ZMod p) (Additive (commutator N)) =>
      f (Additive.ofMul t)) h)
  let ρ := normalQuotientRepresentation N (Subgroup.center N) p
  let e := minimalScalarCommutatorEquiv N hmin p ell hell
  exact (minimal_derived_finrank_le_intertwiner_finrank N hmin p hnonabelian).trans
    (LinearMap.finrank_le_finrank_of_injective (selfDualIntertwinerToEnd_injective ρ e))

end Kourovka2135
