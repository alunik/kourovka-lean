/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Kourovka2135.Hall
import Kourovka2135.Vendor.CFSG.Frattini.CoprimeAction
import Kourovka2135.Vendor.CFSG.Fitting.Centralizer

/-! Coprime Frattini lifting and the self-centralizing p-core in the soluble case. -/

namespace Kourovka2135.Soluble

universe u v

/-- Coprime automorphisms of a finite soluble group give `G = C_G(A)[G,A]`. -/
theorem fixedPoint_sup_commutator_eq_top
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G)
    (hcoprime : (Nat.card A).Coprime (Nat.card G)) :
    fixedPointSubgroup A G ⊔ commutatorAction A G = ⊤ := by
  exact fixedPointSubgroup_sup_commutatorAction_eq_top_of_fixedPointQuotientImage
    (fixedPointSubgroup_quotient_eq_map_of_solvable_coprime hsolv hcoprime)

/-- A coprime action on a finite p-group that is trivial modulo its Frattini subgroup
is trivial on the group. The quotient action is the canonical induced action. -/
theorem actsTrivially_of_trivial_frattini_quotient
    {R : Type u} {A : Type v} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [MulDistribMulAction A R]
    (hcoprime : (Nat.card A).Coprime (Nat.card R))
    (hquot :
      letI : MulDistribMulAction A (R ⧸ frattini R) :=
        quotientMulDistribMulAction (A := A) (G := R) (frattini R)
          (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
      ActsTrivially A (R ⧸ frattini R)) :
    ActsTrivially A R := by
  have : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
  exact actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top (p := p)
    (fixedPoint_sup_commutator_eq_top (by infer_instance) hcoprime) hquot

/-- If the p′-core of a finite soluble group is trivial, its p-core contains its
centralizer. This combines the proved Fitting identification and centralizer theorem. -/
theorem centralizer_pCore_le_of_pPrimeCore_eq_bot
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (p : ℕ) [Fact p.Prime] (hcore : pPrimeCore p G = ⊥) :
    Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G := by
  rw [← Fitting_eq_pcore G p hcore]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

end Kourovka2135.Soluble
