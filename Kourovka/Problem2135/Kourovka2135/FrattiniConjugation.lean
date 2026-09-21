import Kourovka2135.SolubleStructure
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on a normal p-subgroup's Frattini quotient

The homomorphism uses left conjugation. Inner conjugations by the p-subgroup
act trivially on this abelian quotient. Coprime Frattini lifting then detects
centralization of the original, possibly nonabelian, p-subgroup.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

abbrev FrattiniQuotient (P : Subgroup G) := P ⧸ frattini P

noncomputable def frattiniConj (P : Subgroup G) [P.Normal] :
    G →* MulAut (FrattiniQuotient P) := by
  letI : MulDistribMulAction G P :=
    MulDistribMulAction.compHom P (MulAut.conjNormal : G →* MulAut P)
  letI : MulDistribMulAction G (FrattiniQuotient P) :=
    quotientMulDistribMulAction (A := G) (frattini P)
      (isInvariant_of_characteristic (A := G) (G := P) (frattini P))
  exact MulDistribMulAction.toMulAut G (FrattiniQuotient P)

theorem frattiniConj_apply_mk (P : Subgroup G) [P.Normal] (g : G) (t : P) :
    frattiniConj P g ((QuotientGroup.mk' (frattini P)) t) =
      (QuotientGroup.mk' (frattini P)) (MulAut.conjNormal g t) := by
  rfl

theorem frattiniQuotient_isMulCommutative [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Subgroup G) (hP : IsPGroup p P) :
    IsMulCommutative (FrattiniQuotient P) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p P) := ⟨hP⟩
  exact (isElementaryAbelian_quotient_frattini (R := P) (p := p)).toIsMulCommutative

theorem frattiniQuotient_isPGroup
    (p : ℕ) (P : Subgroup G) (hP : IsPGroup p P) :
    IsPGroup p (FrattiniQuotient P) :=
  hP.of_surjective (QuotientGroup.mk' (frattini P)) (QuotientGroup.mk'_surjective _)

open scoped IsMulCommutative in
theorem frattiniConj_eq_one_of_mem [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    {u : G} (hu : u ∈ P) : frattiniConj P u = 1 := by
  let : IsMulCommutative (FrattiniQuotient P) := frattiniQuotient_isMulCommutative p hp P hP
  apply MulEquiv.ext
  intro v
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
  rw [frattiniConj_apply_mk]
  have heq : MulAut.conjNormal u t = (⟨u, hu⟩ : P) * t * (⟨u, hu⟩ : P)⁻¹ := rfl
  rw [heq, map_mul, map_mul, map_inv]
  change _ = (QuotientGroup.mk' (frattini P)) t
  simp [mul_comm, mul_assoc]

theorem frattiniConj_conjugate_eq [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    {u : G} (hu : u ∈ P) (a : G) :
    frattiniConj P (u⁻¹ * a * u) = frattiniConj P a := by
  simp only [map_mul, map_inv, frattiniConj_eq_one_of_mem p hp P hP hu,
    inv_one, one_mul, mul_one]

/-- Triviality on the Frattini quotient detects a coprime conjugation action. -/
theorem centralizes_of_frattiniConj_eq_one [Finite G]
    (p : ℕ) (hp : p.Prime) (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    {x : G} (hxp : ¬ p ∣ orderOf x) (hquot : frattiniConj P x = 1) :
    ∀ t ∈ P, Commute t x := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let A := Subgroup.zpowers x
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P
    ((MulAut.conjNormal : G →* MulAut P).comp A.subtype)
  have hcop : (Nat.card A).Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    change (Nat.card (Subgroup.zpowers x)).Coprime (p ^ k)
    rw [Nat.card_zpowers]
    exact (hp.coprime_iff_not_dvd.mpr hxp).symm.pow_right k
  have hker : A ≤ (frattiniConj P).ker := Subgroup.zpowers_le.mpr hquot
  have htriv := Soluble.actsTrivially_of_trivial_frattini_quotient
    (R := P) (A := A) (p := p) hcop (by
      let : MulDistribMulAction A (FrattiniQuotient P) :=
        quotientMulDistribMulAction (A := A) (G := P) (frattini P)
          (isInvariant_of_characteristic (A := A) (G := P) (frattini P))
      intro a v
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) v
      change (QuotientGroup.mk' (frattini P)) (MulAut.conjNormal (a : G) t) =
        (QuotientGroup.mk' (frattini P)) t
      rw [← frattiniConj_apply_mk]
      have ha : frattiniConj P (a : G) = 1 := hker a.property
      rw [ha]
      rfl)
  intro t ht
  have heq := congrArg Subtype.val (htriv (⟨x, Subgroup.mem_zpowers x⟩ : A) (⟨t, ht⟩ : P))
  change x * t * x⁻¹ = t at heq
  change t * x = x * t
  exact ((mul_inv_eq_iff_eq_mul).mp heq).symm

end Kourovka2135
