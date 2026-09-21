import Kourovka2135.PPrimeCoreQuotient
import Kourovka2135.VerbalQuotientComplement

/-! Closure properties of normal p-complements, with their witnesses retained. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {H : Type v} [Group G] [Group H] {p : ℕ}

theorem HasNormalPComplement.of_surjective_coprime_kernel [Finite G] [Finite H]
    (hp : p.Prime) (f : G →* H) (hf : Function.Surjective f)
    (hker : (Nat.card f.ker).Coprime p) (hH : HasNormalPComplement p H) :
    HasNormalPComplement p G := by
  obtain ⟨N, hN, hNcard, n, hn⟩ := hH
  let : N.Normal := hN
  let q := (QuotientGroup.mk' N).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective N).comp hf
  have hqker : q.ker = N.comap f := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hcard : (Nat.card q.ker).Coprime p := by
    rw [hqker]
    exact (coprime_card_comap_of_surjective f hf N hker.symm hNcard.symm).symm
  have hQ : IsPGroup p (H ⧸ N) := IsPGroup.of_card (by
    rw [← N.index_eq_card]
    exact hn)
  exact hasNormalPComplement_of_surjective_to_pGroup hp q hq hcard hQ

theorem HasNormalPComplement.of_injective [Finite G] [Finite H]
    (hp : p.Prime) (hH : HasNormalPComplement p H)
    (f : G →* H) (hf : Function.Injective f) : HasNormalPComplement p G := by
  obtain ⟨N, hN, hNcard, n, hn⟩ := hH
  let : N.Normal := hN
  let q := (QuotientGroup.mk' N).comp f
  have hQ : IsPGroup p (H ⧸ N) := IsPGroup.of_card (by
    rw [← N.index_eq_card]
    exact hn)
  let i : q.rangeRestrict.ker →* N := {
    toFun := fun x => ⟨f (x : G), by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : N => (z : H)) hxy
  have hker : (Nat.card q.rangeRestrict.ker).Coprime p :=
    Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_injective i hi) hNcard
  exact hasNormalPComplement_of_surjective_to_pGroup hp q.rangeRestrict
    q.rangeRestrict_surjective hker (hQ.to_subgroup q.range)

theorem HasNormalPComplement.subgroup [Finite G]
    (hp : p.Prime) (hG : HasNormalPComplement p G) (H : Subgroup G) :
    HasNormalPComplement p H := hG.of_injective hp H.subtype H.subtype_injective

theorem HasNormalPComplement.of_equiv [Finite G] [Finite H]
    (hp : p.Prime) (hG : HasNormalPComplement p G) (e : G ≃* H) :
    HasNormalPComplement p H := hG.of_injective hp e.symm.toMonoidHom e.symm.injective

/-- A normal p-complement of a verbal quotient lifts across a prime-to-p kernel. -/
theorem verbalSubgroup_hasNormalPComplement_of_quotient [Finite G]
    (w : OuterWord) (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (hN : (Nat.card N).Coprime p)
    (hQ : HasNormalPComplement p (w.verbalSubgroup (G ⧸ N))) :
    HasNormalPComplement p (w.verbalSubgroup G) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let D := w.verbalSubgroup G
  let f : D →* D.map q := q.subgroupMap D
  have hIm : HasNormalPComplement p (D.map q) := by
    change HasNormalPComplement p ((w.verbalSubgroup G).map q)
    rw [w.map_verbalSubgroup_eq q (QuotientGroup.mk'_surjective N)]
    exact hQ
  let i : f.ker →* N := {
    toFun := fun x => ⟨(x.1 : G), by
      apply (QuotientGroup.eq_one_iff (N := N) (x.1 : G)).mp
      exact congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) hxy
  have hker : (Nat.card f.ker).Coprime p :=
    Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_injective i hi) hN
  exact HasNormalPComplement.of_surjective_coprime_kernel hp f
    (q.subgroupMap_surjective D) hker hIm

end Kourovka2135
