import Kourovka2135.Quotient
import Mathlib.GroupTheory.Index

/-!
# Pulling a normal complement back from a verbal quotient

A surjection onto a finite p-group with p′-kernel supplies a normal
p-complement directly, using the kernel as its witness.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem hasNormalPComplement_of_surjective_to_pGroup [Finite G] [Finite H]
    {p : ℕ} (hp : p.Prime) (f : G →* H) (hf : Function.Surjective f)
    (hker : (Nat.card f.ker).Coprime p) (hH : IsPGroup p H) :
    HasNormalPComplement p G := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  refine ⟨f.ker, inferInstance, hker, n, ?_⟩
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top, hn]

/-- A p′-kernel quotient whose verbal subgroup is a p-group proves the
normal p-complement conclusion for the original verbal subgroup. -/
theorem verbalSubgroup_hasNormalPComplement_of_quotient_isPGroup [Finite G]
    (w : OuterWord) {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (hN : (Nat.card N).Coprime p) (hQ : IsPGroup p (w.verbalSubgroup (G ⧸ N))) :
    HasNormalPComplement p (w.verbalSubgroup G) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let D := w.verbalSubgroup G
  let f : D →* D.map q := q.subgroupMap D
  have hIm : IsPGroup p (D.map q) := by
    change IsPGroup p ((w.verbalSubgroup G).map q)
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
  exact hasNormalPComplement_of_surjective_to_pGroup hp f
    (q.subgroupMap_surjective D) hker hIm

end Kourovka2135
