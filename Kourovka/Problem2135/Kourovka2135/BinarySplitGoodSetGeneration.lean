import Kourovka2135.BinarySplitTorusGoodPair
import Kourovka2135.BinarySplitSylow
import Kourovka2135.SolubleCyclicSylowCommutator
import Kourovka2135.GoodSetLifting

/-! Actual generation for Brandl's split-torus commutator pairs. A proper
generated subgroup would be soluble and have cyclic Sylow subgroups at the
split prime, contradicting the three actual prime orders. No generation
premise or additional subgroup classification is assumed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinarySplitGoodSetGeneration

section Generic

variable {S : Type*} [Group S] [Finite S] {r : ℕ} [Fact r.Prime]

/-- Three prime orders force generation if every proper subgroup is soluble
and all of its Sylow subgroups at that prime are cyclic. -/
theorem closure_eq_top_of_three_prime_orders
    (hsolv : ∀ H : Subgroup S, H < ⊤ → Group.IsSolvable H)
    (hcyclic : ∀ (H : Subgroup S) (P : Sylow r H), IsCyclic P)
    (a b : S) (ha : orderOf a = r) (hb : orderOf b = r)
    (hc : orderOf (paperCommutator a b) = r) :
    Subgroup.closure ({a, b} : Set S) = ⊤ := by
  by_contra hne
  let H := Subgroup.closure ({a, b} : Set S)
  have hlt : H < ⊤ := lt_top_iff_ne_top.mpr hne
  let : Group.IsSolvable H := hsolv H hlt
  let aH : H := ⟨a, Subgroup.subset_closure (Set.mem_insert a {b})⟩
  let bH : H := ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))⟩
  have hgenH : Subgroup.closure ({aH, bH} : Set H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      H.range_subtype]
    rfl
  have haH : orderOf aH = r :=
    (orderOf_injective H.subtype H.subtype_injective aH).symm.trans ha
  have hbH : orderOf bH = r :=
    (orderOf_injective H.subtype H.subtype_injective bH).symm.trans hb
  have hcH : orderOf (paperCommutator aH bH) = r :=
    (orderOf_injective H.subtype H.subtype_injective (paperCommutator aH bH)).symm.trans hc
  let P : Sylow r H := Sylow.nonempty.some
  let : IsCyclic P := hcyclic H P
  exact SolubleCyclicSylowCommutator.false_of_three_prime_orders P aH bH haH hbH hgenH hcH

end Generic

open BinarySplitTorusGoodPair

variable (F : Type*) [Field F] [Finite F] {r : ℕ} [Fact r.Prime]

/-- Cyclicity here is derived from the actual split torus, for every generated subgroup. -/
theorem generates_of_three_prime_orders
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (a b : SLTwo.SL2 F) (ha : orderOf a = r) (hb : orderOf b = r)
    (hc : orderOf (paperCommutator a b) = r) :
    Subgroup.closure ({a, b} : Set (SLTwo.SL2 F)) = ⊤ :=
  closure_eq_top_of_three_prime_orders hsolv
    (BinarySplitSylow.subgroup_sylow_isCyclic F hrOdd hrSplit) a b ha hb hc

/-- The explicit torus-target pair actually generates; generation is a conclusion. -/
theorem exists_generating_pair_tor [CharP F 2]
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (v : Fˣ) (hv : orderOf v = r) :
    ∃ a ∈ splitOrderSet r, ∃ b ∈ splitOrderSet r,
      paperCommutator a b = SLTwo.tor v ∧
        Subgroup.closure ({a, b} : Set (SLTwo.SL2 F)) = ⊤ := by
  have hvne : v ≠ 1 := by
    intro heq
    have hrone : r = 1 := by simpa only [heq, orderOf_one] using hv.symm
    exact (Fact.out : r.Prime).ne_one hrone
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_tor v hvne
  rw [hv] at ha hb
  refine ⟨a, ha, b, hb, hab, ?_⟩
  apply generates_of_three_prime_orders F hsolv hrOdd hrSplit a b
    (orderOf_mem_splitOrderSet ha) (orderOf_mem_splitOrderSet hb)
  rw [hab, orderOf_tor, hv]

/-- Every member of the actual split-prime set is a commutator of two members
that generate the actual SL2 group. -/
theorem isGeneratingGoodSet [CharP F 2]
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1) :
    IsGeneratingGoodSet (splitOrderSet (F := F) r) := by
  intro t ht
  obtain ⟨v, hv, hvt⟩ := ht
  obtain ⟨a, ha, b, hb, hab, hgen⟩ :=
    exists_generating_pair_tor F hsolv hrOdd hrSplit v hv
  obtain ⟨g, hg⟩ := isConj_iff.mp hvt
  let f : SLTwo.SL2 F →* SLTwo.SL2 F := (MulAut.conj g).toMonoidHom
  have hfa : f a ∈ splitOrderSet r :=
    mem_splitOrderSet_of_isConj ha (isConj_iff.mpr ⟨g, rfl⟩)
  have hfb : f b ∈ splitOrderSet r :=
    mem_splitOrderSet_of_isConj hb (isConj_iff.mpr ⟨g, rfl⟩)
  refine ⟨f a, hfa, f b, hfb, ?_, ?_⟩
  · calc
      paperCommutator (f a) (f b) = f (paperCommutator a b) :=
        (map_paperCommutator f a b).symm
      _ = f (SLTwo.tor v) := congrArg f hab
      _ = t := hg
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective f (MulAut.conj g).surjective

/-- Cauchy's theorem in the actual field units makes the split-prime set nonempty. -/
theorem splitOrderSet_nonempty (hrSplit : r ∣ Nat.card F - 1) :
    (splitOrderSet (F := F) r).Nonempty := by
  have hdiv : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r hdiv
  exact ⟨SLTwo.tor v, v, hv, IsConj.refl _⟩

omit [Finite F] in
/-- Every member is nonidentity because its actual order is the prime r. -/
theorem ne_one_of_mem {g : SLTwo.SL2 F} (hg : g ∈ splitOrderSet r) : g ≠ 1 := by
  intro heq
  have ho := orderOf_mem_splitOrderSet hg
  have hrone : r = 1 := by simpa only [heq, orderOf_one] using ho.symm
  exact (Fact.out : r.Prime).ne_one hrone

/-- The actual quotient set contains an odd-order member. -/
theorem exists_odd_member (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1) :
    ∃ g ∈ splitOrderSet (F := F) r, Odd (orderOf g) := by
  obtain ⟨g, hg⟩ := splitOrderSet_nonempty F hrSplit
  exact ⟨g, hg, (orderOf_mem_splitOrderSet hg).symm ▸ hrOdd⟩

end Kourovka2135.BinarySplitGoodSetGeneration
