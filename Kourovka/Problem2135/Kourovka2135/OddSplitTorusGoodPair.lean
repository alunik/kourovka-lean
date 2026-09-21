import Kourovka2135.BinarySplitGoodSetGeneration

/-! The checked Brandl matrices give good pairs for split elements of odd
order in every characteristic. A square root is taken inside the actual
odd cyclic subgroup, so no characteristic-two square-surjectivity is used. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddSplitTorusGoodPair
open BinarySplitTorusGoodPair

variable {F : Type*} [Field F]

theorem exists_odd_cyclic_square_root (v : Fˣ) (hv : Odd (orderOf v)) :
    ∃ u : Fˣ, u ^ 2 = v ∧ orderOf u = orderOf v := by
  obtain ⟨k, hk⟩ := hv
  let u := v ^ (k + 1)
  have hs : u ^ 2 = v := by
    dsimp [u]
    rw [← pow_mul, show (k + 1) * 2 = orderOf v + 1 by omega,
      pow_add, pow_orderOf_eq_one, one_mul, pow_one]
  refine ⟨u, hs, Nat.dvd_antisymm (orderOf_pow_dvd (x := v) (k + 1)) ?_⟩
  rw [← hs]
  exact orderOf_pow_dvd (x := u) 2

theorem exists_pair_tor (v : Fˣ) (hv : Odd (orderOf v)) (hne : v ≠ 1) :
    ∃ a b : SLTwo.SL2 F,
      a ∈ splitOrderSet (orderOf v) ∧ b ∈ splitOrderSet (orderOf v) ∧
      paperCommutator a b = SLTwo.tor v := by
  obtain ⟨u, hu, horder⟩ := exists_odd_cyclic_square_root v hv
  have hd : eigenDifference u ≠ 0 := by
    intro hz
    have he : u⁻¹ = u := Units.ext (sub_eq_zero.mp hz)
    have hs : u ^ 2 = 1 := by
      calc
        u ^ 2 = u * u := pow_two _
        _ = u⁻¹ * u := congrArg (fun x => x * u) he.symm
        _ = 1 := inv_mul_cancel _
    exact hne (hu.symm.trans hs)
  refine ⟨pairLeft u, pairRight u, ?_, ?_, ?_⟩
  · rw [← horder]
    exact pairLeft_mem_splitOrderSet u
  · rw [← horder]
    exact pairRight_mem_splitOrderSet u hd
  · rw [pair_commutator, hu]

variable (F) [Finite F] {r : ℕ} [Fact r.Prime]

theorem exists_generating_pair_tor
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (v : Fˣ) (hv : orderOf v = r) :
    ∃ a ∈ splitOrderSet r, ∃ b ∈ splitOrderSet r,
      paperCommutator a b = SLTwo.tor v ∧
        Subgroup.closure ({a, b} : Set (SLTwo.SL2 F)) = ⊤ := by
  have hne : v ≠ 1 := by
    intro h
    have he := hv
    rw [h, orderOf_one] at he
    exact (Fact.out : r.Prime).ne_one he.symm
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_tor v (hv ▸ hrOdd) hne
  rw [hv] at ha hb
  refine ⟨a, ha, b, hb, hab, ?_⟩
  apply BinarySplitGoodSetGeneration.generates_of_three_prime_orders F hsolv hrOdd hrSplit a b
    (orderOf_mem_splitOrderSet ha) (orderOf_mem_splitOrderSet hb)
  rw [hab, orderOf_tor, hv]

theorem isGeneratingGoodSet
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1) :
    IsGeneratingGoodSet (splitOrderSet (F := F) r) := by
  intro t ht
  obtain ⟨v, hv, hvt⟩ := ht
  obtain ⟨a, ha, b, hb, hab, hgen⟩ := exists_generating_pair_tor F hsolv hrOdd hrSplit v hv
  obtain ⟨g, hg⟩ := isConj_iff.mp hvt
  let f : SLTwo.SL2 F →* SLTwo.SL2 F := (MulAut.conj g).toMonoidHom
  refine ⟨f a, mem_splitOrderSet_of_isConj ha (isConj_iff.mpr ⟨g, rfl⟩),
    f b, mem_splitOrderSet_of_isConj hb (isConj_iff.mpr ⟨g, rfl⟩), ?_, ?_⟩
  · exact (map_paperCommutator f a b).symm.trans ((congrArg f hab).trans hg)
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective f (MulAut.conj g).surjective

end Kourovka2135.OddSplitTorusGoodPair
