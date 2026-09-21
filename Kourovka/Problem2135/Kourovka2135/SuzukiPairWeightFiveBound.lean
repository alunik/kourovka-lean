import Kourovka2135.SuzukiNaturalWeightDifferences
import Kourovka2135.SuzukiExceptionalPairWeights
import Kourovka2135.SuzukiPairGrid

/-! The uniform bound of five for shifted Suzuki pair weights. The natural
four weights and all ordered pair positions remain explicit. The general
argument uses binary-support arithmetic; finite certificates cover only
the fixed exceptional graph and the two small arithmetic bases. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiPairWeightFiveBound

open Finset BinaryWeights BinaryCyclicIntervals SuzukiPairWeightCollisions
open SuzukiNaturalWeightDifferences SuzukiPairGrid

def IsFrobenius (m : ℕ) (x : Residue m) : Prop :=
  ∃ i : Fin (2*m+1), x = 2^i.val

instance (m : ℕ) (x : Residue m) : Decidable (IsFrobenius m x) :=
  inferInstanceAs (Decidable (∃ i : Fin (2*m+1), x = 2^i.val))

def selected (m j : ℕ) (s : Residue m) : Finset Grid :=
  univ.filter fun p => IsFrobenius m (s + pairValue m j p)

@[simp] theorem mem_selected (m j : ℕ) (s : Residue m) (p : Grid) :
    p ∈ selected m j s ↔ IsFrobenius m (s + pairValue m j p) := by
  simp only [selected, mem_filter, mem_univ, true_and]

theorem pow_reduced (m n : ℕ) :
    (2 : Residue m)^n = 2^(n%(2*m+1)) := by
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (two_pow_modEq_reduced (2*m+1) n)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

theorem isFrobenius_mul (m j : ℕ) {x : Residue m} (hx : IsFrobenius m x) :
    IsFrobenius m ((2 : Residue m)^j * x) := by
  obtain ⟨i,rfl⟩ := hx
  refine ⟨⟨(j+i.val)%(2*m+1), Nat.mod_lt _ (by omega)⟩, ?_⟩
  rw [← pow_add]
  exact pow_reduced m _

theorem isFrobenius_mul_iff {m j : ℕ} (hj : j ≤ 2*m+1) (x : Residue m) :
    IsFrobenius m ((2 : Residue m)^j*x) ↔ IsFrobenius m x := by
  constructor
  · intro hx
    have he := isFrobenius_mul m ((2*m+1)-j) hx
    have hi : (2 : Residue m)^((2*m+1)-j) * 2^j = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hj, two_pow_cycle]
    simpa only [← mul_assoc, hi, one_mul] using he
  · exact isFrobenius_mul m j

theorem selected_row_path {m j : ℕ} (hm : 3 ≤ m) (s : Residue m) (r : Fin 4) :
    PathSupport (row (selected m j s) r) := by
  intro a ha b hb hab
  obtain ⟨c,hc⟩ := (mem_selected m j s (a,r)).mp (mem_filter.mp ha).2
  obtain ⟨d,hd⟩ := (mem_selected m j s (b,r)).mp (mem_filter.mp hb).2
  apply adjacent_of_frobenius_difference hm d.isLt c.isLt a b hab
  unfold pairValue at hc hd
  linear_combination hd - hc

/-- The Sidon property identifies both actual Frobenius endpoints of a
selected edge with natural-weight difference `2^e`. -/
theorem edge_targets {m j e : ℕ} (hm : 3 ≤ m) (s : Residue m)
    (a b r : Fin 4) (hab : a ≠ b) (he : e+1 < 2*m+1)
    (hstep : baseWeight m b - baseWeight m a = (2 : Residue m)^e)
    (ha : (a,r) ∈ selected m j s) (hb : (b,r) ∈ selected m j s) :
    s + pairValue m j (a,r) = (2 : Residue m)^e ∧
    s + pairValue m j (b,r) = (2 : Residue m)^(e+1) := by
  obtain ⟨c,hc⟩ := (mem_selected m j s (a,r)).mp ha
  obtain ⟨d,hd⟩ := (mem_selected m j s (b,r)).mp hb
  have hdc : d.val ≠ c.val := by
    intro h
    apply hab
    apply baseWeight_injective (m := m) (by omega)
    have hp : (2 : Residue m)^d.val = 2^c.val := by rw [h]
    unfold pairValue at hc hd
    linear_combination hc - hd - hp
  have hdiff : (2 : Residue m)^d.val - 2^c.val = 2^(e+1) - 2^e := by
    rw [pow_succ (2 : Residue m) e]
    unfold pairValue at hc hd
    linear_combination hc - hd + hstep
  obtain ⟨hde,hce⟩ := difference_injective (by omega) d.isLt c.isLt he (by omega) hdc hdiff
  exact ⟨by simpa only [hce] using hc, by simpa only [hde] using hd⟩

theorem outer_targets {m j : ℕ} (hm : 3 ≤ m) (s : Residue m) (i : Fin 2) (r : Fin 4)
    (ha : (outerLeft i,r) ∈ selected m j s) (hb : (outerRight i,r) ∈ selected m j s) :
    s + pairValue m j (outerLeft i,r) = 1 ∧
    s + pairValue m j (outerRight i,r) = 2 := by
  have hne : outerLeft i ≠ outerRight i := by fin_cases i <;> decide
  have hstep : baseWeight m (outerRight i) - baseWeight m (outerLeft i) = (2 : Residue m)^0 := by
    fin_cases i <;> norm_num [outerLeft, outerRight, baseWeight, baseValue,
      Matrix.cons_val_two, Matrix.cons_val_three]
  simpa only [Nat.zero_add, pow_zero, pow_one] using edge_targets hm s (outerLeft i) (outerRight i) r
    hne (by omega : 0+1 < 2*m+1) hstep ha hb

theorem inner_targets {m j : ℕ} (hm : 3 ≤ m) (s : Residue m) (r : Fin 4)
    (ha : ((1 : Fin 4),r) ∈ selected m j s) (hb : ((2 : Fin 4),r) ∈ selected m j s) :
    s + pairValue m j (1,r) = 2 * (2 : Residue m)^m ∧
    s + pairValue m j (2,r) = 4 * (2 : Residue m)^m := by
  have hstep : baseWeight m 2 - baseWeight m 1 = (2 : Residue m)^(m+1) := by
    norm_num [baseWeight, baseValue, Matrix.cons_val_two, Matrix.cons_val_three, pow_succ]
    ring
  have hh := edge_targets hm s 1 2 r (by decide) (by omega : m+1+1 < 2*m+1) hstep ha hb
  constructor
  · calc
      _ = (2 : Residue m)^(m+1) := hh.1
      _ = 2 * (2 : Residue m)^m := by rw [pow_succ (2 : Residue m) m]; ring
  · calc
      _ = (2 : Residue m)^(m+1+1) := hh.2
      _ = 4 * (2 : Residue m)^m := by
        rw [pow_succ (2 : Residue m) (m+1), pow_succ (2 : Residue m) m]
        ring

theorem selected_outerCount_le_one {m j : ℕ} (hm : 3 ≤ m) (s : Residue m)
    (hinj : Function.Injective (pairValue m j)) : outerCount (selected m j s) ≤ 1 := by
  apply outerCount_le_one_of_unique
  intro i k r t hil hir hkl hkr
  have hi := (outer_targets hm s i r hil hir).1
  have hk := (outer_targets hm s k t hkl hkr).1
  exact hinj (add_left_cancel (hi.trans hk.symm))

theorem selected_innerCount_le_one {m j : ℕ} (hm : 3 ≤ m) (s : Residue m)
    (hinj : Function.Injective (pairValue m j)) : innerCount (selected m j s) ≤ 1 := by
  apply innerCount_le_one_of_unique
  intro r t hr1 hr2 ht1 ht2
  have hr := (inner_targets hm s r hr1 hr2).1
  have ht := (inner_targets hm s t ht1 ht2).1
  exact congrArg Prod.snd (hinj (add_left_cancel (hr.trans ht.symm)))

/-- Outer and middle selected row edges cannot coexist. Their forced
endpoints give one of the two excluded mixed differences. -/
theorem not_both_edge_types {m j : ℕ} (hm : 3 ≤ m) (hj : j < 2*m+1) (s : Residue m)
    (ho : 0 < outerCount (selected m j s)) (hi : 0 < innerCount (selected m j s)) : False := by
  obtain ⟨r,hr⟩ := exists_outer_of_pos (selected m j s) ho
  obtain ⟨t,ht1,ht2⟩ := exists_inner_of_pos (selected m j s) hi
  have ht := (inner_targets hm s t ht1 ht2).1
  rcases hr with ⟨hr0,hr1⟩ | ⟨hr2,hr3⟩
  · have htr : t ≠ r := by
      intro he
      subst t
      have hh := selected_row_path hm s r 0 (by simpa [row] using hr0)
        2 (by simpa [row] using ht2) (by decide)
      norm_num at hh
    have hr := (outer_targets hm s 0 r hr0 hr1).1
    have hw : baseWeight m 1 - baseWeight m 0 = (1 : Residue m) := by
      norm_num [baseWeight,baseValue]
    have he : (2 : Residue m)^j * (baseWeight m t - baseWeight m r) = 2 * (2 : Residue m)^m - 2 := by
      change s + pairValue m j (0,r) = 1 at hr
      unfold pairValue at ht hr
      linear_combination ht - hr - hw
    exact (no_mixed_difference hm hj t r htr).1 he
  · have htr : t ≠ r := by
      intro he
      subst t
      have hh := selected_row_path hm s r 1 (by simpa [row] using ht1)
        3 (by simpa [row] using hr3) (by decide)
      norm_num at hh
    have hr := (outer_targets hm s 1 r hr2 hr3).1
    have hw : baseWeight m 1 - baseWeight m 2 = -(2 * (2 : Residue m)^m) := by
      norm_num [baseWeight,baseValue, Matrix.cons_val_two, Matrix.cons_val_three]
      ring
    have he : (2 : Residue m)^j * (baseWeight m t - baseWeight m r) = 4 * (2 : Residue m)^m - 1 := by
      change s + pairValue m j (2,r) = 1 at hr
      unfold pairValue at ht hr
      linear_combination ht - hr - hw
    exact (no_mixed_difference hm hj t r htr).2 he

/-- The nonexceptional branch needs only four row counts and the mixed
support obstruction; no cyclic-overlap or diameter premise remains. -/
theorem nonexceptional_bound {m j : ℕ} (hm : 3 ≤ m) (hj : j < 2*m+1)
    (hj0 : j ≠ 0) (hjm : j ≠ m) (hjm1 : j ≠ m+1) (s : Residue m) :
    (selected m j s).card ≤ 5 := by
  have hinj := pairValue_injective (by omega : 2 ≤ m) hj hj0 hjm hjm1
  have ho := selected_outerCount_le_one hm s hinj
  have hi := selected_innerCount_le_one hm s hinj
  by_contra h
  have hh := six_forces_edges (selected m j s) (selected_row_path hm s) ho hi (by omega)
  exact not_both_edge_types hm hj s (by omega) (by omega)

/-- The exact fiber map from sixteen ordered pairs to twelve exceptional
weights; repeated vertices retain their multiplicities. -/
def pairVertex (p : Grid) : Fin 12 :=
  (!![0,2,3,5; 1,3,4,6; 5,7,8,10; 6,8,9,11] :
    Matrix (Fin 4) (Fin 4) (Fin 12)) p.1 p.2

theorem pairVertex_fiber_card : ∀ i : Fin 12,
    ((univ : Finset Grid).filter fun p => pairVertex p = i).card =
      SuzukiPairWeightFinite.multiplicity i := by
  decide +kernel

theorem pairVertex_preimage_card (S : Finset (Fin 12)) :
    ((univ : Finset Grid).filter fun p => pairVertex p ∈ S).card =
      ∑ i ∈ S, SuzukiPairWeightFinite.multiplicity i := by
  rw [← sum_card_fiberwise_eq_card_filter univ S pairVertex]
  apply sum_congr rfl
  intro i _
  exact pairVertex_fiber_card i

/-- Doubling and translating the actual pair sum gives exactly its graph
vertex value. This is a ring identity using `2r²=1` modulo `2r²−1`. -/
theorem pairValue_doubled (m : ℕ) (p : Grid) :
    2 * pairValue m m p + (4 * (2 : Residue m)^m + 3) =
      (SuzukiExceptionalPairWeights.value (2^m) (pairVertex p) : Residue m) := by
  have hsq : (2 : Residue m) * ((2 : Residue m)^m)^2 = 1 := by
    calc
      _ = (2 : Residue m)^(m*2+1) := by
        rw [pow_add (2 : Residue m) (m*2) 1, pow_mul (2 : Residue m) m 2]
        ring
      _ = 1 := by rw [show m*2+1 = 2*m+1 by omega, two_pow_cycle]
  obtain ⟨a,b⟩ := p
  fin_cases a <;> fin_cases b <;>
    norm_num [pairValue, baseWeight, baseValue, pairVertex] <;>
    first | linear_combination hsq | linear_combination -hsq

theorem exceptional_selected_iff (m : ℕ) (s : Residue m) (p : Grid) :
    p ∈ selected m m s ↔ pairVertex p ∈ SuzukiExceptionalPairWeights.selected m
      (2*s - (4*(2 : Residue m)^m+3)) := by
  rw [mem_selected]
  simp only [SuzukiExceptionalPairWeights.selected, mem_filter, mem_univ, true_and]
  change IsFrobenius m (s + pairValue m m p) ↔
    IsFrobenius m (2*s - (4*(2 : Residue m)^m+3) +
      (SuzukiExceptionalPairWeights.value (2^m) (pairVertex p) : Residue m))
  have he : 2*s - (4*(2 : Residue m)^m+3) +
      (SuzukiExceptionalPairWeights.value (2^m) (pairVertex p) : Residue m) =
      2*(s + pairValue m m p) := by
    linear_combination -(pairValue_doubled m p)
  rw [he]
  simpa only [pow_one] using (isFrobenius_mul_iff (by omega : 1 ≤ 2*m+1)
    (s + pairValue m m p)).symm

theorem exceptional_bound {m : ℕ} (hm : 3 ≤ m) (s : Residue m) :
    (selected m m s).card ≤ 5 := by
  let S := SuzukiExceptionalPairWeights.selected m (2*s-(4*(2 : Residue m)^m+3))
  have he : selected m m s = univ.filter fun p => pairVertex p ∈ S := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    exact exceptional_selected_iff m s p
  rw [he, pairVertex_preimage_card]
  exact SuzukiExceptionalPairWeights.weighted_selected_le_five hm _

theorem pairValue_swap (m : ℕ) (p : Grid) :
    pairValue m m p.swap = (2 : Residue m)^m * pairValue m (m+1) p := by
  have hp : (2 : Residue m)^m * 2^(m+1) = 1 := by
    rw [← pow_add, show m+(m+1) = 2*m+1 by omega, two_pow_cycle]
  unfold pairValue
  change baseWeight m p.2 + (2 : Residue m)^m * baseWeight m p.1 =
    (2 : Residue m)^m * (baseWeight m p.1 + 2^(m+1)*baseWeight m p.2)
  rw [mul_add, ← mul_assoc, hp, one_mul]
  ring

theorem selected_swap_iff (m : ℕ) (s : Residue m) (p : Grid) :
    p.swap ∈ selected m m ((2 : Residue m)^m*s) ↔ p ∈ selected m (m+1) s := by
  simp only [mem_selected, pairValue_swap, ← mul_add]
  exact isFrobenius_mul_iff (by omega) _

theorem selected_swap_card (m : ℕ) (s : Residue m) :
    (selected m (m+1) s).card = (selected m m ((2 : Residue m)^m*s)).card := by
  apply card_bij (fun p _ => p.swap)
  · intro p hp
    exact (selected_swap_iff m s p).mpr hp
  · intro p _ q _ he
    exact Prod.swap_injective he
  · intro p hp
    refine ⟨p.swap, ?_, ?_⟩
    · exact (selected_swap_iff m s p.swap).mp (by simpa using hp)
    · exact Prod.swap_swap p

theorem other_exceptional_bound {m : ℕ} (hm : 3 ≤ m) (s : Residue m) :
    (selected m (m+1) s).card ≤ 5 := by
  rw [selected_swap_card]
  exact exceptional_bound hm _

theorem small_frobenius_iff (x : Residue 2) :
    IsFrobenius 2 x ↔ x ∈ SuzukiPairWeightFinite.smallFrobenius := by
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> norm_num [SuzukiPairWeightFinite.smallFrobenius]
  · intro hx
    simp only [SuzukiPairWeightFinite.smallFrobenius, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨4, by norm_num⟩

theorem small_bound {j : ℕ} (hj : 0 < j) (hjf : j < 5) (s : Residue 2) :
    (selected 2 j s).card ≤ 5 := by
  have hweight (i : Fin 4) : baseWeight 2 i = SuzukiPairWeightFinite.smallWeight i := by
    fin_cases i <;> norm_num [baseWeight, baseValue, SuzukiPairWeightFinite.smallWeight]
  have he : j-1+1 = j := by omega
  have hh := SuzukiPairWeightFinite.five_exponent_pair_bound ⟨j-1, by omega⟩ s
  simpa only [selected, pairValue, small_frobenius_iff, hweight, he, add_assoc] using hh

/-- For every odd field exponent `2m+1≥5`, every nonzero twist gap and
every shift select at most five of the sixteen ordered natural-weight
pairs. The statement counts positions, including exceptional repetitions. -/
theorem pair_bound {m j : ℕ} (hm : 2 ≤ m) (hj : 0 < j) (hjf : j < 2*m+1)
    (s : Residue m) : (selected m j s).card ≤ 5 := by
  by_cases hm2 : m = 2
  · subst m
    exact small_bound hj hjf s
  · have hm3 : 3 ≤ m := by omega
    by_cases hjm : j = m
    · subst j
      exact exceptional_bound hm3 s
    · by_cases hjm1 : j = m+1
      · subst j
        exact other_exceptional_bound hm3 s
      · exact nonexceptional_bound hm3 hjf (Nat.ne_of_gt hj) hjm hjm1 s

end Kourovka2135.SuzukiPairWeightFiveBound
