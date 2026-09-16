import Kourovka.Problems.P21_38.Proof.TreePairRealization
import Mathlib.Data.List.Forall2

/-!
# The companion's two ordered binary partitions

These are the two explicit refinements used in the `c = d = 1` case of
Golan-Polak's construction. The starting partition is an honest intermediate
parameter; no generation property is assumed.
-/

namespace Kourovka.P21_38

open BinaryWord
open GroupApproximation.HigmanThompson

namespace WordPartition

/-- Refine one designated leaf by an ordered partition of that same interval. -/
theorem replaceLeaf {a b : ℚ} {pre post : List (List Bool)} {w : List Bool}
    {xs : List (List Bool)} (h : WordPartition a b (pre ++ w :: post))
    (hx : WordPartition (chart w 0) (chart w 1) xs) :
    WordPartition a b (pre ++ xs ++ post) := by
  induction pre generalizing a with
  | nil =>
    cases h with
    | @cons a _ c _ _ hl hr ht =>
      have hxt : WordPartition a c xs := by simpa only [hl, hr] using hx
      exact hxt.append ht
  | cons v pre ih =>
    cases h with
    | cons hl hr ht => exact .cons hl hr (ih ht)

end WordPartition

namespace HasBranch

/-- A branch is the asserted affine map at every point of its closed
source interval, not just at normalized chart parameters. -/
theorem affine_formula {f : Equiv.Perm ℚ} {u v : List Bool} (h : HasBranch f u v)
    {x : ℚ} (hx0 : chart u 0 ≤ x) (hx1 : x ≤ chart u 1) :
    f x = chart v 0 + ((2 : ℚ) ^ u.length / 2 ^ v.length) * (x - chart u 0) := by
  let t : ℚ := (x - chart u 0) * 2 ^ u.length
  have hp : (0 : ℚ) < 2 ^ u.length := by positivity
  have ht0 : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hx0) hp.le
  have ht1 : t ≤ 1 := by
    have hb := chart_affine u 1
    have hx : x - chart u 0 ≤ 1 / (2 : ℚ) ^ u.length := by linarith
    exact (le_div_iff₀ hp).mp hx
  have hchart : chart u t = x := by
    rw [chart_affine]
    dsimp [t]
    field_simp
    ring
  have hh := h t ⟨ht0, ht1⟩
  rw [hchart, chart_affine] at hh
  rw [hh]
  dsimp [t]
  ring

theorem affine_formula_right {f : Equiv.Perm ℚ} {u v : List Bool} (h : HasBranch f u v)
    {x : ℚ} (hx0 : chart u 0 ≤ x) (hx1 : x ≤ chart u 1) :
    f x = chart v 1 + ((2 : ℚ) ^ u.length / 2 ^ v.length) * (x - chart u 1) := by
  rw [h.affine_formula hx0 hx1, chart_affine v 1, chart_affine u 1]
  field_simp
  ring

theorem identity_on_interval {f : Equiv.Perm ℚ} {u : List Bool} (h : HasBranch f u u)
    {x : ℚ} (hx0 : chart u 0 ≤ x) (hx1 : x ≤ chart u 1) : f x = x := by
  have hh := h.affine_formula hx0 hx1
  have hp : (2 : ℚ) ^ u.length ≠ 0 := by positivity
  rw [div_self hp, one_mul] at hh
  linarith

private theorem two_pow_length_ratio (p : List Bool) :
    (2 : ℚ) ^ (p.length + 2) / 2 ^ (p.length + 1) = 2 := by
  simp only [pow_add]
  norm_num
  field_simp
  norm_num

theorem double_zero_formula {f : Equiv.Perm ℚ} {p : List Bool}
    (h : HasBranch f (p ++ [false, false]) (p ++ [false]))
    {x : ℚ} (hx0 : chart p 0 ≤ x) (hx1 : x ≤ chart (p ++ [false, false]) 1) :
    f x = chart p 0 + 2 * (x - chart p 0) := by
  have hu : chart (p ++ [false, false]) 0 = chart p 0 := by simp [chart_append, chart]
  have hv : chart (p ++ [false]) 0 = chart p 0 := by simp [chart_append, chart]
  have hh := h.affine_formula (by simpa only [hu] using hx0) hx1
  simpa only [hu, hv, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, two_pow_length_ratio] using hh

theorem double_one_formula {f : Equiv.Perm ℚ} {p : List Bool}
    (h : HasBranch f (p ++ [true, true]) (p ++ [true]))
    {x : ℚ} (hx0 : chart (p ++ [true, true]) 0 ≤ x) (hx1 : x ≤ chart p 1) :
    f x = chart p 1 + 2 * (x - chart p 1) := by
  have hu : chart (p ++ [true, true]) 1 = chart p 1 := by norm_num [chart_append, chart]
  have hv : chart (p ++ [true]) 1 = chart p 1 := by norm_num [chart_append, chart]
  have hh := h.affine_formula_right hx0 (by simpa only [hu] using hx1)
  simpa only [hu, hv, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, two_pow_length_ratio] using hh

end HasBranch

namespace CompanionTrees

def baseWords (a w z : List Bool) (L R : List (List Bool)) : List (List Bool) :=
  [a] ++ L ++ [w ++ [false], w ++ [true, false], w ++ [true, true]] ++ R ++ [z]

def sourceWords (a w z : List Bool) (L R : List (List Bool)) : List (List Bool) :=
  [a ++ [false, false], a ++ [false, true], a ++ [true]] ++ L ++
    [w ++ [false], w ++ [true, false, false], w ++ [true, false, true, false, false],
      w ++ [true, false, true, false, true], w ++ [true, false, true, true],
      w ++ [true, true]] ++ R ++ [z ++ [false], z ++ [true, false], z ++ [true, true]]

def targetWords (a w z : List Bool) (L R : List (List Bool)) : List (List Bool) :=
  [a ++ [false], a ++ [true]] ++ L ++
    [w ++ [false, false], w ++ [false, true], w ++ [true, false, false],
      w ++ [true, false, true, false], w ++ [true, false, true, true, false],
      w ++ [true, false, true, true, true], w ++ [true, true, false],
      w ++ [true, true, true]] ++ R ++ [z ++ [false], z ++ [true]]

@[simp] theorem sourceWords_length (a w z : List Bool) (L R : List (List Bool)) :
    (sourceWords a w z L R).length = L.length + R.length + 12 := by
  simp [sourceWords]
  omega

@[simp] theorem targetWords_length (a w z : List Bool) (L R : List (List Bool)) :
    (targetWords a w z L R).length = L.length + R.length + 12 := by
  simp [targetWords]
  omega

private theorem splitTwo (w : List Bool) :
    WordPartition (chart w 0) (chart w 1) [w ++ [false], w ++ [true]] := by
  simpa [BinaryTree.leaves] using
    (BinaryTree.leaves_partition (.node .leaf .leaf)).prefixWords w

private theorem splitLeft (w : List Bool) :
    WordPartition (chart w 0) (chart w 1)
      [w ++ [false, false], w ++ [false, true], w ++ [true]] := by
  simpa [BinaryTree.leaves] using
    (BinaryTree.leaves_partition (.node (.node .leaf .leaf) .leaf)).prefixWords w

private theorem splitRight (w : List Bool) :
    WordPartition (chart w 0) (chart w 1)
      [w ++ [false], w ++ [true, false], w ++ [true, true]] := by
  simpa [BinaryTree.leaves] using
    (BinaryTree.leaves_partition (.node .leaf (.node .leaf .leaf))).prefixWords w

private theorem splitSourceMiddle (w : List Bool) :
    WordPartition (chart w 0) (chart w 1)
      [w ++ [false], w ++ [true, false, false],
        w ++ [true, false, true], w ++ [true, true]] := by
  simpa [BinaryTree.leaves] using
    (BinaryTree.leaves_partition (.node .leaf (.node (.node .leaf .leaf) .leaf))).prefixWords w

private theorem splitTargetMiddle (w : List Bool) :
    WordPartition (chart w 0) (chart w 1)
      [w ++ [false], w ++ [true, false],
        w ++ [true, true, false], w ++ [true, true, true]] := by
  simpa [BinaryTree.leaves] using
    (BinaryTree.leaves_partition (.node .leaf (.node .leaf (.node .leaf .leaf)))).prefixWords w

theorem source_partition {a w z : List Bool} {L R : List (List Bool)}
    (h : WordPartition 0 1 (baseWords a w z L R)) :
    WordPartition 0 1 (sourceWords a w z L R) := by
  have h1 := WordPartition.replaceLeaf (pre := [])
    (post := L ++ [w ++ [false], w ++ [true, false], w ++ [true, true]] ++ R ++ [z])
    (w := a) (by simpa [baseWords] using h) (splitLeft a)
  have h2 := WordPartition.replaceLeaf
    (pre := [a ++ [false, false], a ++ [false, true], a ++ [true]] ++ L ++ [w ++ [false]])
    (post := [w ++ [true, true]] ++ R ++ [z]) (w := w ++ [true, false])
    (by simpa [List.append_assoc] using h1) (splitSourceMiddle (w ++ [true, false]))
  have h3 := WordPartition.replaceLeaf
    (pre := [a ++ [false, false], a ++ [false, true], a ++ [true]] ++ L ++
      [w ++ [false], w ++ [true, false, false], w ++ [true, false, true, false, false],
        w ++ [true, false, true, false, true], w ++ [true, false, true, true],
        w ++ [true, true]] ++ R)
    (post := []) (w := z) (by simpa [List.append_assoc] using h2) (splitRight z)
  simpa [sourceWords, List.append_assoc] using h3

theorem target_partition {a w z : List Bool} {L R : List (List Bool)}
    (h : WordPartition 0 1 (baseWords a w z L R)) :
    WordPartition 0 1 (targetWords a w z L R) := by
  have h1 := WordPartition.replaceLeaf (pre := [])
    (post := L ++ [w ++ [false], w ++ [true, false], w ++ [true, true]] ++ R ++ [z])
    (w := a) (by simpa [baseWords] using h) (splitTwo a)
  have h2 := WordPartition.replaceLeaf
    (pre := [a ++ [false], a ++ [true]] ++ L)
    (post := [w ++ [true, false], w ++ [true, true]] ++ R ++ [z]) (w := w ++ [false])
    (by simpa [List.append_assoc] using h1) (splitTwo (w ++ [false]))
  have h3 := WordPartition.replaceLeaf
    (pre := [a ++ [false], a ++ [true]] ++ L ++ [w ++ [false, false], w ++ [false, true]])
    (post := [w ++ [true, true]] ++ R ++ [z]) (w := w ++ [true, false])
    (by simpa [List.append_assoc] using h2) (splitTargetMiddle (w ++ [true, false]))
  have h4 := WordPartition.replaceLeaf
    (pre := [a ++ [false], a ++ [true]] ++ L ++
      [w ++ [false, false], w ++ [false, true], w ++ [true, false, false],
        w ++ [true, false, true, false], w ++ [true, false, true, true, false],
        w ++ [true, false, true, true, true]])
    (post := R ++ [z]) (w := w ++ [true, true])
    (by simpa [List.append_assoc] using h3) (splitTwo (w ++ [true, true]))
  have h5 := WordPartition.replaceLeaf
    (pre := [a ++ [false], a ++ [true]] ++ L ++
      [w ++ [false, false], w ++ [false, true], w ++ [true, false, false],
        w ++ [true, false, true, false], w ++ [true, false, true, true, false],
        w ++ [true, false, true, true, true], w ++ [true, true, false], w ++ [true, true, true]] ++ R)
    (post := []) (w := z) (by simpa [List.append_assoc] using h4) (splitTwo z)
  simpa [targetWords, List.append_assoc] using h5

/-- The two explicit partitions realize an actual element of `F`, with all
ordered branch pairs recorded by `List.Forall₂`. -/
theorem exists_companion_branches {a w z : List Bool} {L R : List (List Bool)}
    (h : WordPartition 0 1 (baseWords a w z L R)) :
    ∃ g : F, List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R) := by
  have hlen : (sourceWords a w z L R).length = (targetWords a w z L R).length := by simp
  obtain ⟨f, hf, hf0, hf1, hbranches⟩ := exists_pl_of_wordPartitions
    (source_partition h) (target_partition h) hlen
    ⟨0, int_mem_grid (m := 2) 0 0⟩ ⟨0, int_mem_grid (m := 2) 0 0⟩
  obtain ⟨g, hg⟩ := exists_interval_restriction hf hf0 hf1
  refine ⟨g, List.forall₂_iff_zip.mpr ⟨hlen, ?_⟩⟩
  intro u v huv t ht
  rw [hg _ (chart_mem_unit u ht)]
  exact hbranches u v huv t ht

theorem left_branch {g : F} {a w z : List Bool} {L R : List (List Bool)}
    (h : List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R)) :
    HasBranch g.1 (a ++ [false, false]) (a ++ [false]) := by
  change List.Forall₂ _ ((a ++ [false, false]) :: _) ((a ++ [false]) :: _) at h
  cases h with
  | cons hh _ => exact hh

theorem right_branch {g : F} {a w z : List Bool} {L R : List (List Bool)}
    (h : List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R)) :
    HasBranch g.1 (z ++ [true, true]) (z ++ [true]) := by
  have hr := List.rel_reverse h
  simp only [sourceWords, targetWords, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append] at hr
  cases hr with
  | cons hh _ => exact hh

private theorem forall₂_tail_of_prefix_length_eq {α β : Type*} {r : α → β → Prop}
    {ps us : List α} {qs vs : List β} (h : List.Forall₂ r (ps ++ us) (qs ++ vs))
    (hlen : ps.length = qs.length) : List.Forall₂ r us vs := by
  have hd := List.forall₂_drop ps.length h
  rw [List.drop_left, hlen, List.drop_left] at hd
  exact hd

theorem middle_branches {g : F} {a w z : List Bool} {L R : List (List Bool)}
    (h : List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R)) :
    HasBranch g.1 (w ++ [true, false, false]) (w ++ [true, false, false]) ∧
      HasBranch g.1 (w ++ [true, false, true, false, false])
        (w ++ [true, false, true, false]) := by
  let ps := [a ++ [false, false], a ++ [false, true], a ++ [true]] ++ L ++ [w ++ [false]]
  let qs := [a ++ [false], a ++ [true]] ++ L ++ [w ++ [false, false], w ++ [false, true]]
  have h' : List.Forall₂ (HasBranch g.1)
      (ps ++ [w ++ [true, false, false], w ++ [true, false, true, false, false],
        w ++ [true, false, true, false, true], w ++ [true, false, true, true],
        w ++ [true, true]] ++ R ++ [z ++ [false], z ++ [true, false], z ++ [true, true]])
      (qs ++ [w ++ [true, false, false], w ++ [true, false, true, false],
        w ++ [true, false, true, true, false], w ++ [true, false, true, true, true],
        w ++ [true, true, false], w ++ [true, true, true]] ++ R ++ [z ++ [false], z ++ [true]]) := by
    simpa [ps, qs, sourceWords, targetWords, List.append_assoc] using h
  have hd := forall₂_tail_of_prefix_length_eq (ps := ps) (qs := qs)
    (by simpa only [List.append_assoc] using h') (by simp [ps, qs])
  cases hd with
  | cons hfix ht =>
    cases ht with
    | cons hslope _ => exact ⟨hfix, hslope⟩

theorem endpoint_exponents {g : F} {a w z : List Bool} {L R : List (List Bool)}
    (h : List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R))
    (ha : chart a 0 = 0) (hz : chart z 1 = 1) :
    leftExponent g = 1 ∧ rightExponent g = 1 := by
  constructor
  · apply leftExponent_eq
    let ε : ℚ := chart (a ++ [false, false]) 1
    have hzero : chart (a ++ [false, false]) 0 = 0 := by simp [chart_append, chart, ha]
    have hε : 0 < ε := by
      have hh := chart_zero_lt_one (a ++ [false, false])
      simpa only [hzero] using hh
    refine ⟨ε, hε, fun t ht0 htε => ?_⟩
    have hh := (left_branch h).double_zero_formula (by simpa only [ha] using ht0) htε
    simpa only [ha, sub_zero, zero_add, zpow_one] using hh
  · apply rightExponent_eq
    let ε : ℚ := 1 - chart (z ++ [true, true]) 0
    have hone : chart (z ++ [true, true]) 1 = 1 := by norm_num [chart_append, chart, hz]
    have hε : 0 < ε := by
      have hh := chart_zero_lt_one (z ++ [true, true])
      rw [hone] at hh
      exact sub_pos.mpr hh
    refine ⟨ε, hε, fun t htε ht1 => ?_⟩
    have hlow : chart (z ++ [true, true]) 0 ≤ t := by dsimp [ε] at htε; linarith
    have hh := (right_branch h).double_one_formula hlow (by simpa only [hz] using ht1)
    simpa only [hz, zpow_one] using hh

/-- The dyadic point at which the constructed companion changes from
the identity on the left to slope two on the right. -/
def jumpPoint (w : List Bool) : ℚ := chart (w ++ [true, false, true]) 0

theorem jumpPoint_interior (w : List Bool) : 0 < jumpPoint w ∧ jumpPoint w < 1 := by
  have he : jumpPoint w = chart w (5 / 8) := by norm_num [jumpPoint, chart_append, chart]
  have h0 : 0 ≤ chart w 0 := (chart_mem_unit w (show (0 : ℚ) ∈ Set.Icc 0 1 by constructor <;> norm_num)).1
  have h1 : chart w 1 ≤ 1 := (chart_mem_unit w (show (1 : ℚ) ∈ Set.Icc 0 1 by constructor <;> norm_num)).2
  rw [he]
  exact ⟨h0.trans_lt (chart_strictMono w (by norm_num)),
    (chart_strictMono w (by norm_num)).trans_le h1⟩

theorem slope_jump {g : F} {a w z : List Bool} {L R : List (List Bool)}
    (h : List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R)) :
    0 < jumpPoint w ∧ jumpPoint w < 1 ∧
      (∃ N : ℕ, jumpPoint w ∈ Grid 2 N) ∧ g.1 (jumpPoint w) = jumpPoint w ∧
      ∃ ρ δ : ℚ, 0 < ρ ∧ 0 < δ ∧
        (∀ t : ℚ, jumpPoint w - ρ ≤ t → t ≤ jumpPoint w → g.1 t = t) ∧
        (∀ t : ℚ, jumpPoint w ≤ t → t ≤ jumpPoint w + δ →
          g.1 t = jumpPoint w + 2 * (t - jumpPoint w)) := by
  obtain ⟨hfix, hslope⟩ := middle_branches h
  let p := w ++ [true, false, true]
  let l := w ++ [true, false, false]
  have hjoin : chart l 1 = jumpPoint w := by norm_num [l, jumpPoint, chart_append, chart]
  have hslope' : HasBranch g.1 (p ++ [false, false]) (p ++ [false]) := by
    simpa [p, List.append_assoc] using hslope
  have hzero : chart (p ++ [false, false]) 0 = jumpPoint w := by
    simp [p, jumpPoint, chart_append, chart]
  let ρ : ℚ := jumpPoint w - chart l 0
  let δ : ℚ := chart (p ++ [false, false]) 1 - jumpPoint w
  have hρ : 0 < ρ := by
    have hh := chart_zero_lt_one l
    rw [hjoin] at hh
    exact sub_pos.mpr hh
  have hδ : 0 < δ := by
    have hh := chart_zero_lt_one (p ++ [false, false])
    rw [hzero] at hh
    exact sub_pos.mpr hh
  have hfixed : g.1 (jumpPoint w) = jumpPoint w :=
    hfix.identity_on_interval (by have hh := chart_zero_lt_one l; rw [hjoin] at hh; exact hh.le)
      hjoin.ge
  refine ⟨(jumpPoint_interior w).1, (jumpPoint_interior w).2,
    chart_zero_dyadic _, hfixed, ρ, δ, hρ, hδ, ?_, ?_⟩
  · intro t ht0 ht1
    apply hfix.identity_on_interval
    · dsimp [ρ] at ht0
      exact by linarith
    · rw [hjoin]
      exact ht1
  · intro t ht0 ht1
    apply hslope'.double_zero_formula ht0
    dsimp [δ] at ht1
    linarith

/-- The companion exists with every explicit branch, endpoint exponents
`(1,1)`, and the dyadic identity/slope-two junction required later. -/
theorem exists_companion {a w z : List Bool} {L R : List (List Bool)}
    (hbase : WordPartition 0 1 (baseWords a w z L R))
    (ha : chart a 0 = 0) (hz : chart z 1 = 1) :
    ∃ g : F, List.Forall₂ (HasBranch g.1)
      (sourceWords a w z L R) (targetWords a w z L R) ∧
      leftExponent g = 1 ∧ rightExponent g = 1 ∧
      g.1 (jumpPoint w) = jumpPoint w := by
  obtain ⟨g, hg⟩ := exists_companion_branches hbase
  obtain ⟨hl, hr⟩ := endpoint_exponents hg ha hz
  exact ⟨g, hg, hl, hr, (slope_jump hg).2.2.2.1⟩

end CompanionTrees

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.CompanionTrees.source_partition
#audit_axioms Kourovka.P21_38.CompanionTrees.target_partition
#audit_axioms Kourovka.P21_38.CompanionTrees.exists_companion_branches
#audit_axioms Kourovka.P21_38.CompanionTrees.endpoint_exponents
#audit_axioms Kourovka.P21_38.CompanionTrees.slope_jump
#audit_axioms Kourovka.P21_38.CompanionTrees.exists_companion
