import Kourovka.Problems.P21_38.Proof.PLBranchPartition
import Kourovka.Problems.P21_38.Proof.LocalInterpolation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.List.Forall2

/-!
# Interior branch partitions for local interpolation

A compactly supported element has paired binary partitions on a slightly
larger interior interval than any prescribed compact interval. Common binary
refinement makes all their leaves accessible to deep branch communication.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson BinaryWord

private theorem mixed_of_interior {w : List Bool}
    (h0 : 0 < chart w 0) (h1 : chart w 1 < 1) : false ∈ w ∧ true ∈ w := by
  have hz : ∀ w : List Bool, true ∉ w → chart w 0 = 0 := by
    intro w
    induction w with
    | nil => simp
    | cons b w ih => cases b <;> simp_all [chart]
  have ho : ∀ w : List Bool, false ∉ w → chart w 1 = 1 := by
    intro w
    induction w with
    | nil => simp
    | cons b w ih => cases b <;> simp_all [chart]
  constructor
  · by_contra hw
    rw [ho w hw] at h1
    exact lt_irrefl _ h1
  · by_contra hw
    rw [hz w hw] at h0
    exact lt_irrefl _ h0

private theorem zip_ofFn {α β : Type*} {n : ℕ} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v) = List.ofFn (fun i => (u i, v i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

/-- Enlarge a requested interior interval to fixed dyadic endpoints and
partition the intervening action into branches between mixed binary words. -/
theorem exists_mixed_core_branch_partitions (f : F) (hf : f.1 ∈ compactCore 0)
    {a b : ℚ} (ha : 0 < a) (_hab : a < b) (hb : b < 1) :
    ∃ A B : ℚ, 0 < A ∧ A ≤ a ∧ b ≤ B ∧ B < 1 ∧
      f.1 A = A ∧ f.1 B = B ∧
      ∃ us vs : List (List Bool), WordPartition A B us ∧ WordPartition A B vs ∧
        us.length = vs.length ∧
        (∀ u v, (u, v) ∈ us.zip vs → HasBranch f.1 u v) ∧
        (∀ w ∈ us ++ vs, false ∈ w ∧ true ∈ w) := by
  classical
  obtain ⟨δ, hδ, hfix0, hfix1⟩ := hf.2
  obtain ⟨K, hK⟩ := exists_eventual_grid_branches f
  let ε := min δ (min a (1 - b))
  have hε : 0 < ε := lt_min hδ (lt_min ha (by linarith))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / ε) (show (1 : ℚ) < 2 by norm_num)
  let L := max K N + 1
  have hKL : K ≤ L := (le_max_left K N).trans (Nat.le_succ _)
  have hNL : N ≤ L := (le_max_right K N).trans (Nat.le_succ _)
  have hp : (0 : ℚ) < 2 ^ L := by positivity
  have htwo : 2 ≤ 2 ^ L := by
    have hL1 : 1 ≤ L := by dsimp [L]; omega
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL1
  let A : ℚ := 1 / 2 ^ L
  let B : ℚ := 1 - A
  have hA : 0 < A := div_pos one_pos hp
  have hAε : A < ε := by
    have hpcomp : (2 : ℚ) ^ N ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hNL
    have hex : 1 / ε < (2 : ℚ) ^ L := hN.trans_le hpcomp
    have hmul := (div_lt_iff₀ hε).mp hex
    exact (div_lt_iff₀ hp).mpr (by nlinarith)
  have hAδ : A ≤ δ := hAε.le.trans (min_le_left _ _)
  have hAa : A ≤ a := hAε.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAb : A ≤ 1 - b := hAε.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbB : b ≤ B := by dsimp [B]; linarith
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hfA : f.1 A = A := hfix0 A hAδ
  have hfB : f.1 B = B := hfix1 B (by dsimp [B]; linarith)
  let n := 2 ^ L - 2
  have hn : n + 2 = 2 ^ L := Nat.sub_add_cancel htwo
  have hcell (i : Fin n) := hK L hKL (i.val + 1) (by omega)
  choose u v hu0 hu1 hbranch using hcell
  simp only [Nat.cast_add, Nat.cast_one] at hu0 hu1
  have hstart : gridPt 2 L ((0 : ℕ) + 1) = A := by simp [gridPt, A]
  have hend : gridPt 2 L (n + 1) = B := by
    have hnq : (n : ℚ) + 2 = (2 : ℚ) ^ L := by exact_mod_cast hn
    simp only [gridPt, Nat.cast_ofNat, Int.cast_add, Int.cast_natCast, Int.cast_one]
    dsimp [B, A]
    apply (div_eq_iff hp.ne').mpr
    field_simp
    linarith
  have hpartu : WordPartition A B (List.ofFn u) := by
    have h := WordPartition.ofFn u (fun j => gridPt 2 L (j + 1)) hu0
      (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using hu1 i)
    simpa only [hstart, hend] using h
  have hpartv : WordPartition A B (List.ofFn v) := by
    have hv0 (i : Fin n) : chart (v i) 0 = f.1 (gridPt 2 L (i.val + 1)) := by
      rw [← hu0 i]
      exact (hbranch i).left_endpoint.symm
    have hv1 (i : Fin n) : chart (v i) 1 = f.1 (gridPt 2 L (i.val + 1 + 1)) := by
      rw [← hu1 i]
      exact (hbranch i).right_endpoint.symm
    have h := WordPartition.ofFn v (fun j => f.1 (gridPt 2 L (j + 1))) hv0
      (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using hv1 i)
    simpa only [hstart, hend, hfA, hfB] using h
  refine ⟨A, B, hA, hAa, hbB, hB1, hfA, hfB, List.ofFn u, List.ofFn v,
    hpartu, hpartv, by simp, ?_, ?_⟩
  · intro U V hmem
    rw [zip_ofFn, List.mem_ofFn] at hmem
    obtain ⟨i, hi⟩ := hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
    exact hbranch i
  · intro w hw
    have hbds : A ≤ chart w 0 ∧ chart w 1 ≤ B := by
      rcases List.mem_append.mp hw with hw | hw
      · exact hpartu.mem_bounds hw
      · exact hpartv.mem_bounds hw
    exact mixed_of_interior (hA.trans_le hbds.1) (hbds.2.trans_lt hB1)

namespace BinaryTree

/-- The full binary tree of a prescribed depth. -/
def uniform : ℕ → BinaryTree
  | 0 => .leaf
  | n + 1 => .node (uniform n) (uniform n)

theorem length_of_mem_uniform_leaves {n : ℕ} {w : List Bool}
    (hw : w ∈ (uniform n).leaves) : w.length = n := by
  induction n generalizing w with
  | zero => simpa [uniform] using hw
  | succ n ih =>
    simp only [uniform, leaves_node, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

end BinaryTree

/-- Replace every leaf by its descendants indexed by the same suffix list. -/
def refineWords (ss ws : List (List Bool)) : List (List Bool) :=
  ws.flatMap (fun w => ss.map (w ++ ·))

theorem WordPartition.refineWords {a b : ℚ} {ws ss : List (List Bool)}
    (h : WordPartition a b ws) (hss : WordPartition 0 1 ss) :
    WordPartition a b (refineWords ss ws) := by
  induction h with
  | nil => exact .nil _
  | @cons a b c w ws hl hr ht ih =>
    have hp := hss.prefixWords w
    rw [hl, hr] at hp
    exact hp.append ih

theorem forall₂_branches_refineWords {f : Equiv.Perm ℚ}
    {us vs : List (List Bool)} (h : List.Forall₂ (HasBranch f) us vs)
    (ss : List (List Bool)) :
    List.Forall₂ (HasBranch f) (refineWords ss us) (refineWords ss vs) := by
  induction h with
  | nil => exact .nil
  | @cons u v us vs hhead htail ih =>
    change List.Forall₂ _
      (ss.map (u ++ ·) ++ refineWords ss us) (ss.map (v ++ ·) ++ refineWords ss vs)
    apply List.rel_append ?_ ih
    clear ih
    induction ss with
    | nil => exact .nil
    | cons s ss ihss => exact .cons (hhead.append s) ihss

/-- Deep communication makes the finite branch data of an arbitrary compact
core element available to the local interpolation induction. -/
theorem exists_refined_core_branch_partitions
    {H : Subgroup (Equiv.Perm ℚ)} (hdeep : DeepBranchCommunication H)
    {u : List Bool} (hu : true ∈ u) (f : F) (hf : f.1 ∈ compactCore 0)
    {a b : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ A B : ℚ, 0 < A ∧ A ≤ a ∧ b ≤ B ∧ B < 1 ∧
      f.1 A = A ∧ f.1 B = B ∧
      ∃ us vs : List (List Bool), WordPartition A B us ∧ WordPartition A B vs ∧
        us.length = vs.length ∧
        (∀ U V, (U, V) ∈ us.zip vs → HasBranch f.1 U V) ∧
        (∀ U ∈ us, ZeroExtensionRelated H u U) ∧
        (∀ V ∈ vs, ZeroExtensionRelated H u V) := by
  obtain ⟨A, B, hA, hAa, hbB, hB, hfA, hfB, us, vs, hpus, hpvs, hlen, hbranches, hmix⟩ :=
    exists_mixed_core_branch_partitions f hf ha hab hb
  obtain ⟨N, hN⟩ := hdeep.eventually_zeroExtension_list hu (us ++ vs) hmix
  let ss := (BinaryTree.uniform N).leaves
  have hss : WordPartition 0 1 ss := (BinaryTree.uniform N).leaves_partition
  have hrel : List.Forall₂ (HasBranch f.1) us vs :=
    List.forall₂_iff_zip.mpr ⟨hlen, fun {U V} hp => hbranches U V hp⟩
  have href := forall₂_branches_refineWords hrel ss
  have hzero {ws : List (List Bool)} (hws : ∀ w ∈ ws, w ∈ us ++ vs) :
      ∀ w ∈ refineWords ss ws, ZeroExtensionRelated H u w := by
    intro w hw
    obtain ⟨v, hv, hmem⟩ := List.mem_flatMap.mp hw
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    exact hN v (hws v hv) s (by
      have hlen := BinaryTree.length_of_mem_uniform_leaves hs
      exact hlen.ge)
  refine ⟨A, B, hA, hAa, hbB, hB, hfA, hfB,
    refineWords ss us, refineWords ss vs, hpus.refineWords hss, hpvs.refineWords hss,
    href.length_eq, ?_, ?_, ?_⟩
  · intro U V hmem
    exact (List.forall₂_iff_zip.mp href).2 hmem
  · exact hzero (fun w hw => List.mem_append_left _ hw)
  · exact hzero (fun w hw => List.mem_append_right _ hw)

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.exists_mixed_core_branch_partitions
#audit_axioms Kourovka.P21_38.exists_refined_core_branch_partitions
