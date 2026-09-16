import Kourovka.Problems.P21_38.Proof.AffineBranches
import Kourovka.Problems.P21_38.Proof.PLSplice
import Kourovka.Problems.P21_38.Proof.EndpointSlopes
import Kourovka.Problems.P21_38.Proof.BinaryPartitions

/-!
# Realizing finite dyadic branch data

The construction glues global affine pieces on a finite dyadic partition.
The resulting element acts on the actual rational line and belongs to `F`.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- Match two consecutive dyadic partitions of equal finite length. -/
theorem exists_pl_of_wordPartitions {a b c d : ℚ} {us vs : List (List Bool)}
    (hu : WordPartition a b us) (hv : WordPartition c d vs)
    (hlen : us.length = vs.length)
    (ha : ∃ N, a ∈ Grid 2 N) (hc : ∃ N, c ∈ Grid 2 N) :
    ∃ f ∈ PLGroup 2 (powSlopes 0), f a = c ∧ f b = d ∧
      ∀ u v, (u, v) ∈ us.zip vs → HasBranch f u v := by
  induction hu generalizing c d vs with
  | nil a =>
    have hvs : vs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst vs
    cases hv
    obtain ⟨Na, ha⟩ := ha
    obtain ⟨Nc, hc⟩ := hc
    have hshift : c - a ∈ Grid 2 (max Na Nc) :=
      grid_sub (grid_mono (le_max_right _ _) hc) (grid_mono (le_max_left _ _) ha)
    refine ⟨transPerm (c - a), transPerm_mem 0 hshift, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  | @cons a b e u us hlu hru htu ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      cases hv with
      | @cons _ _ e' _ _ hlv hrv htv =>
        have hlen' : us.length = vs.length := by simpa using hlen
        obtain ⟨f, hf, hfe, hfb, hbranches⟩ := ih htv hlen'
          (hru ▸ BinaryWord.chart_one_dyadic u) (hrv ▸ BinaryWord.chart_one_dyadic v)
        let q := branchAffine u v
        have hq := branchAffine_mem u v
        have hjoin : q e = f e := by
          change branchAffine u v e = f e
          calc branchAffine u v e = BinaryWord.chart v 1 := by rw [← hru, branchAffine_chart]
               _ = e' := hrv
               _ = f e := hfe.symm
        let p := splicePerm q f e hq.1 hf.1 hjoin
        have hp : p ∈ PLGroup 2 (powSlopes 0) :=
          splicePerm_mem_PLGroup hq hf (hru ▸ BinaryWord.chart_one_dyadic u) hjoin
        refine ⟨p, hp, ?_, ?_, ?_⟩
        · change spliceFun q f e a = c
          have hae : a ≤ e := by
            rw [← hlu, ← hru]
            exact (BinaryWord.chart_zero_lt_one u).le
          rw [spliceFun_left _ _ hae]
          change branchAffine u v a = c
          rw [← hlu, branchAffine_chart, hlv]
        · change spliceFun q f e b = d
          rw [spliceFun_right hjoin htu.le, hfb]
        · intro u' v' hmem t ht
          rw [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · obtain ⟨hu', hv'⟩ := Prod.mk.inj heq
            subst u'
            subst v'
            change spliceFun q f e (BinaryWord.chart u t) = _
            have hte : BinaryWord.chart u t ≤ e := by
              rw [← hru]
              exact (BinaryWord.chart_strictMono u).monotone ht.2
            rw [spliceFun_left _ _ hte]
            exact branchAffine_chart u v t
          · change spliceFun q f e (BinaryWord.chart u' t) = _
            have huleaf : u' ∈ us := (List.of_mem_zip hmem).1
            have het : e ≤ BinaryWord.chart u' t :=
              (htu.mem_bounds huleaf).1.trans ((BinaryWord.chart_strictMono u').monotone ht.1)
            rw [spliceFun_right hjoin het]
            exact hbranches u' v' hmem t ht

/-- Restrict a dyadic PL permutation fixing 0 and 1 to the unit interval. -/
theorem exists_interval_restriction {f : Equiv.Perm ℚ}
    (hf : f ∈ PLGroup 2 (powSlopes 0)) (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    ∃ g : F, ∀ t ∈ Set.Icc (0 : ℚ) 1, g.1 t = f t := by
  have h0 : (1 : Equiv.Perm ℚ) 0 = f 0 := hf0.symm
  let p := splicePerm 1 f 0 strictMono_id hf.1 h0
  have hp : p ∈ PLGroup 2 (powSlopes 0) :=
    splicePerm_mem_PLGroup (PLGroup 2 (powSlopes 0)).one_mem hf
      ⟨0, int_mem_grid (m := 2) 0 0⟩ h0
  have hp0 (t : ℚ) (ht : t ≤ 0) : p t = t := spliceFun_left _ _ ht
  have hpf (t : ℚ) (ht : 0 ≤ t) : p t = f t := spliceFun_right h0 ht
  have h1 : p 1 = (1 : Equiv.Perm ℚ) 1 := by rw [hpf 1 (by norm_num), hf1]; rfl
  let g := splicePerm p 1 1 hp.1 strictMono_id h1
  have hg : g ∈ compactF 0 1 := by
    refine ⟨splicePerm_mem_PLGroup hp (PLGroup 2 (powSlopes 0)).one_mem
      ⟨0, int_mem_grid (m := 2) 0 1⟩ h1, ?_, ?_⟩
    · intro t ht
      change spliceFun p (⇑(1 : Equiv.Perm ℚ)) 1 t = t
      rw [spliceFun_left _ _ (by linarith)]
      exact hp0 t ht
    · intro t ht
      change spliceFun p (⇑(1 : Equiv.Perm ℚ)) 1 t = t
      exact spliceFun_right h1 ht
  refine ⟨⟨g, hg⟩, fun t ht => ?_⟩
  change spliceFun p (⇑(1 : Equiv.Perm ℚ)) 1 t = f t
  rw [spliceFun_left _ _ ht.2, hpf t ht.1]

#audit_axioms exists_interval_restriction

/-- Every finite tree pair with the same number of leaves gives an actual element of `F`. -/
theorem exists_treePair (T U : BinaryTree) (hlen : T.leaves.length = U.leaves.length) :
    ∃ f : F, ∀ u v, (u, v) ∈ T.leaves.zip U.leaves → HasBranch f.1 u v := by
  obtain ⟨f, hf, hf0, hf1, hbranches⟩ := exists_pl_of_wordPartitions
    T.leaves_partition U.leaves_partition hlen
    ⟨0, int_mem_grid (m := 2) 0 0⟩ ⟨0, int_mem_grid (m := 2) 0 0⟩
  obtain ⟨g, hg⟩ := exists_interval_restriction hf hf0 hf1
  refine ⟨g, fun u v huv t ht => ?_⟩
  rw [hg _ (BinaryWord.chart_mem_unit u ht)]
  exact hbranches u v huv t ht

#audit_axioms exists_pl_of_wordPartitions
#audit_axioms exists_treePair

end Kourovka.P21_38
