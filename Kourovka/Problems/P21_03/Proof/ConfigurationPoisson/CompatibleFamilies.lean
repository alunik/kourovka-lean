import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.DisjointFamilies

/-!
# Exact contribution of a compatible witness family

A realizable witness family determines a partial bijection on its distinct
source vertices.  Consequently its realizing permutations are counted by a
single factorial, even when the family has overlaps.
-/

namespace Kourovka213

variable {P Q : BoundedPartition n}

/-- The distinct source vertices occurring in a witness family. -/
noncomputable def witnessFamilySources
    (S : Finset (CollisionWitness P Q)) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (witnessFamilySource S)

/-- The distinct target vertices occurring in a witness family. -/
noncomputable def witnessFamilyTargets
    (S : Finset (CollisionWitness P Q)) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (witnessFamilyTarget S)

@[simp]
theorem mem_witnessFamilySources
    (S : Finset (CollisionWitness P Q)) (x : Fin n) :
    x ∈ witnessFamilySources S ↔
      ∃ i : S × Bool, witnessFamilySource S i = x := by
  classical
  simp [witnessFamilySources]

@[simp]
theorem mem_witnessFamilyTargets
    (S : Finset (CollisionWitness P Q)) (x : Fin n) :
    x ∈ witnessFamilyTargets S ↔
      ∃ i : S × Bool, witnessFamilyTarget S i = x := by
  classical
  simp [witnessFamilyTargets]

/-- A realizing permutation maps the source support of a family bijectively
onto its target support. -/
theorem mem_sources_iff_image_mem_targets
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n)
    (hsigma : WitnessFamilyHolds S sigma) (x : Fin n) :
    x ∈ witnessFamilySources S ↔ sigma x ∈ witnessFamilyTargets S := by
  rw [mem_witnessFamilySources, mem_witnessFamilyTargets]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    exact ((witnessFamilyHolds_iff_forall_oriented S sigma).mp hsigma i).symm
  · rintro ⟨i, hi⟩
    refine ⟨i, sigma.injective ?_⟩
    exact ((witnessFamilyHolds_iff_forall_oriented S sigma).mp hsigma i).trans hi

/-- The partial bijection on the support prescribed by a realizing
permutation. -/
noncomputable def realizingSourceEquiv
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n)
    (hsigma : WitnessFamilyHolds S sigma) :
    {x // x ∈ witnessFamilySources S} ≃
      {x // x ∈ witnessFamilyTargets S} :=
  sigma.subtypeEquiv (mem_sources_iff_image_mem_targets S sigma hsigma)

@[simp]
theorem realizingSourceEquiv_apply_val
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n)
    (hsigma : WitnessFamilyHolds S sigma)
    (x : {x // x ∈ witnessFamilySources S}) :
    ((realizingSourceEquiv S sigma hsigma x :
      {x // x ∈ witnessFamilyTargets S}) : Fin n) = sigma x := by
  rfl

/-- A compatible family has equally many distinct source and target
vertices. -/
theorem card_witnessFamilyTargets_eq_sources
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n)
    (hsigma : WitnessFamilyHolds S sigma) :
    (witnessFamilyTargets S).card = (witnessFamilySources S).card := by
  have hcard := Fintype.card_congr (realizingSourceEquiv S sigma hsigma)
  simpa only [Fintype.card_coe] using hcard.symm

/-- In a compatible family, the left pair uniquely determines a witness. -/
theorem CollisionWitness.eq_of_left_eq_of_holds
    {w v : CollisionWitness P Q} {sigma : Sym n}
    (hleft : w.left = v.left) (hw : w.Holds sigma) (hv : v.Holds sigma) :
    w = v := by
  rcases w with ⟨wl, wr, wf⟩
  rcases v with ⟨vl, vr, vf⟩
  dsimp at hleft
  subst vl
  cases wf <;> cases vf
  · simp only [CollisionWitness.Holds, Bool.false_eq_true, ↓reduceIte] at hw hv
    have hr : wr = vr := by
      cases wr
      cases vr
      simp_all
    subst vr
    rfl

  · simp only [CollisionWitness.Holds, Bool.false_eq_true, ↓reduceIte] at hw hv
    exfalso
    have h1 : wr.fst = vr.snd := hw.1.symm.trans hv.1
    have h2 : wr.snd = vr.fst := hw.2.symm.trans hv.2
    have := wr.fst_lt_snd
    have := vr.fst_lt_snd
    omega
  · simp only [CollisionWitness.Holds, Bool.false_eq_true, ↓reduceIte] at hw hv
    exfalso
    have h1 : wr.snd = vr.fst := hw.1.symm.trans hv.1
    have h2 : wr.fst = vr.snd := hw.2.symm.trans hv.2
    have := wr.fst_lt_snd
    have := vr.fst_lt_snd
    omega
  · simp only [CollisionWitness.Holds, ↓reduceIte] at hw hv
    have hr : wr = vr := by
      cases wr
      cases vr
      simp_all
    subst vr
    rfl

/-- The two oriented source and target endpoints determine a witness. -/
theorem CollisionWitness.eq_of_prescribed_endpoints_eq
    (w v : CollisionWitness P Q)
    (hsource : ∀ b, w.prescribedSource b = v.prescribedSource b)
    (htarget : ∀ b, w.prescribedTarget b = v.prescribedTarget b) :
    w = v := by
  rcases w with ⟨wl, wr, wf⟩
  rcases v with ⟨vl, vr, vf⟩
  have hleft : wl = vl := by
    have h0 := hsource false
    have h1 := hsource true
    simp only [CollisionWitness.prescribedSource] at h0 h1
    cases wl
    cases vl
    simp_all
  subst vl
  cases wf <;> cases vf
  · have h0 := htarget false
    have h1 := htarget true
    simp only [CollisionWitness.prescribedTarget, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] at h0 h1
    have hr : wr = vr := by
      cases wr
      cases vr
      simp_all
    subst vr
    rfl
  · have h0 := htarget false
    have h1 := htarget true
    simp only [CollisionWitness.prescribedTarget, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] at h0 h1
    exfalso
    have := wr.fst_lt_snd
    have := vr.fst_lt_snd
    omega
  · have h0 := htarget false
    have h1 := htarget true
    simp only [CollisionWitness.prescribedTarget, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] at h0 h1
    exfalso
    have := wr.fst_lt_snd
    have := vr.fst_lt_snd
    omega
  · have h0 := htarget false
    have h1 := htarget true
    simp only [CollisionWitness.prescribedTarget, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] at h0 h1
    have hr : wr = vr := by
      cases wr
      cases vr
      simp_all
    subst vr
    rfl

/-- Once one realization is fixed, all other realizations are precisely the
permutations agreeing with it on the distinct source support. -/
theorem witnessFamilyHolds_iff_agrees_on_sources
    (S : Finset (CollisionWitness P Q)) (sigma tau : Sym n)
    (hsigma : WitnessFamilyHolds S sigma) :
    WitnessFamilyHolds S tau ↔
      ∀ x : {x // x ∈ witnessFamilySources S}, tau x = sigma x := by
  constructor
  · intro htau x
    obtain ⟨i, hi⟩ := (mem_witnessFamilySources S x).mp x.2
    have ht := (witnessFamilyHolds_iff_forall_oriented S tau).mp htau i
    have hs := (witnessFamilyHolds_iff_forall_oriented S sigma).mp hsigma i
    change tau x.1 = sigma x.1
    rw [← hi, ht, hs]
  · intro hagree
    rw [witnessFamilyHolds_iff_forall_oriented]
    intro i
    have hmem : witnessFamilySource S i ∈ witnessFamilySources S :=
      (mem_witnessFamilySources S _).mpr ⟨i, rfl⟩
    calc
      tau (witnessFamilySource S i) = sigma (witnessFamilySource S i) :=
        hagree ⟨witnessFamilySource S i, hmem⟩
      _ = witnessFamilyTarget S i :=
        (witnessFamilyHolds_iff_forall_oriented S sigma).mp hsigma i

/-- Every compatible family contributes exactly `(n-r)!`, where `r` is the
number of distinct prescribed sources. -/
theorem card_holdingPermutationsOfFamily_of_nonempty
    (S : Finset (CollisionWitness P Q))
    (hS : (holdingPermutationsOfFamily S).Nonempty) :
    (holdingPermutationsOfFamily S).card =
      (n - (witnessFamilySources S).card).factorial := by
  classical
  obtain ⟨sigma, hsigmaMem⟩ := hS
  have hsigma : WitnessFamilyHolds S sigma := by
    simpa [holdingPermutationsOfFamily] using hsigmaMem
  let e := realizingSourceEquiv S sigma hsigma
  have hcount := card_perm_extending_subtype e
  rw [holdingPermutationsOfFamily]
  have hfilter :
      (Finset.univ.filter (WitnessFamilyHolds S) : Finset (Sym n)) =
        Finset.univ.filter
          (fun tau => ∀ x : {x // x ∈ witnessFamilySources S},
            tau (x : Fin n) = (e x : Fin n)) := by
    ext tau
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [witnessFamilyHolds_iff_agrees_on_sources S sigma tau hsigma]
    constructor
    · intro h x
      simpa [e] using h x
    · intro h x
      simpa [e] using h x
  rw [hfilter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hcount]
  rw [Fintype.card_fin, Fintype.card_coe]

end Kourovka213
