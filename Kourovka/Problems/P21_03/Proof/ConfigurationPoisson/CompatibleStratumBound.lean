import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.WitnessBlockSupport

/-!
# Polynomial count of compatible support strata

Compatible `k`-families on `r < 2k` source vertices are encoded by their two
endpoint maps and their occupied source/target block counts.  The source block
count has a strict factor-two deficit, giving one power of `n` of saving.
-/

namespace Kourovka213

section Enumeration

variable {W : Type*} [Fintype W] [DecidableEq W]

private noncomputable def stratumFamilyEquiv
    (S : Finset W) (hS : S.card = k) : Fin k ≃ S :=
  Fintype.equivOfCardEq (by simpa using hS.symm)

private noncomputable def stratumFamilyTuple
    (S : Finset W) (hS : S.card = k) : Fin k → W :=
  fun i => (stratumFamilyEquiv S hS i).1

private theorem image_stratumFamilyTuple
    (S : Finset W) (hS : S.card = k) :
    Finset.univ.image (stratumFamilyTuple S hS) = S := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hw
    rw [← hi]
    exact (stratumFamilyEquiv S hS i).2
  · intro hw
    obtain ⟨i, hi⟩ := (stratumFamilyEquiv S hS).surjective ⟨w, hw⟩
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩

private theorem image_comp_equiv_univ {A B X : Type*}
    [Fintype A] [Fintype B] [DecidableEq X]
  (e : A ≃ B) (f : B → X) :
    Finset.univ.image (f ∘ e) = Finset.univ.image f := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨e a, Finset.mem_univ _, ha⟩
  · intro hx
    obtain ⟨b, _hb, hb⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨e.symm b, Finset.mem_univ _, by simpa using hb⟩

end Enumeration

section Codes

variable {P Q : BoundedPartition n}

private noncomputable def stratumOrientationEquiv
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool ≃ S × Bool :=
  (stratumFamilyEquiv S hS).prodCongr (Equiv.refl Bool)

private noncomputable def stratumSourceMap
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool → Fin n :=
  witnessFamilySource S ∘ stratumOrientationEquiv S hS

private noncomputable def stratumTargetMap
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool → Fin n :=
  witnessFamilyTarget S ∘ stratumOrientationEquiv S hS

private theorem usedBlockLabels_stratumSourceMap
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    usedBlockLabels P.block (stratumSourceMap S hS) =
      witnessFamilySourceBlocks S := by
  unfold usedBlockLabels stratumSourceMap witnessFamilySourceBlocks
  simpa only [Function.comp_assoc, usedBlockLabels] using
    image_comp_equiv_univ (stratumOrientationEquiv S hS)
      (P.block ∘ witnessFamilySource S)

private theorem usedBlockLabels_stratumTargetMap
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    usedBlockLabels Q.block (stratumTargetMap S hS) =
      witnessFamilyTargetBlocks S := by
  unfold usedBlockLabels stratumTargetMap witnessFamilyTargetBlocks
  simpa only [Function.comp_assoc, usedBlockLabels] using
    image_comp_equiv_univ (stratumOrientationEquiv S hS)
      (Q.block ∘ witnessFamilyTarget S)

/-- Endpoint maps using exactly `b` blocks. -/
def BlockEndpointMaps (R : BoundedPartition n) (k b : ℕ) :=
  {f : Fin k × Bool → Fin n // (usedBlockLabels R.block f).card = b}

noncomputable instance (R : BoundedPartition n) (k b : ℕ) :
    Fintype (BlockEndpointMaps R k b) :=
  Subtype.fintype _

/-- The finite code space used for compatible support-`r` families. -/
def CompatibleStratumCode (P Q : BoundedPartition n) (k r : ℕ) :=
  Σ bs : Fin (r + 1),
    Σ bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r},
      BlockEndpointMaps P k bs.1 × BlockEndpointMaps Q k bt.1

noncomputable instance (P Q : BoundedPartition n) (k r : ℕ) :
    Fintype (CompatibleStratumCode P Q k r) := by
  classical
  unfold CompatibleStratumCode
  infer_instance

private theorem target_support_card_eq_of_stratum
    {S : Finset (CollisionWitness P Q)}
    (hS : S ∈ compatibleWitnessFamiliesBySupport P Q k r) :
    (witnessFamilyTargets S).card = r := by
  have hm := mem_compatibleWitnessFamiliesBySupport.mp hS
  obtain ⟨sigma, hsigmaMem⟩ := hm.2.1
  have hsigma : WitnessFamilyHolds S sigma := by
    simpa [holdingPermutationsOfFamily] using hsigmaMem
  exact (card_witnessFamilyTargets_eq_sources S sigma hsigma).trans hm.2.2

private noncomputable def compatibleStratumEmbedding
    (P Q : BoundedPartition n) (k r : ℕ) (hr : r < 2 * k) :
    ↥(compatibleWitnessFamiliesBySupport P Q k r) ↪
      CompatibleStratumCode P Q k r where
  toFun family := by
    let S := family.1
    have hm := mem_compatibleWitnessFamiliesBySupport.mp family.2
    let sigma := Classical.choose hm.2.1
    have hsigmaMem := Classical.choose_spec hm.2.1
    have hsigma : WitnessFamilyHolds S sigma := by
      dsimp [S, sigma]
      simpa [holdingPermutationsOfFamily] using hsigmaMem
    have hslt : 2 * (witnessFamilySourceBlocks S).card < r := by
      have hraw := two_mul_card_sourceBlocks_lt_of_compatible
        family.1 sigma hsigma hm.1 (hm.2.2.trans_lt hr)
      exact hraw.trans_le hm.2.2.le
    have htcard : (witnessFamilyTargets S).card = r :=
      (card_witnessFamilyTargets_eq_sources S sigma hsigma).trans hm.2.2
    have htle : 2 * (witnessFamilyTargetBlocks S).card ≤ r := by
      rw [← htcard]
      exact two_mul_card_targetBlocks_le_targets S
    let bs : Fin (r + 1) :=
      ⟨(witnessFamilySourceBlocks S).card, by omega⟩
    let bt : Fin (r + 1) :=
      ⟨(witnessFamilyTargetBlocks S).card, by omega⟩
    have hsum : bs.1 + bt.1 < r := by
      dsimp [bs, bt]
      omega
    refine ⟨bs, ⟨⟨bt, hsum⟩, ?_⟩⟩
    exact
      (⟨stratumSourceMap S hm.1,
          congrArg Finset.card (usedBlockLabels_stratumSourceMap S hm.1)⟩,
       ⟨stratumTargetMap S hm.1,
          congrArg Finset.card (usedBlockLabels_stratumTargetMap S hm.1)⟩)
  inj' := by
    classical
    intro family family' hcode
    apply Subtype.ext
    have hm := mem_compatibleWitnessFamiliesBySupport.mp family.2
    have hm' := mem_compatibleWitnessFamiliesBySupport.mp family'.2
    have hsource : stratumSourceMap family.1 hm.1 =
        stratumSourceMap family'.1 hm'.1 :=
      congrArg (fun z : CompatibleStratumCode P Q k r => z.2.2.1.1) hcode
    have htarget : stratumTargetMap family.1 hm.1 =
        stratumTargetMap family'.1 hm'.1 :=
      congrArg (fun z : CompatibleStratumCode P Q k r => z.2.2.2.1) hcode
    have htuple : stratumFamilyTuple family.1 hm.1 =
        stratumFamilyTuple family'.1 hm'.1 := by
      funext i
      apply CollisionWitness.eq_of_prescribed_endpoints_eq
      · intro b
        exact congrFun hsource (i, b)
      · intro b
        exact congrFun htarget (i, b)
    calc
      family.1 = Finset.univ.image (stratumFamilyTuple family.1 hm.1) :=
        (image_stratumFamilyTuple family.1 hm.1).symm
      _ = Finset.univ.image (stratumFamilyTuple family'.1 hm'.1) := by rw [htuple]
      _ = family'.1 := image_stratumFamilyTuple family'.1 hm'.1

/-- Compatible families inject into the endpoint-map code space. -/
theorem card_compatibleWitnessFamiliesBySupport_le_code
    (P Q : BoundedPartition n) (k r : ℕ) (hr : r < 2 * k) :
    (compatibleWitnessFamiliesBySupport P Q k r).card ≤
      Fintype.card (CompatibleStratumCode P Q k r) := by
  calc
    (compatibleWitnessFamiliesBySupport P Q k r).card =
        Fintype.card ↥(compatibleWitnessFamiliesBySupport P Q k r) := by
      rw [Fintype.card_coe]
    _ ≤ Fintype.card (CompatibleStratumCode P Q k r) :=
      Fintype.card_le_of_injective
        (compatibleStratumEmbedding P Q k r hr)
        (compatibleStratumEmbedding P Q k r hr).injective

private theorem card_blockEndpointMaps_le
    (R : BoundedPartition n) (k b r : ℕ) (hbr : b ≤ r) :
    Fintype.card (BlockEndpointMaps R k b) ≤
      n ^ b * (r * 4) ^ (2 * k) := by
  have hraw := card_maps_usedBlockLabels_eq_le
    (I := Fin k × Bool) R.block b 4 R.card_fiber_le_four
  have hraw' : Fintype.card (BlockEndpointMaps R k b) ≤
      n ^ b * (b * 4) ^ (2 * k) := by
    simpa [BlockEndpointMaps, Fintype.card_prod, mul_comm, mul_left_comm,
      mul_assoc] using hraw
  have hlocal : (b * 4) ^ (2 * k) ≤ (r * 4) ^ (2 * k) :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right 4 hbr) _
  exact hraw'.trans (Nat.mul_le_mul_left (n ^ b) hlocal)

private theorem card_code_fiber_le
    (P Q : BoundedPartition n) (k r : ℕ) (hn : 0 < n)
    (bs : Fin (r + 1))
    (bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r}) :
    Fintype.card
        (BlockEndpointMaps P k bs.1 × BlockEndpointMaps Q k bt.1.1) ≤
      n ^ (r - 1) * ((r * 4) ^ (2 * k)) ^ 2 := by
  let A := (r * 4) ^ (2 * k)
  have hbs : bs.1 ≤ r := by omega
  have hbt : bt.1.1 ≤ r := by omega
  have hs := card_blockEndpointMaps_le P k bs.1 r hbs
  have ht := card_blockEndpointMaps_le Q k bt.1.1 r hbt
  have hsum : bs.1 + bt.1.1 ≤ r - 1 := by omega
  have hpow : n ^ (bs.1 + bt.1.1) ≤ n ^ (r - 1) :=
    pow_le_pow_right' (by omega) hsum
  calc
    Fintype.card
        (BlockEndpointMaps P k bs.1 × BlockEndpointMaps Q k bt.1.1) =
        Fintype.card (BlockEndpointMaps P k bs.1) *
          Fintype.card (BlockEndpointMaps Q k bt.1.1) := by
      rw [Fintype.card_prod]
    _ ≤ (n ^ bs.1 * A) * (n ^ bt.1.1 * A) := Nat.mul_le_mul hs ht
    _ = n ^ (bs.1 + bt.1.1) * A ^ 2 := by
      rw [pow_add]
      ring
    _ ≤ n ^ (r - 1) * A ^ 2 := Nat.mul_le_mul_right _ hpow

/-- Explicit `O_{k,r}(n^(r-1))` bound for every compatible lower support
stratum. -/
theorem card_compatibleWitnessFamiliesBySupport_le
    (P Q : BoundedPartition n) (k r : ℕ) (hn : 0 < n)
    (hr : r < 2 * k) :
    (compatibleWitnessFamiliesBySupport P Q k r).card ≤
      (r + 1) ^ 2 *
        (n ^ (r - 1) * ((r * 4) ^ (2 * k)) ^ 2) := by
  classical
  let M := n ^ (r - 1) * ((r * 4) ^ (2 * k)) ^ 2
  have hcode : Fintype.card (CompatibleStratumCode P Q k r) ≤
      (r + 1) ^ 2 * M := by
    unfold CompatibleStratumCode
    rw [Fintype.card_sigma]
    calc
      (∑ bs : Fin (r + 1),
          Fintype.card
            (Σ bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r},
              BlockEndpointMaps P k bs.1 × BlockEndpointMaps Q k bt.1)) ≤
          ∑ _bs : Fin (r + 1), (r + 1) * M := by
        apply Finset.sum_le_sum
        intro bs _hbs
        rw [Fintype.card_sigma]
        calc
          (∑ bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r},
              Fintype.card
                (BlockEndpointMaps P k bs.1 × BlockEndpointMaps Q k bt.1)) ≤
              ∑ _bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r}, M := by
            apply Finset.sum_le_sum
            intro bt _hbt
            exact card_code_fiber_le P Q k r hn bs bt
          _ = Fintype.card {bt : Fin (r + 1) // bs.1 + bt.1 < r} * M := by
            simp
          _ ≤ (r + 1) * M := by
            apply Nat.mul_le_mul_right M
            simpa using Fintype.card_le_of_injective
              (fun bt : {bt : Fin (r + 1) // bs.1 + bt.1 < r} => bt.1)
              (fun _ _ h => Subtype.ext h)
      _ = (r + 1) ^ 2 * M := by
        simp [pow_two]
        ring
  exact (card_compatibleWitnessFamiliesBySupport_le_code P Q k r hr).trans
    (by simpa [M] using hcode)

end Codes

end Kourovka213
