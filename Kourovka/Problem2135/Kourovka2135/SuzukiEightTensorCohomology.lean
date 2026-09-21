import Kourovka2135.SuzukiEightNormCoefficients
import Kourovka2135.TensorCyclicNormRank
import Kourovka2135.SuzukiTensorFactors
import Kourovka2135.PerfectIrreducibleCohomology
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-! Actual H1 bounds for every nonempty natural Frobenius tensor of Sz(8).
Only the two proved generator relations C²=1 and B⁴=1 are used. One factor is
split off; explicit tensor norm projections replace dense matrix certificates. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightTensorCohomology

open SuzukiTorusMovingRank SuzukiTensorNatural SuzukiEightCodeGeometry
open CocycleTwoPowerNorms TensorCyclicNormRank SuzukiEightNormCoefficients
open scoped TensorProduct PiTensorProduct Classical

variable (k : Type) [Field k] [CharP k 2] (σ : K 1 →+* k)
variable (I : Finset (Fin 3)) (i : I)

abbrev Rest := ({i}ᶜ : Set I)
abbrev RestSpace := ⨂[k] _j : Rest I i, (Fin 4 → k)

def restBasis : Module.Basis (Rest I i → Fin 4) k (RestSpace k I i) :=
  Basis.piTensorProduct fun _ : Rest I i => Pi.basisFun k (Fin 4)

instance restFinite : Module.Finite k (RestSpace k I i) :=
  (restBasis k I i).finiteDimensional_of_finite

def restRepresentation : Representation k (G 1) (RestSpace k I i) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun j : Rest I i => naturalTwist k 1 σ j.val.val.val)

def splitLinearEquiv : TensorSpace k 1 I ≃ₗ[k] RestSpace k I i ⊗[k] (Fin 4 → k) :=
  PiTensorProduct.equivPiTensorComplSingletonTensor k (fun _ : I => Fin 4 → k) i

omit [CharP k 2] in
theorem rest_card : Fintype.card (Rest I i) = I.card - 1 := by
  have he : Finset.univ.filter (fun j : I => j ≠ i) = Finset.univ.erase i := by
    ext j
    simp
  change Fintype.card {j : I // j ≠ i} = _
  rw [Fintype.card_subtype, he, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

omit [CharP k 2] in
theorem finrank_rest : Module.finrank k (RestSpace k I i) = 4 ^ (I.card - 1) := by
  rw [Module.finrank_eq_card_basis (restBasis k I i)]
  simp [rest_card I i]

omit [CharP k 2] in
theorem split_tprod (v : I → Fin 4 → k) :
    splitLinearEquiv k I i (PiTensorProduct.tprod k v) =
      (PiTensorProduct.tprod k (fun j : Rest I i => v j.val)) ⊗ₜ[k] v i :=
  PiTensorProduct.equivPiTensorComplSingletonTensor_tprod k (fun _ : I => Fin 4 → k) i v

theorem rest_tprod (g : G 1) (v : Rest I i → Fin 4 → k) :
    restRepresentation k σ I i g (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k
        (fun j : Rest I i => naturalTwist k 1 σ j.val.val.val g (v j)) :=
  PiTensorProduct.map_tprod _ _

theorem split_action (g : G 1) (v : TensorSpace k 1 I) :
    splitLinearEquiv k I i (representation k 1 I σ g v) =
      TensorProduct.map (restRepresentation k σ I i g) (naturalTwist k 1 σ i.val.val g)
        (splitLinearEquiv k I i v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul, representation_tprod, split_tprod,
        TensorProduct.map_tmul, rest_tprod]
  | add v w hv hw => simp only [map_add, hv, hw]

include i in
theorem normTwo_rank :
    2 * 4 ^ (I.card - 1) ≤ Module.finrank k
      (LinearMap.range (normTwo (representation k 1 I σ C))) := by
  have he := finrank_range_eq_of_intertwining (k := k)
    (V := TensorSpace k 1 I) (W := RestSpace k I i ⊗[k] (Fin 4 → k))
    (splitLinearEquiv k I i)
    (normTwo (representation k 1 I σ C))
    (normTwo (TensorProduct.map (restRepresentation k σ I i C)
      (naturalTwist k 1 σ i.val.val C))) (fun v => by
      simp only [normTwo, LinearMap.add_apply, Module.End.one_apply, map_add, split_action])
  rw [he]
  have hr := twice_finrank_le_normTwo_tensor
    (restRepresentation k σ I i C) (naturalTwist k 1 σ i.val.val C)
    (Pi.single 0 1) (Pi.single 1 1)
    (LinearMap.proj (0 : Fin 4)) (LinearMap.proj (1 : Fin 4))
    (by simp) (by simp) (by simp) (by simp)
    (naturalTwist_C_top k σ i.val.val 0 0)
    (naturalTwist_C_top k σ i.val.val 0 1)
    (naturalTwist_C_top k σ i.val.val 1 0)
    (naturalTwist_C_top k σ i.val.val 1 1)
  rw [finrank_rest] at hr
  exact hr

include i in
theorem normFour_rank :
    4 ^ (I.card - 1) ≤ Module.finrank k
      (LinearMap.range (normFour (representation k 1 I σ B))) := by
  have hp (r : ℕ) (v : TensorSpace k 1 I) :
      splitLinearEquiv k I i ((representation k 1 I σ B ^ r) v) =
        (TensorProduct.map (restRepresentation k σ I i B)
          (naturalTwist k 1 σ i.val.val B) ^ r) (splitLinearEquiv k I i v) := by
    simpa only [map_pow, TensorProduct.map_pow] using split_action k σ I i (B ^ r) v
  have he := finrank_range_eq_of_intertwining (k := k)
    (V := TensorSpace k 1 I) (W := RestSpace k I i ⊗[k] (Fin 4 → k))
    (splitLinearEquiv k I i)
    (normFour (representation k 1 I σ B))
    (normFour (TensorProduct.map (restRepresentation k σ I i B)
      (naturalTwist k 1 σ i.val.val B))) (fun v => by
      simp only [normFour, LinearMap.add_apply, Module.End.one_apply, map_add, hp, split_action])
  rw [he]
  have hT : restRepresentation k σ I i B ^ 4 = 1 := by
    rw [← map_pow, B_fourth, map_one]
  have hr := finrank_le_normFour_tensor
    (restRepresentation k σ I i B) (naturalTwist k 1 σ i.val.val B) hT
    (Pi.single 3 1) (LinearMap.proj (0 : Fin 4)) (corner k σ i.val.val)
    (corner_ne_zero k σ i.val.val) (by simp)
    (by simpa using naturalTwist_B_corner k σ i.val.val (0 : Fin 3))
    (by simpa using naturalTwist_B_corner k σ i.val.val (1 : Fin 3))
    (by simpa using naturalTwist_B_corner k σ i.val.val (2 : Fin 3))
  rw [finrank_rest] at hr
  exact hr

theorem invariants_eq_bot (hI : I.Nonempty) :
    (representation k 1 I σ).invariants = ⊥ := by
  let : Representation.IsIrreducible (representation k 1 I σ) :=
    SuzukiTensorFactors.isIrreducible k 1 I σ
  rcases PerfectIrreducibleCohomology.invariants_eq_bot_or_trivial
    (representation k 1 I σ) with h | h
  · exact h
  · have hv := congrArg (fun A : Module.End k (TensorSpace k 1 I) => A (highest k 1 I)) (h C)
    change representation k 1 I σ (weyl 1) (highest k 1 I) = highest k 1 I at hv
    rw [representation_weyl_highest] at hv
    exact False.elim (highest_ne_lowest k 1 I hI hv.symm)

/-- Every nonempty support has H1 dimension at most one quarter of its tensor dimension. -/
theorem finrank_H1_le_quarter (hI : I.Nonempty) :
    Module.finrank k (groupCohomology (Rep.of (representation k 1 I σ)) 1) ≤
      4 ^ (I.card - 1) := by
  obtain ⟨a, ha⟩ := hI
  let i : I := ⟨a, ha⟩
  have hg : Subgroup.closure (Set.range (generators C B)) = ⊤ := by
    rw [show Set.range (generators C B) = {C, B} from Matrix.range_cons_cons_empty _ _ _]
    exact generates
  apply CocycleTwoPowerNorms.finrank_H1_le_quarter (representation k 1 I σ) C B
    hg C_sq B_fourth (invariants_eq_bot k σ I ⟨a, ha⟩) (4 ^ (I.card - 1))
  · rw [finrank_tensor]
    have hcard : 1 ≤ I.card := Finset.one_le_card.mpr ⟨a, ha⟩
    rw [← pow_succ', Nat.sub_add_cancel hcard]
  · exact normTwo_rank k σ I i
  · exact normFour_rank k σ I i

end Kourovka2135.SuzukiEightTensorCohomology
