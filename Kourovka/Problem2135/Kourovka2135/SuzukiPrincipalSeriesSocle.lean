import Kourovka2135.SuzukiPrincipalSeriesCoordinates
import Kourovka2135.IrreducibleImageComparison

/-! Uniqueness of the irreducible socle at a nontrivial torus character.
The argument concerns actual principal-series functions. Every nonzero
proper submodule has a root-fixed vector with coordinates (0,1); those
coordinates determine the vector. Consequently any actual proper simple
model determines every irreducible source at the same character. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SuzukiPrincipalSeriesSocle

open SuzukiGeometry SuzukiPrincipalSeries SuzukiPrincipalSeriesBorel
open SuzukiPrincipalSeriesCoordinates

variable (m : ℕ) {k : Type u} [Field k] [CharP k 2]
variable (σ : K m →+* k) (n : ℕ)

/-- A nonzero reduced exponent has two distinct opposite torus weights. -/
theorem exists_distinct_weights (hn : 0 < n) (hnq : n < Nat.card (K m) - 1) :
    ∃ a : (K m)ˣ, σ (a : K m) ^ n ≠ σ ((a⁻¹ : (K m)ˣ) : K m) ^ n := by
  classical
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (K m)ˣ)
  have horder : orderOf a = Nat.card (K m) - 1 := by
    simpa only [Nat.card_units] using ha
  refine ⟨a, ?_⟩
  intro he
  have hs : (σ (a : K m) ^ n) ^ 2 = 1 := by
    calc
      _ = σ (a : K m) ^ n * σ (a : K m) ^ n := pow_two _
      _ = σ (a : K m) ^ n * σ ((a⁻¹ : (K m)ˣ) : K m) ^ n :=
        congrArg (fun x : k => σ (a : K m) ^ n * x) he
      _ = 1 := by rw [← mul_pow, ← map_mul]; simp
  have hp : σ (a : K m) ^ n = 1 := by
    simpa only [sq_eq_one_iff, CharTwo.neg_eq, or_self] using hs
  have hpa : (a : K m) ^ n = 1 := σ.injective (by simpa only [map_pow, map_one] using hp)
  have hau : a ^ n = 1 := Units.ext
    (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hpa)
  exact pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hn) (by rwa [horder]) hau

omit [CharP k 2] in
/-- In a proper stable subspace the first root-fixed coordinate must vanish. -/
theorem rootFixed_one_eq_zero (S : Submodule k (Space m σ n)) (hproper : S ≠ ⊤)
    (hstable : ∀ (g : G m) (f : Space m σ n), f ∈ S → representation m σ n g f ∈ S)
    (a : (K m)ˣ)
    (ha : σ (a : K m) ^ n ≠ σ ((a⁻¹ : (K m)ˣ) : K m) ^ n)
    (f : Space m σ n) (hfS : f ∈ S) (hf : RootFixed m σ n f) : f.val 1 = 0 := by
  by_contra h1
  let α := σ (a : K m) ^ n
  let β := σ ((a⁻¹ : (K m)ˣ) : K m) ^ n
  let t := SuzukiTorusMovingRank.torusHom m a
  have htf := rootFixed_torus m σ n f hf a
  have he : representation m σ n t f - α • f =
      ((β - α) * f.val 1) • delta m σ n := by
    apply rootFixed_ext m σ n
    · intro r
      rw [map_sub, map_smul, htf r, hf r]
    · intro r
      rw [map_smul, delta_rootFixed m σ n r]
    · change (representation m σ n t f).val 1 - α * f.val 1 =
        ((β - α) * f.val 1) * (delta m σ n).val 1
      rw [delta_one, torus_coordinate_one]
      dsimp [α, β]
      ring
    · change (representation m σ n t f).val (weyl m) - α * f.val (weyl m) =
        ((β - α) * f.val 1) * (delta m σ n).val (weyl m)
      rw [delta_weyl, torus_coordinate_weyl]
      dsimp [α]
      ring
  have hm := S.sub_mem (hstable t f hfS) (S.smul_mem α hfS)
  rw [he] at hm
  have hc : (β - α) * f.val 1 ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha)) h1
  exact hproper (eq_top_of_delta_mem m σ n S hstable ((S.smul_mem_iff hc).mp hm))

/-- The canonical coordinates (0,1) are attained in every nonzero proper
stable subspace. Their vector is constructed there, rather than assumed. -/
theorem exists_normalized_rootFixed (S : Submodule k (Space m σ n))
    (hS : S ≠ ⊥) (hproper : S ≠ ⊤)
    (hstable : ∀ (g : G m) (f : Space m σ n), f ∈ S → representation m σ n g f ∈ S)
    (hn : 0 < n) (hnq : n < Nat.card (K m) - 1) :
    ∃ f ∈ S, RootFixed m σ n f ∧ f.val 1 = 0 ∧ f.val (weyl m) = 1 := by
  let : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS
  let τ : Representation k (root m) S :=
    Representation.subrepresentation ((representation m σ n).comp (root m).subtype) S
      (fun r v hv => hstable (r : G m) v hv)
  obtain ⟨f, hf, hfix⟩ := PGroupInvariantFunctional.exists_nonzero_fixed (k := k) (V := S) τ (root_isPGroup m)
  have hfix' : RootFixed m σ n f.val := fun r => congrArg Subtype.val (hfix r)
  obtain ⟨a, ha⟩ := exists_distinct_weights m σ n hn hnq
  have h1 := rootFixed_one_eq_zero m σ n S hproper hstable a ha f.val f.property hfix'
  have hW : f.val.val (weyl m) ≠ 0 := by
    intro he
    apply hf
    apply Subtype.ext
    apply rootFixed_ext m σ n f.val 0 hfix' (fun r => map_zero _)
    · exact h1
    · exact he
  refine ⟨(f.val.val (weyl m))⁻¹ • f.val, S.smul_mem _ f.property, ?_, ?_, ?_⟩
  · intro r
    rw [map_smul, hfix' r]
  · change (f.val.val (weyl m))⁻¹ * f.val.val 1 = 0
    rw [h1, mul_zero]
  · change (f.val.val (weyl m))⁻¹ * f.val.val (weyl m) = 1
    exact inv_mul_cancel₀ hW

/-- Two genuine nonzero proper subrepresentations have a shared nonzero vector. -/
theorem exists_common_nonzero (S T : Subrepresentation (representation m σ n))
    (hS : S ≠ ⊥) (hSproper : S ≠ ⊤) (hT : T ≠ ⊥) (hTproper : T ≠ ⊤)
    (hn : 0 < n) (hnq : n < Nat.card (K m) - 1) :
    ∃ f : Space m σ n, f ≠ 0 ∧ f ∈ S ∧ f ∈ T := by
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  have hSp' : S.toSubmodule ≠ ⊤ := fun h => hSproper (Subrepresentation.toSubmodule_injective h)
  have hT' : T.toSubmodule ≠ ⊥ := fun h => hT (Subrepresentation.toSubmodule_injective h)
  have hTp' : T.toSubmodule ≠ ⊤ := fun h => hTproper (Subrepresentation.toSubmodule_injective h)
  obtain ⟨f, hfS, hf, hf1, hfW⟩ := exists_normalized_rootFixed m σ n
    S.toSubmodule hS' hSp' (fun g v hv => S.apply_mem_toSubmodule g hv) hn hnq
  obtain ⟨g, hgT, hg, hg1, hgW⟩ := exists_normalized_rootFixed m σ n
    T.toSubmodule hT' hTp' (fun a v hv => T.apply_mem_toSubmodule a hv) hn hnq
  have he : f = g := rootFixed_ext m σ n f g hf hg (hf1.trans hg1.symm) (hfW.trans hgW.symm)
  refine ⟨f, ?_, hfS, he.symm ▸ hgT⟩
  intro hz
  have h10 : (1 : k) = 0 := hfW.symm.trans (congrArg (fun v : Space m σ n => v.val (weyl m)) hz)
  exact one_ne_zero h10

variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (G m) V} {τ : Representation k (G m) W}
variable [ρ.IsIrreducible] [τ.IsIrreducible]

/-- An actual proper simple model at this character determines every simple
source embedded in the principal series. Only the model's properness is
needed; the other image's properness is derived. -/
def equivOfProperModel (j : ρ.IntertwiningMap (representation m σ n)) (hj : j ≠ 0)
    (e : τ.IntertwiningMap (representation m σ n)) (he : e ≠ 0)
    (heproper : e.range ≠ ⊤) (hn : 0 < n) (hnq : n < Nat.card (K m) - 1) : ρ.Equiv τ := by
  classical
  apply Classical.choice
  have hje : ∃ v : V, j v ≠ 0 := by
    by_contra h
    push Not at h
    exact hj (Representation.IntertwiningMap.ext (LinearMap.ext h))
  have hee : ∃ v : W, e v ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨v, hv⟩ := hje
  obtain ⟨w, hw⟩ := hee
  have hjbot : j.range ≠ ⊥ := by
    intro hb
    have hm : j v ∈ j.range := ⟨v, rfl⟩
    rw [hb] at hm
    exact hv hm
  have hebot : e.range ≠ ⊥ := by
    intro hb
    have hm : e w ∈ e.range := ⟨w, rfl⟩
    rw [hb] at hm
    exact hw hm
  have hjproper := IrreducibleImageComparison.range_ne_top_of_nonzero_proper
    j e.range heproper (e w) hw ⟨w, rfl⟩
  obtain ⟨z, hz, hzj, hze⟩ := exists_common_nonzero m σ n
    j.range e.range hjbot hjproper hebot heproper hn hnq
  exact ⟨IrreducibleImageComparison.equivOfNonzeroCommon j e z hz hzj hze⟩

end Kourovka2135.SuzukiPrincipalSeriesSocle
