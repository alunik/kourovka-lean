import Kourovka2135.OddCanonicalCentralGoodSet
import Kourovka2135.PGroupSubgroupLift
import Kourovka2135.CentralNormalizerPersistence
import Kourovka2135.MinimalDerivedVanishing

/-! Coprime persistent commutators from actual quotient normalizers.

An actual q-subgroup is lifted by Sylow theory. A chosen canonical good-set
lift normalizes its image because the remaining kernel is central and has
p-power order. The finite-kernel normalizer theorem then corrects its lift
inside [R,G], retaining membership in the full lifted good set. This gives
a nonidentity coprime value of every outer word. The least-exception
corollary explicitly requires a noncentral radical; the unrestricted central
odd-prime case is not asserted here.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.OddCanonicalNormalizerObstruction

variable {G : Type u} [Group G] [Finite G]

/-- Lift a normalizing good-set element without taking a power or changing
its actual canonical-quotient value. -/
theorem exists_normalizing_persistent_lift [Group.IsPerfect G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hodd : p ≠ 2) (hqp : q ≠ p)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hF : R ≤ frattini G)
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B)
    (P : Subgroup G) (hP : IsPGroup q P)
    (d : G ⧸ R) (hd : d ∈ B)
    (hdnorm : d ∈ Subgroup.normalizer (P.map (QuotientGroup.mk' R) : Set (G ⧸ R))) :
    ∃ a : G, a ∈ Subgroup.normalizer (P : Set G) ∧
      QuotientGroup.mk' R a = d ∧ ∀ v : OuterWord, a ∈ v.values G := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let D := ⁅R, (⊤ : Subgroup G)⁆
  let κ : G →* (G ⧸ D) := QuotientGroup.mk' D
  let π : (G ⧸ D) →* (G ⧸ R) := OddCanonicalCentralGoodSet.projection R
  let C := OddCanonicalCentralGoodSet.canonicalGoodSet R B
  have hfactor : π.comp κ = QuotientGroup.mk' R := rfl
  have hπker : IsPGroup p π.ker := by
    change IsPGroup p (NestedNormalExtension.projection D R
      (Subgroup.commutator_le_left _ _)).ker
    rw [NestedNormalExtension.projection_ker]
    exact hR.map κ
  have hκker : IsPGroup p κ.ker := by
    rw [show κ = QuotientGroup.mk' D from rfl, QuotientGroup.ker_mk']
    exact hR.to_le (Subgroup.commutator_le_left _ _)
  have hCimage : π '' C = B := OddCanonicalCentralGoodSet.image_canonicalGoodSet R hB
  have hdimage : d ∈ π '' C := by rwa [hCimage]
  obtain ⟨c, hc, hcd⟩ := hdimage
  have hPimage : (P.map κ).map π = P.map (QuotientGroup.mk' R) := by
    rw [Subgroup.map_map, hfactor]
  have hcnorm : c ∈ Subgroup.normalizer (P.map κ : Set (G ⧸ D)) := by
    apply CentralNormalizerPersistence.mem_normalizer_of_image π hπker
      (OddCanonicalCentralGoodSet.projection_kernel_central R)
      (P.map κ) (hP.map κ) hqp c
    rw [hPimage, hcd]
    exact hdnorm
  obtain ⟨a, ha, hac⟩ := NormalizerCoprimeKernelLift.exists_lift_normalizer κ
    (QuotientGroup.mk'_surjective D) hκker P hP hqp c hcnorm
  have hpre : IsGeneratingGoodSet (κ ⁻¹' C) :=
    OddCanonicalCentralGoodSet.isGeneratingGoodSet_full_preimage hp hodd R hR hF hB
  refine ⟨a, ha, ?_, ?_⟩
  · change π (κ a) = d
    rw [hac]
    exact hcd
  · intro v
    apply hpre.subset_values v
    change κ a ∈ C
    rwa [hac]

/-- A quotient good-set normalizer witness yields an actual nonidentity
coprime value of every outer word in the original group. -/
theorem exists_coprime_persistent_commutator [Group.IsPerfect G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hodd : p ≠ 2) (hqp : q ≠ p)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hF : R ≤ frattini G)
    {B : Set (G ⧸ R)} (hB : IsGeneratingGoodSet B)
    (U : Subgroup (G ⧸ R)) (hU : IsPGroup q U)
    (d x : G ⧸ R) (hd : d ∈ B)
    (hdnorm : d ∈ Subgroup.normalizer (U : Set (G ⧸ R))) (hx : x ∈ U)
    (hne : paperCommutator d (x⁻¹ * d * x) ≠ 1) :
    ∃ z : G, z ≠ 1 ∧ ¬ p ∣ orderOf z ∧ ∀ v : OuterWord, z ∈ v.values G := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let π := QuotientGroup.mk' R
  obtain ⟨P, hP, hPU⟩ := PGroupSubgroupLift.exists_subgroup_map_eq π
    (QuotientGroup.mk'_surjective R) U hU
  have hdnorm' : d ∈ Subgroup.normalizer (P.map π : Set (G ⧸ R)) := by
    rwa [hPU]
  obtain ⟨a, ha, had, hav⟩ := exists_normalizing_persistent_lift hp hq hodd hqp
    R hR hF hB P hP d hd hdnorm'
  change π a = d at had
  have hximage : x ∈ P.map π := by rwa [hPU]
  obtain ⟨b, hb, hbx⟩ := hximage
  let z := paperCommutator a (b⁻¹ * a * b)
  have hzP : z ∈ P := CentralNormalizerPersistence.conjugate_commutator_mem P a b ha hb
  have hz : z ≠ 1 := by
    intro he
    apply hne
    have hmap := congrArg π he
    simpa only [z, paperCommutator, map_mul, map_inv, map_one, had, hbx] using hmap
  have hcop : Nat.Coprime p (orderOf z) := by
    have hc := hP.orderOf_coprime ((Nat.coprime_primes hq hp).mpr hqp)
      (⟨z, hzP⟩ : P)
    simpa only [Subgroup.orderOf_mk] using hc.symm
  refine ⟨z, hz, hp.coprime_iff_not_dvd.mp hcop, ?_⟩
  intro v
  cases v with
  | leaf => exact ⟨z, rfl⟩
  | bracket left right =>
      exact (OuterWord.mem_values_bracket left right z).mpr
        ⟨a, hav left, b⁻¹ * a * b, right.conj_mem_values (hav right) b, rfl⟩

end Kourovka2135.OddCanonicalNormalizerObstruction

namespace Kourovka2135

/-- A genuine normalized coprime subgroup witness excludes an odd-prime
least exception with noncentral radical. The central-radical case remains
outside the scope of this theorem. -/
theorem OrderMinimalException.false_of_odd_quotient_normalizer_good_set
    {G : Type u} [Group G] [Finite G] {w : OuterWord} {p q : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hq : q.Prime)
    (hodd : p ≠ 2) (hqp : q ≠ p)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    {B : Set (G ⧸ solubleRadical G)} (hB : IsGeneratingGoodSet B)
    (U : Subgroup (G ⧸ solubleRadical G)) (hU : IsPGroup q U)
    (d x : G ⧸ solubleRadical G) (hd : d ∈ B)
    (hdnorm : d ∈ Subgroup.normalizer (U : Set (G ⧸ solubleRadical G)))
    (hx : x ∈ U) (hne : paperCommutator d (x⁻¹ * d * x) ≠ 1) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect G := h.isPerfect hp
  have hR : IsPGroup p (solubleRadical G) := by
    rw [h.radical_eq_pCore hp]
    exact pCore_isPGroup
  obtain ⟨z, hz, hzp, hzv⟩ :=
    OddCanonicalNormalizerObstruction.exists_coprime_persistent_commutator
      hp hq hodd hqp (solubleRadical G) hR (h.radical_le_frattini hp)
      hB U hU d x hd hdnorm hx hne
  exact hz (h.derivedValue_eq_one_of_coprime hp hnoncentral le_rfl
    (hzv (OuterWord.derivedWord w.height)) hzp)

end Kourovka2135
