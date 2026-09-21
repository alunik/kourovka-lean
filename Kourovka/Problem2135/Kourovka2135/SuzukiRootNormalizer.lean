import Kourovka2135.SuzukiRootCoordinates
import Kourovka2135.DerivedCentralization
import Kourovka2135.GeneratingSets

/-! A concrete normalized elementary abelian root subgroup in Suzuki.
Every nonidentity torus element gives a nontrivial double commutator. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiRootNormalizer

open BenderSuzuki.MatrixGroups
open SuzukiTorusMovingRank
open scoped MatrixGroups

/-- The central root coordinate, as an actual group element. -/
def rootZero (m : ℕ) (b : K m) : G m :=
  ⟨SuzukiRootGL m 0 b, Subgroup.subset_closure (Or.inl ⟨0, b, rfl⟩)⟩

theorem rootZero_zero (m : ℕ) : rootZero m 0 = 1 :=
  Subtype.ext (SuzukiGeometry.suzukiRootGL_zero_zero m)

theorem rootZero_add (m : ℕ) (a b : K m) :
    rootZero m (a + b) = rootZero m a * rootZero m b := by
  apply Subtype.ext
  change SuzukiRootGL m 0 (a + b) = SuzukiRootGL m 0 a * SuzukiRootGL m 0 b
  simpa only [zero_add, zero_mul, add_zero] using
    (SuzukiGeometry.suzukiRootGL_mul m (tits m) (tits_sq m) (tits_apply m) 0 a 0 b).symm

def zeroHom (m : ℕ) : Multiplicative (K m) →* G m where
  toFun a := rootZero m a.toAdd
  map_one' := rootZero_zero m
  map_mul' a b := rootZero_add m a.toAdd b.toAdd

theorem rootZero_injective (m : ℕ) : Function.Injective (rootZero m) := by
  intro a b hab
  exact (SuzukiGeometry.suzukiRootGL_injective m 0 a 0 b
    (congrArg Subtype.val hab)).2

def U (m : ℕ) : Subgroup (G m) := (zeroHom m).range

theorem mem_U_iff (m : ℕ) (x : G m) : x ∈ U m ↔ ∃ b : K m, rootZero m b = x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toAdd, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨Multiplicative.ofAdd b, hb⟩

theorem isPGroup_U (m : ℕ) : IsPGroup 2 (U m) := by
  have hF : IsPGroup 2 (Multiplicative (K m)) := by
    intro x
    refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    change 2 • x.toAdd = 0
    simp only [two_nsmul, CharTwo.add_self_eq_zero]
  exact hF.of_surjective (zeroHom m).rangeRestrict (zeroHom m).rangeRestrict_surjective

theorem torus_conj_rootZero (m : ℕ) (x : (K m)ˣ) (b : K m) :
    torusHom m x * rootZero m b * (torusHom m x)⁻¹ =
      rootZero m ((x : K m) * tits m (x : K m) * b) := by
  apply Subtype.ext
  change SuzukiTorusGL m x * SuzukiRootGL m 0 b * (SuzukiTorusGL m x)⁻¹ =
    SuzukiRootGL m 0 ((x : K m) * tits m (x : K m) * b)
  simpa only [mul_zero] using
    SuzukiGeometry.suzukiTorusGL_conj_root m (tits m) (tits_sq m) (tits_apply m) 0 b x

theorem torus_normalizes_U (m : ℕ) (x : (K m)ˣ) :
    torusHom m x ∈ Subgroup.normalizer (U m : Set (G m)) := by
  have hle : (torusHom m).range ≤ Subgroup.normalizer (U m : Set (G m)) := by
    apply (Subgroup.le_normalizer_iff).mpr
    intro a ha b hb
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := (mem_U_iff m b).mp hb
    exact (mem_U_iff m _).mpr ⟨_, (torus_conj_rootZero m u c).symm⟩
  exact hle ⟨x, rfl⟩

theorem torus_eq_one_of_commute_rootZero (m : ℕ) (x : (K m)ˣ)
    (b : K m) (hb : b ≠ 0) (h : Commute (torusHom m x) (rootZero m b)) : x = 1 := by
  have he : rootZero m ((x : K m) * tits m (x : K m) * b) = rootZero m b := by
    rw [← torus_conj_rootZero, h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hs : (x : K m) * tits m (x : K m) = 1 :=
    mul_right_cancel₀ hb (by simpa only [one_mul] using rootZero_injective m he)
  apply Units.ext
  exact (twisted_norm_eq_one_iff m _ x.ne_zero).mp hs

theorem double_commutator_ne_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    paperCommutator (torusHom m x)
      ((rootZero m 1)⁻¹ * torusHom m x * rootZero m 1) ≠ 1 := by
  let d := torusHom m x
  let u := rootZero m 1
  have hd : d ∈ Subgroup.normalizer (U m : Set (G m)) := torus_normalizes_U m x
  have hu : u ∈ U m := (mem_U_iff m u).mpr ⟨1, rfl⟩
  have hcomm : paperCommutator d u ∈ U m := by
    apply (U m).mul_mem ?_ hu
    exact (Subgroup.mem_normalizer_iff''.mp hd u⁻¹).mp ((U m).inv_mem hu)
  obtain ⟨b, hb⟩ := (mem_U_iff m _).mp hcomm
  have hb0 : b ≠ 0 := by
    intro he
    have hc : paperCommutator d u = 1 := by rw [← hb, he, rootZero_zero]
    exact hx (torus_eq_one_of_commute_rootZero m x 1 one_ne_zero
      ((paperCommutator_eq_one_iff _ _).mp hc))
  have heq : paperCommutator d (u⁻¹ * d * u) = paperCommutator d (paperCommutator d u) := by
    unfold paperCommutator
    group
  intro hz
  change paperCommutator d (u⁻¹ * d * u) = 1 at hz
  rw [heq, ← hb] at hz
  exact hx (torus_eq_one_of_commute_rootZero m x b hb0 ((paperCommutator_eq_one_iff _ _).mp hz))

end Kourovka2135.SuzukiRootNormalizer
