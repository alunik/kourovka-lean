import Kourovka2135.BinaryNaturalLineTorusAction
import Kourovka2135.NormalJoinInducedCharacter
import Kourovka2135.CoinducedBinaryDeterminant

/-! Construct the actual split-torus coinduced representation from the native
minimal binary kernel. Its degree, central action, trace one and determinant
one are proved from the actual line and actual odd torus lift.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryNaturalInduction

open BinaryNaturalInvariantLine BinaryNaturalLineQuotient
open NormalJoinRightCosets NormalJoinInducedCharacter CoinducedLinearCharacter
open scoped IsMulCommutative

variable (F : Type) [Field F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable (j : SLTwo.SL2 F ≃* (G ⧸ R))
variable (e : (BinaryNaturalPrimeField.representation F).Equiv
  ((minimalCenterRepresentation N hN hmin R hR).comp j.toMonoidHom))
variable (u : Fˣ) (g : G)

local notation "A" => centerLinePreimage F N e.toLinearEquiv
local notation "C" => Subgroup.zpowers g
local notation "S" => Stabilizer N A C
local notation "t" => includeC N C (Subtype.mk g (Subgroup.mem_zpowers g))

include hnonabelian in
/-- The actual split-torus inducing representation has all four required properties. -/
theorem exists_induced
    (hg : QuotientGroup.mk' R g = j (SLTwo.tor u)) (hu : u ≠ 1)
    (hodd : Odd (orderOf g))
    {k : Type} [Field k] [IsAlgClosed k] (χ₀ : Subgroup.center N →* kˣ) :
    ∃ χ : S →* kˣ,
      Module.finrank k (Space S χ) = Nat.card F ∧
      (∀ z : Subgroup.center N,
        (induced S χ).comp (includeN N C) (z : N) =
          (χ₀ z : k) • (1 : Module.End k (Space S χ))) ∧
      (induced S χ).character t = 1 ∧
      LinearMap.det (induced S χ t) = 1 := by
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let : IsMulCommutative A :=
    minimal_centerLinePreimage_isMulCommutative F N hN hmin R hR j e
  have hZA : Subgroup.center N ≤ A := center_le_centerLinePreimage F N e.toLinearEquiv
  have hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G :=
    minimal_noncentral_center_le N hnonabelian hmin
  have hC : Nat.Coprime 2 (Nat.card C) := by
    rw [Nat.card_zpowers]
    exact hodd.coprime_two_left
  have hnorm : C ≤ Subgroup.normalizer ((A).map N.subtype) :=
    Subgroup.zpowers_le.mpr
      (BinaryNaturalLineTorusAction.mem_normalizer_centerLinePreimage_map
        F N hN hmin R hR j e u g hg)
  have hdisjoint : Disjoint N C :=
    IsPGroup.disjoint_of_coprime hN (IsPGroup.card : IsPGroup (Nat.card C) C) hC
  have hAN : (A).map N.subtype ≤ N := by
    rintro x ⟨a, _, rfl⟩
    exact a.property
  have hinter : N ⊓ C ≤ (A).map N.subtype := by
    rw [hdisjoint.eq_bot]
    exact bot_le
  obtain ⟨χ, hχZ, hχC, r, hr⟩ := exists_inducing_character N A C hZA hZ
    (hN.to_subgroup A) hC hnorm (hdisjoint.mono_left hAN) χ₀
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · rw [induced_finrank N A C hnorm hinter]
    exact quotient_card F N e.toLinearEquiv
  · exact induced_center N A C hZA hZ χ₀ χ hχZ
  · apply induced_trace_one N A C hnorm hinter χ hχC
    intro x
    have hτ : conjugationQuotient N A C hnorm ⟨g, Subgroup.mem_zpowers g⟩ =
        BinaryNaturalLineTorusAction.quotientConjugation F N hN hmin R hR j e u g hg := by
      apply MulEquiv.ext
      intro y
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective A y
      rfl
    rw [hτ]
    exact BinaryNaturalLineTorusAction.quotientConjugation_fixed_iff
      F N hN hmin R hR j e u g hg hu x
  · apply CoinducedBinaryDeterminant.det_induced_eq_one_of_odd_pow
      S χ r hr t (orderOf g) hodd
    apply Subtype.ext
    exact pow_orderOf_eq_one g

end Kourovka2135.BinaryNaturalInduction
