import Kourovka2135.BinaryNaturalLineQuotient

/-! The actual diagonal action on the actual native line quotient.

The second native coordinate has weight u⁻¹. Actual intertwining and the
representative formula for the minimal-center representation transfer this
to ambient conjugation. The line preimage is consequently preserved, and a
nonidentity diagonal parameter fixes only the identity quotient coset.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryNaturalLineTorusAction

open BinaryNaturalInvariantLine BinaryNaturalLineQuotient
open scoped IsMulCommutative

variable (F : Type) [Field F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual native diagonal matrix acts with weights u and u⁻¹. -/
theorem representation_tor (u : Fˣ) (v : Fin 2 → F) :
    BinaryNaturalPrimeField.representation F (SLTwo.tor u) v =
      ![(u : F) * v 0, ((u⁻¹ : Fˣ) : F) * v 1] := by
  funext i
  fin_cases i <;>
    simp [BinaryNaturalPrimeField.representation_apply, SLTwo.tor_val, Fin.sum_univ_two]

/-- In particular the second coordinate has the inverse diagonal weight. -/
theorem representation_tor_second (u : Fˣ) (v : Fin 2 → F) :
    BinaryNaturalPrimeField.representation F (SLTwo.tor u) v 1 =
      ((u⁻¹ : Fˣ) : F) * v 1 := by
  rw [representation_tor]
  rfl

omit [CharP F 2] in
/-- Multiplication by the inverse of a nonidentity unit fixes only zero. -/
theorem inverse_mul_fixed_iff (u : Fˣ) (hu : u ≠ 1) (x : F) :
    ((u⁻¹ : Fˣ) : F) * x = x ↔ x = 0 := by
  have hi : ((u⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    apply hu
    exact inv_eq_one.mp (Units.ext h)
  simp only [mul_left_eq_self₀, hi, false_or]

section Minimal

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable (j : SLTwo.SL2 F ≃* (G ⧸ R))
variable (e : (BinaryNaturalPrimeField.representation F).Equiv
  ((minimalCenterRepresentation N hN hmin R hR).comp j.toMonoidHom))
variable (u : Fˣ) (g : G) (hg : QuotientGroup.mk' R g = j (SLTwo.tor u))

include hg in
/-- Actual conjugation becomes the actual native diagonal action under e. -/
theorem nativeCoordinates_conj (n : N) :
    e.toLinearEquiv.symm
        (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal g n))) =
      BinaryNaturalPrimeField.representation F (SLTwo.tor u)
        (e.toLinearEquiv.symm
          (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) n))) := by
  let v := e.toLinearEquiv.symm
    (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) n))
  have hv : e.toLinearEquiv v =
      Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) n) :=
    e.toLinearEquiv.apply_symm_apply _
  have he : e.toLinearEquiv (BinaryNaturalPrimeField.representation F (SLTwo.tor u) v) =
      minimalCenterRepresentation N hN hmin R hR (j (SLTwo.tor u)) (e.toLinearEquiv v) :=
    LinearMap.congr_fun (e.isIntertwining' (SLTwo.tor u)) v
  rw [← hg, hv] at he
  change e.toLinearEquiv (BinaryNaturalPrimeField.representation F (SLTwo.tor u) v) =
    Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal g n)) at he
  have h := congrArg e.toLinearEquiv.symm he
  rw [e.toLinearEquiv.symm_apply_apply] at h
  exact h.symm

include hg in
/-- The actual second coordinate of ambient conjugation is multiplied by u⁻¹. -/
theorem secondCoordinate_conj_toAdd (n : N) :
    (secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n)).toAdd =
      ((u⁻¹ : Fˣ) : F) * (secondCoordinate F N e.toLinearEquiv n).toAdd := by
  change e.toLinearEquiv.symm
      (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal g n))) 1 = _
  rw [nativeCoordinates_conj F N hN hmin R hR j e u g hg, representation_tor_second]
  rfl

include hg in
/-- Multiplicative-tag version of the actual coordinate action formula. -/
theorem secondCoordinate_conj (n : N) :
    secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n) =
      Multiplicative.ofAdd
        (((u⁻¹ : Fˣ) : F) * (secondCoordinate F N e.toLinearEquiv n).toAdd) :=
  congrArg Multiplicative.ofAdd
    (secondCoordinate_conj_toAdd F N hN hmin R hR j e u g hg n)

include hg in
/-- The actual line-preimage subgroup is preserved in both directions. -/
theorem conj_mem_centerLinePreimage_iff (n : N) :
    MulAut.conjNormal g n ∈ centerLinePreimage F N e.toLinearEquiv ↔
      n ∈ centerLinePreimage F N e.toLinearEquiv := by
  change (secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n)).toAdd = 0 ↔
    (secondCoordinate F N e.toLinearEquiv n).toAdd = 0
  rw [secondCoordinate_conj_toAdd F N hN hmin R hR j e u g hg]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)
  · intro h
    rw [h, mul_zero]

include hg in
/-- Equality of actual subgroups under the actual conjugation automorphism. -/
theorem map_centerLinePreimage_conj :
    (centerLinePreimage F N e.toLinearEquiv).map
        (MulAut.conjNormal g : MulAut N).toMonoidHom =
      centerLinePreimage F N e.toLinearEquiv := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact (conj_mem_centerLinePreimage_iff F N hN hmin R hR j e u g hg n).mpr hn
  · intro x hx
    refine ⟨(MulAut.conjNormal g : MulAut N).symm x, ?_,
      (MulAut.conjNormal g : MulAut N).apply_symm_apply x⟩
    apply (conj_mem_centerLinePreimage_iff F N hN hmin R hR j e u g hg _).mp
    simpa only [MulEquiv.apply_symm_apply] using hx

include hg in
/-- The actual ambient lift normalizes the actual image of the line preimage. -/
theorem mem_normalizer_centerLinePreimage_map :
    g ∈ Subgroup.normalizer ((centerLinePreimage F N e.toLinearEquiv).map N.subtype) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have h := congrArg (fun A : Subgroup N => A.map N.subtype)
    (map_centerLinePreimage_conj F N hN hmin R hR j e u g hg)
  have hc : N.subtype.comp (MulAut.conjNormal g : MulAut N).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp N.subtype := by
    ext n
    rfl
  rw [Subgroup.map_map, hc, ← Subgroup.map_map] at h
  exact h

include hg in
/-- A fixed second coordinate is zero exactly when the diagonal unit is nonidentity. -/
theorem secondCoordinate_fixed_iff (hu : u ≠ 1) (n : N) :
    secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n) =
        secondCoordinate F N e.toLinearEquiv n ↔
      n ∈ centerLinePreimage F N e.toLinearEquiv := by
  rw [secondCoordinate_conj F N hN hmin R hR j e u g hg]
  change ((u⁻¹ : Fˣ) : F) * (secondCoordinate F N e.toLinearEquiv n).toAdd =
    (secondCoordinate F N e.toLinearEquiv n).toAdd ↔
      (secondCoordinate F N e.toLinearEquiv n).toAdd = 0
  exact inverse_mul_fixed_iff F u hu _

/-- The quotient automorphism is induced by actual ambient conjugation. -/
def quotientConjugation : MulAut (N ⧸ centerLinePreimage F N e.toLinearEquiv) :=
  QuotientGroup.congr _ _ (MulAut.conjNormal g)
    (map_centerLinePreimage_conj F N hN hmin R hR j e u g hg)

@[simp] theorem quotientConjugation_mk (n : N) :
    quotientConjugation F N hN hmin R hR j e u g hg
        (QuotientGroup.mk' (centerLinePreimage F N e.toLinearEquiv) n) =
      QuotientGroup.mk' (centerLinePreimage F N e.toLinearEquiv) (MulAut.conjNormal g n) := rfl

/-- The actual quotient action fixes only the identity coset for u ≠ 1. -/
theorem quotientConjugation_fixed_iff (hu : u ≠ 1)
    (x : N ⧸ centerLinePreimage F N e.toLinearEquiv) :
    quotientConjugation F N hN hmin R hR j e u g hg x = x ↔ x = 1 := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (centerLinePreimage F N e.toLinearEquiv) x
  rw [quotientConjugation_mk]
  constructor
  · intro h
    have hc := congrArg (quotientEquiv F N e.toLinearEquiv) h
    change secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n) =
      secondCoordinate F N e.toLinearEquiv n at hc
    have hn := (secondCoordinate_fixed_iff F N hN hmin R hR j e u g hg hu n).mp hc
    exact (QuotientGroup.eq_one_iff _).mpr hn
  · intro h
    apply (quotientEquiv F N e.toLinearEquiv).injective
    change secondCoordinate F N e.toLinearEquiv (MulAut.conjNormal g n) =
      secondCoordinate F N e.toLinearEquiv n
    exact (secondCoordinate_fixed_iff F N hN hmin R hR j e u g hg hu n).mpr
      ((QuotientGroup.eq_one_iff _).mp h)

end Minimal

end Kourovka2135.BinaryNaturalLineTorusAction
