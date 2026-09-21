import Kourovka2135.BinaryNaturalPrimeField
import Kourovka2135.MinimalInvariantForms
import Kourovka2135.MinimalEndomorphismBound
import Mathlib.LinearAlgebra.BilinearMap

/-! The actual first native field line is isotropic for every invariant binary
bilinear map, including the vector-valued central commutator pairing.

An upper unipotent fixes the first axis and adds any chosen first-axis vector
to `(0,1)`. Invariance and additivity therefore force the pairing on the first
axis to vanish. No identification of a commuting field, classification of
invariant forms, finiteness of the parameter field, or alternating hypothesis
is needed for this argument.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryNaturalInvariantLine

open scoped IsMulCommutative

variable (F : Type) [Field F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

section Bilinear

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Upper-root invariance alone forces every vector-valued binary pairing to
vanish on the actual first field line. -/
theorem bilinear_firstAxis_eq_zero
    (B : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → F) →ₗ[ZMod 2] W)
    (hinv : ∀ (t : F) (x y : Fin 2 → F),
      B (BinaryNaturalPrimeField.representation F (SLTwo.uni t) x)
        (BinaryNaturalPrimeField.representation F (SLTwo.uni t) y) = B x y)
    (x y : F) : B ![x, 0] ![y, 0] = 0 := by
  have hfix : BinaryNaturalPrimeField.representation F (SLTwo.uni y) ![x, 0] =
      ![x, 0] := by
    rw [BinaryNaturalPrimeField.representation_uni]
    simp
  have hmove : BinaryNaturalPrimeField.representation F (SLTwo.uni y) ![0, 1] =
      ![0, 1] + ![y, 0] := by
    rw [BinaryNaturalPrimeField.representation_uni]
    funext j
    fin_cases j <;> simp
  have h := hinv y ![x, 0] ![0, 1]
  rw [hfix, hmove, map_add] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- Membership in the first field line is the concrete second-coordinate test. -/
theorem bilinear_eq_zero_of_secondCoordinate_eq_zero
    (B : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → F) →ₗ[ZMod 2] W)
    (hinv : ∀ (t : F) (x y : Fin 2 → F),
      B (BinaryNaturalPrimeField.representation F (SLTwo.uni t) x)
        (BinaryNaturalPrimeField.representation F (SLTwo.uni t) y) = B x y)
    (x y : Fin 2 → F) (hx : x 1 = 0) (hy : y 1 = 0) : B x y = 0 := by
  have hxe : x = ![x 0, 0] := by
    funext j
    fin_cases j <;> simp [hx]
  have hye : y = ![y 0, 0] := by
    funext j
    fin_cases j <;> simp [hy]
  rw [hxe, hye]
  exact bilinear_firstAxis_eq_zero F B hinv (x 0) (y 0)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) (SLTwo.SL2 F) V)
variable (e : (BinaryNaturalPrimeField.representation F).Equiv ρ)

/-- Transport the line-isotropy statement through an actual intertwining
linear equivalence, without identifying any endomorphism fields. -/
theorem bilinear_equiv_eq_zero_of_secondCoordinate_eq_zero
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hinv : ∀ (t : F) (x y : V), B (ρ (SLTwo.uni t) x) (ρ (SLTwo.uni t) y) = B x y)
    (x y : V) (hx : e.toLinearEquiv.symm x 1 = 0)
    (hy : e.toLinearEquiv.symm y 1 = 0) : B x y = 0 := by
  let C := B.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap
  have hC : ∀ (t : F) (a b : Fin 2 → F),
      C (BinaryNaturalPrimeField.representation F (SLTwo.uni t) a)
        (BinaryNaturalPrimeField.representation F (SLTwo.uni t) b) = C a b := by
    intro t a b
    change B (e (BinaryNaturalPrimeField.representation F (SLTwo.uni t) a))
      (e (BinaryNaturalPrimeField.representation F (SLTwo.uni t) b)) = B (e a) (e b)
    have he (z : Fin 2 → F) :
        e (BinaryNaturalPrimeField.representation F (SLTwo.uni t) z) =
          ρ (SLTwo.uni t) (e z) := LinearMap.congr_fun (e.isIntertwining' (SLTwo.uni t)) z
    rw [he a, he b]
    exact hinv t (e a) (e b)
  have h := bilinear_eq_zero_of_secondCoordinate_eq_zero F C hC
    (e.toLinearEquiv.symm x) (e.toLinearEquiv.symm y) hx hy
  change B (e.toLinearEquiv (e.toLinearEquiv.symm x))
    (e.toLinearEquiv (e.toLinearEquiv.symm y)) = 0 at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end Bilinear

section CenterQuotient

variable (M : Type*) [Group M]
variable [IsElementaryAbelian 2 (M ⧸ Subgroup.center M)]

/-- The actual inverse image in M of the native first field line, under an
actual binary linear identification of M/Z(M). -/
def centerLinePreimage
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] Additive (M ⧸ Subgroup.center M)) : Subgroup M where
  carrier := {a | e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) a)) 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) (a * b))) 1 = 0
    rw [map_mul, ofMul_mul, map_add, Pi.add_apply, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) a⁻¹)) 1 = 0
    rw [map_inv, ofMul_inv, map_neg, Pi.neg_apply, ha, neg_zero]

@[simp] theorem mem_centerLinePreimage
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] Additive (M ⧸ Subgroup.center M)) (a : M) :
    a ∈ centerLinePreimage F M e ↔
      e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) a)) 1 = 0 := Iff.rfl

/-- The preimage contains the actual center. -/
theorem center_le_centerLinePreimage
    (e : (Fin 2 → F) ≃ₗ[ZMod 2] Additive (M ⧸ Subgroup.center M)) :
    Subgroup.center M ≤ centerLinePreimage F M e := by
  intro a ha
  change e.symm (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) a)) 1 = 0
  have hq : QuotientGroup.mk' (Subgroup.center M) a = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ha
  rw [hq, ofMul_one, map_zero]
  rfl

variable [IsElementaryAbelian 2 (commutator M)]
variable (ρ : Representation (ZMod 2) (SLTwo.SL2 F) (Additive (M ⧸ Subgroup.center M)))
variable (e : (BinaryNaturalPrimeField.representation F).Equiv ρ)

/-- Vanishing of the actual vector-valued commutator pairing proves that the
actual line-preimage subgroup is abelian. -/
theorem centerLinePreimage_isMulCommutative
    (hD : commutator M ≤ Subgroup.center M)
    (hinv : ∀ (t : F) (x y : Additive (M ⧸ Subgroup.center M)),
      centralCommutatorBilinearMap hD 2 (ρ (SLTwo.uni t) x) (ρ (SLTwo.uni t) y) =
        centralCommutatorBilinearMap hD 2 x y) :
    IsMulCommutative (centerLinePreimage F M e.toLinearEquiv) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply (paperCommutator_eq_one_iff (a : M) (b : M)).mp
  have h := bilinear_equiv_eq_zero_of_secondCoordinate_eq_zero F ρ e
    (centralCommutatorBilinearMap hD 2) hinv
    (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) a))
    (Additive.ofMul (QuotientGroup.mk' (Subgroup.center M) b)) a.property b.property
  change centralCommutatorPairingHom hD
    (QuotientGroup.mk' (Subgroup.center M) a)
    (QuotientGroup.mk' (Subgroup.center M) b) = 1 at h
  exact congrArg Subtype.val h

end CenterQuotient

section Minimal

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian 2 (commutator N)]

/-- For the actual minimal-center representation, invariance is discharged by
the proved ambient-conjugation formula and quotient surjectivity. -/
theorem minimal_centerLinePreimage_isMulCommutative
    (j : SLTwo.SL2 F ≃* (G ⧸ R))
    (e : (BinaryNaturalPrimeField.representation F).Equiv
      ((minimalCenterRepresentation N hN hmin R hR).comp j.toMonoidHom)) :
    IsMulCommutative (centerLinePreimage F N e.toLinearEquiv) := by
  let : Group.IsNilpotent N := hN.isNilpotent
  apply centerLinePreimage_isMulCommutative F N
    ((minimalCenterRepresentation N hN hmin R hR).comp j.toMonoidHom) e
    (minimal_noncentral_commutator_le_internal_center N hmin)
  intro t x y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R (j (SLTwo.uni t))
  change centralCommutatorBilinearMap _ 2
    (minimalCenterRepresentation N hN hmin R hR (j (SLTwo.uni t)) x)
    (minimalCenterRepresentation N hN hmin R hR (j (SLTwo.uni t)) y) = _
  rw [← hg]
  exact minimal_commutatorBilinearMap_invariant N hmin 2 g x y

end Minimal

end Kourovka2135.BinaryNaturalInvariantLine
