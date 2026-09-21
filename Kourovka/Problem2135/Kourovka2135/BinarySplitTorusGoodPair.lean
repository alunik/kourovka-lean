import Kourovka2135.SLTwoUnipotent
import Kourovka2135.RelativeCongruence
import Mathlib.Algebra.CharP.Reduced

/-! Explicit Brandl split-torus commutator witnesses.

The matrix identities and conjugating matrices are actual constructions.
In characteristic two, every nonidentity split-torus element is a commutator
of two elements conjugate to split-torus elements of its own order.
The generation step is a separate finite-group obligation; it is not assumed
or asserted in this matrix-foundation module.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinarySplitTorusGoodPair

open Matrix

variable {F : Type*} [Field F]

/-- Brandl's companion matrix, with the same eigenvalues as tor(u^-1). -/
def companion (u : Fˣ) : SLTwo.SL2 F :=
  ⟨!![0, -1; 1, (u : F) + ((u⁻¹ : Fˣ) : F)], by
    simp [Matrix.det_fin_two_of]⟩

def eigenDifference (u : Fˣ) : F := ((u⁻¹ : Fˣ) : F) - (u : F)

/-- An actual determinant-one eigenbasis, with no appeal to matrix classification. -/
def companionConjugator (u : Fˣ) (hd : eigenDifference u ≠ 0) : SLTwo.SL2 F :=
  ⟨!![1, (eigenDifference u)⁻¹;
      -((u⁻¹ : Fˣ) : F), -(u : F) * (eigenDifference u)⁻¹], by
    simp only [Matrix.det_fin_two_of, one_mul]
    calc
      -(u : F) * (eigenDifference u)⁻¹ -
          (eigenDifference u)⁻¹ * -((u⁻¹ : Fˣ) : F) =
          eigenDifference u * (eigenDifference u)⁻¹ := by
            dsimp [eigenDifference]
            ring
      _ = 1 := mul_inv_cancel₀ hd⟩

theorem companion_mul_conjugator (u : Fˣ) (hd : eigenDifference u ≠ 0) :
    companion u * companionConjugator u hd =
      companionConjugator u hd * SLTwo.tor u⁻¹ := by
  have hu0 : (u : F) ≠ 0 := Units.ne_zero u
  have hd' : (u : F)⁻¹ - (u : F) ≠ 0 := by
    simpa only [eigenDifference, Units.val_inv_eq_inv_val] using hd
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, companionConjugator, eigenDifference, SLTwo.tor,
      Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

theorem companion_conjugate (u : Fˣ) (hd : eigenDifference u ≠ 0) :
    companionConjugator u hd * SLTwo.tor u⁻¹ * (companionConjugator u hd)⁻¹ =
      companion u := by
  rw [← companion_mul_conjugator]
  group

theorem companion_isConj (u : Fˣ) (hd : eigenDifference u ≠ 0) :
    IsConj (SLTwo.tor u⁻¹) (companion u) :=
  isConj_iff.mpr ⟨companionConjugator u hd, companion_conjugate u hd⟩

/-- Brandl's commutator is an explicit unipotent conjugate of tor(u^2). -/
theorem commutator_companion (u : Fˣ) :
    paperCommutator (SLTwo.tor u⁻¹) (companion u) =
      SLTwo.uni (-(u : F)) * SLTwo.tor (u ^ 2) * (SLTwo.uni (-(u : F)))⁻¹ := by
  have hu0 : (u : F) ≠ 0 := Units.ne_zero u
  apply Subtype.ext
  simp only [paperCommutator, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, SLTwo.tor, SLTwo.uni, Matrix.mul_apply,
      Fin.sum_univ_two, Units.val_inv_eq_inv_val, pow_two]
  field_simp
  ring

/-- The first input after transporting the exact commutator back to the torus. -/
def pairLeft (u : Fˣ) : SLTwo.SL2 F :=
  MulAut.conj (SLTwo.uni (-(u : F)))⁻¹ (SLTwo.tor u⁻¹)

/-- The second input after the same actual conjugation. -/
def pairRight (u : Fˣ) : SLTwo.SL2 F :=
  MulAut.conj (SLTwo.uni (-(u : F)))⁻¹ (companion u)

theorem pair_commutator (u : Fˣ) :
    paperCommutator (pairLeft u) (pairRight u) = SLTwo.tor (u ^ 2) := by
  let t := SLTwo.uni (-(u : F))
  have hm := map_paperCommutator (MulAut.conj t⁻¹).toMonoidHom
    (SLTwo.tor u⁻¹) (companion u)
  calc
    paperCommutator (pairLeft u) (pairRight u) =
        MulAut.conj t⁻¹ (paperCommutator (SLTwo.tor u⁻¹) (companion u)) := hm.symm
    _ = SLTwo.tor (u ^ 2) := by
      rw [commutator_companion]
      change t⁻¹ * (t * SLTwo.tor (u ^ 2) * t⁻¹) * (t⁻¹)⁻¹ = SLTwo.tor (u ^ 2)
      group

theorem pairLeft_isConj (u : Fˣ) : IsConj (SLTwo.tor u⁻¹) (pairLeft u) :=
  isConj_iff.mpr ⟨(SLTwo.uni (-(u : F)))⁻¹, rfl⟩

theorem pairRight_isConj (u : Fˣ) (hd : eigenDifference u ≠ 0) :
    IsConj (SLTwo.tor u⁻¹) (pairRight u) :=
  (companion_isConj u hd).trans
    (isConj_iff.mpr ⟨(SLTwo.uni (-(u : F)))⁻¹, rfl⟩)

/-- A conjugacy-invariant set sufficient for the flexible good-set induction.
It avoids requiring a separate classification of all elements of a given order. -/
def splitOrderSet (r : ℕ) : Set (SLTwo.SL2 F) :=
  {g | ∃ u : Fˣ, orderOf u = r ∧ IsConj (SLTwo.tor u) g}

/-- The actual torus homomorphism preserves element order because it is injective. -/
theorem orderOf_tor (u : Fˣ) : orderOf (SLTwo.tor u) = orderOf u :=
  orderOf_injective (SLTwo.torHom F) SLTwo.torHom_injective u

/-- Every member of the actual split-order set has exactly the specified order. -/
theorem orderOf_mem_splitOrderSet {r : ℕ} {g : SLTwo.SL2 F}
    (hg : g ∈ splitOrderSet r) : orderOf g = r := by
  obtain ⟨u, hu, hconj⟩ := hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc]
  calc
    orderOf (c * SLTwo.tor u * c⁻¹) = orderOf (SLTwo.tor u) :=
      (MulAut.conj c).orderOf_eq _
    _ = r := (orderOf_tor u).trans hu

/-- Membership is preserved by actual conjugacy. -/
theorem mem_splitOrderSet_of_isConj {r : ℕ} {a b : SLTwo.SL2 F}
    (ha : a ∈ splitOrderSet r) (hab : IsConj a b) : b ∈ splitOrderSet r := by
  obtain ⟨u, hu, hconj⟩ := ha
  exact ⟨u, hu, hconj.trans hab⟩

/-- The actual split-order set is invariant under every inner automorphism. -/
theorem conjugate_mem_splitOrderSet_iff (r : ℕ) (g x : SLTwo.SL2 F) :
    g * x * g⁻¹ ∈ splitOrderSet r ↔ x ∈ splitOrderSet r := by
  constructor
  · intro h
    exact mem_splitOrderSet_of_isConj h (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  · intro h
    exact mem_splitOrderSet_of_isConj h (isConj_iff.mpr ⟨g, rfl⟩)

theorem pairLeft_mem_splitOrderSet (u : Fˣ) :
    pairLeft u ∈ splitOrderSet (orderOf u) :=
  ⟨u⁻¹, orderOf_inv u, pairLeft_isConj u⟩

theorem pairRight_mem_splitOrderSet (u : Fˣ) (hd : eigenDifference u ≠ 0) :
    pairRight u ∈ splitOrderSet (orderOf u) :=
  ⟨u⁻¹, orderOf_inv u, pairRight_isConj u hd⟩

section CharTwo

variable [CharP F 2]

theorem eigenDifference_ne_zero (u : Fˣ) (hu : u ≠ 1) : eigenDifference u ≠ 0 := by
  intro h
  have he : ((u⁻¹ : Fˣ) : F) = (u : F) := sub_eq_zero.mp h
  have hsq : (u : F) ^ 2 = 1 := by
    calc
      (u : F) ^ 2 = (u : F) * (u : F) := pow_two _
      _ = ((u⁻¹ : Fˣ) : F) * (u : F) := by rw [he]
      _ = 1 := Units.inv_mul u
  have hu' : (u : F) = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hsq
  exact hu (Units.ext hu')

theorem square_injective : Function.Injective (fun u : Fˣ => u ^ 2) := by
  intro u v huv
  apply Units.ext
  apply (frobenius F 2).injective
  simpa only [frobenius_def, Units.val_pow_eq_pow_val] using congrArg Units.val huv

theorem orderOf_square (u : Fˣ) : orderOf (u ^ 2) = orderOf u :=
  orderOf_injective (powMonoidHom 2) square_injective u

/-- Every actual nonidentity split-torus target has exact same-order inputs. -/
theorem exists_pair_tor [Finite F] (v : Fˣ) (hv : v ≠ 1) :
    ∃ a b : SLTwo.SL2 F,
      a ∈ splitOrderSet (orderOf v) ∧ b ∈ splitOrderSet (orderOf v) ∧
      paperCommutator a b = SLTwo.tor v := by
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective square_injective v
  change u ^ 2 = v at hu
  have hune : u ≠ 1 := by intro h; apply hv; rw [← hu, h, one_pow]
  have horder : orderOf u = orderOf v := by rw [← hu, orderOf_square]
  refine ⟨pairLeft u, pairRight u, ?_, ?_, ?_⟩
  · rw [← horder]
    exact pairLeft_mem_splitOrderSet u
  · rw [← horder]
    exact pairRight_mem_splitOrderSet u (eigenDifference_ne_zero u hune)
  · rw [pair_commutator, hu]

end CharTwo

end Kourovka2135.BinarySplitTorusGoodPair
