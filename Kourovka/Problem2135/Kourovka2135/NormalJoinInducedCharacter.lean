import Kourovka2135.NormalJoinRightCosets
import Kourovka2135.CentralCharacterOddSupplement
import Kourovka2135.CoinducedLinearCharacter

/-! Actual inducing characters and their coinduced representations on a
normal-subgroup join. All subgroup embeddings and scalar restrictions below
are the actual inclusions; no representation model is supplied as a premise.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.NormalJoinInducedCharacter

open NormalJoinRightCosets CoinducedLinearCharacter
open scoped IsMulCommutative

variable {G k : Type*} [Group G] [Field k]
variable (N : Subgroup G) (A : Subgroup N) (C : Subgroup G)

/-- The actual stabilizer is the ambient subgroup join with its ambient type restricted. -/
def stabilizerEquiv : Stabilizer N A C ≃* ↥(A.map N.subtype ⊔ C) :=
  Subgroup.subgroupOfEquivOfLe
    (show A.map N.subtype ⊔ C ≤ N ⊔ C from sup_le
      (by
        rintro x ⟨a, _, rfl⟩
        exact Subgroup.mem_sup_left a.property)
      le_sup_right)

def supplementInStabilizer : C →* Stabilizer N A C where
  toFun c := ⟨includeC N C c, Subgroup.mem_sup_right c.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def centerInStabilizer (hZA : Subgroup.center N ≤ A) :
    Subgroup.center N →* Stabilizer N A C where
  toFun z := ⟨includeN N C (z : N),
    Subgroup.mem_sup_left (Subgroup.mem_map_of_mem N.subtype (hZA z.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable [Finite G] [IsAlgClosed k]

/-- Construct the actual inducing character from its prescribed central character. -/
theorem exists_inducing_character [IsMulCommutative A]
    (hZA : Subgroup.center N ≤ A)
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (hA : IsPGroup 2 A) (hC : Nat.Coprime 2 (Nat.card C))
    (hnorm : C ≤ Subgroup.normalizer (A.map N.subtype))
    (hdisjoint : Disjoint (A.map N.subtype) C)
    (χ₀ : Subgroup.center N →* kˣ) :
    ∃ χ : Stabilizer N A C →* kˣ,
      χ.comp (centerInStabilizer N A C hZA) = χ₀ ∧
      χ.comp (supplementInStabilizer N A C) = 1 ∧
      ∃ r : ℕ, ∀ s : Stabilizer N A C, χ s ^ (2 ^ r) = 1 := by
  let eZ := (Subgroup.center N).equivMapOfInjective N.subtype Subtype.val_injective
  let eA := A.equivMapOfInjective N.subtype Subtype.val_injective
  let χZ : (Subgroup.center N).map N.subtype →* kˣ := χ₀.comp eZ.symm.toMonoidHom
  obtain ⟨χJ, hχZ, hχC, r, hr⟩ := CentralCharacterOddSupplement.exists_extension
    ((Subgroup.center N).map N.subtype) (A.map N.subtype) C
    (Subgroup.map_mono hZA) hZ (hA.of_equiv eA) hC hnorm hdisjoint χZ
  let χ := χJ.comp (stabilizerEquiv N A C).toMonoidHom
  refine ⟨χ, ?_, ?_, r, fun s => hr (stabilizerEquiv N A C s)⟩
  · apply MonoidHom.ext
    intro z
    have hz := DFunLike.congr_fun hχZ (eZ z)
    change χJ (Subgroup.inclusion ((Subgroup.map_mono hZA).trans le_sup_left) (eZ z)) =
      χZ (eZ z) at hz
    have he : stabilizerEquiv N A C (centerInStabilizer N A C hZA z) =
        Subgroup.inclusion ((Subgroup.map_mono hZA).trans le_sup_left) (eZ z) := by
      apply Subtype.ext
      rfl
    change χJ (stabilizerEquiv N A C (centerInStabilizer N A C hZA z)) = χ₀ z
    rw [he, hz]
    exact congrArg χ₀ (eZ.symm_apply_apply z)
  · apply MonoidHom.ext
    intro c
    exact DFunLike.congr_fun hχC c

omit [IsAlgClosed k] in
/-- Exact dimension from the actual coset equivalence. -/
theorem induced_finrank [N.Normal]
    (hnorm : C ≤ Subgroup.normalizer (A.map N.subtype))
    (hinter : N ⊓ C ≤ A.map N.subtype)
    (χ : Stabilizer N A C →* kˣ) :
    Module.finrank k (Space (Stabilizer N A C) χ) = Nat.card (N ⧸ A) := by
  rw [finrank_space]
  exact Nat.card_congr (cosetEquiv N A C hnorm hinter).symm

omit [IsAlgClosed k] [Finite G] in
/-- The actual restricted coinduced representation has the prescribed central scalar action. -/
theorem induced_center
    (hZA : Subgroup.center N ≤ A)
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (χ₀ : Subgroup.center N →* kˣ) (χ : Stabilizer N A C →* kˣ)
    (hχ : χ.comp (centerInStabilizer N A C hZA) = χ₀)
    (z : Subgroup.center N) :
    (induced (Stabilizer N A C) χ).comp (includeN N C) (z : N) =
      (χ₀ z : k) • (1 : Module.End k (Space (Stabilizer N A C) χ)) := by
  have hz : (includeN N C (z : N)) ∈ Subgroup.center (Ambient N C) := by
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hZ (Subgroup.mem_map_of_mem N.subtype z.property)) (h : G)
  have hc := induced_central (Stabilizer N A C) χ (centerInStabilizer N A C hZA z) hz
  change induced (Stabilizer N A C) χ (includeN N C (z : N)) = _
  change induced (Stabilizer N A C) χ (includeN N C (z : N)) =
    (χ (centerInStabilizer N A C hZA z) : k) •
      (1 : Module.End k (Space (Stabilizer N A C) χ)) at hc
  rw [hc]
  exact congrArg (fun u : kˣ => (u : k) • (1 : Module.End k (Space (Stabilizer N A C) χ)))
    (DFunLike.congr_fun hχ z)

omit [IsAlgClosed k] in
/-- The unique fixed quotient point forces trace one for an inducing character trivial on C. -/
theorem induced_trace_one [N.Normal] [A.Normal]
    (hnorm : C ≤ Subgroup.normalizer (A.map N.subtype))
    (hinter : N ⊓ C ≤ A.map N.subtype)
    (χ : Stabilizer N A C →* kˣ)
    (hχ : χ.comp (supplementInStabilizer N A C) = 1)
    (c : C)
    (hfix : ∀ x : N ⧸ A, conjugationQuotient N A C hnorm c x = x ↔ x = 1) :
    (induced (Stabilizer N A C) χ).character (includeC N C c) = 1 := by
  have ht := character_eq_of_unique_fixed_coset (Stabilizer N A C) χ
    (supplementInStabilizer N A C c)
    (rightCoset_fixed_iff N A C hnorm hinter c hfix)
  change (induced (Stabilizer N A C) χ).character (includeC N C c) = _ at ht
  rw [ht]
  exact congrArg (fun u : kˣ => (u : k)) (DFunLike.congr_fun hχ c)

end Kourovka2135.NormalJoinInducedCharacter
