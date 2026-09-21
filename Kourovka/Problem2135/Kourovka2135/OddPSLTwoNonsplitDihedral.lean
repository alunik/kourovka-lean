import Kourovka2135.OddPSLTwoNonsplitNormTorus

/-! The actual nonsplit torus and Frobenius reflection generate an odd-index
subgroup of PSL₂(F) when the field cardinality is three modulo four.
This uses the proved SL₂ order and scalar center, not a subgroup classification.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoNonsplitDihedral

open OddPSLTwoProjectiveChart

variable (F : Type*) [Field F] [Finite F]

theorem ringChar_ne_two (hmod : Nat.card F % 4 = 3) : ringChar F ≠ 2 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  intro hchar
  have heven : Nat.card F % 2 = 0 := by
    simpa only [Nat.card_eq_fintype_card] using
      (FiniteField.even_card_iff_char_two (F := F)).mp hchar
  omega

/-- The actual scalar center supplies the division-free projective order. -/
theorem twice_card_projective (hp : ringChar F ≠ 2) :
    2 * Nat.card (Q F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hz : Nat.card (Subgroup.center (SLTwo.SL2 F)) = 2 := by
    calc
      _ = Nat.card (rootsOfUnity 2 F) := by
        simpa only [Fintype.card_fin] using Nat.card_congr
          (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F)
            (0 : Fin 2)).toEquiv
      _ = 2 := (IsPrimitiveRoot.neg_one (ringChar F) hp).card_rootsOfUnity
  have h := (Subgroup.center (SLTwo.SL2 F)).card_mul_index
  rw [hz, SLTwo.sl2_card_formula F] at h
  exact h

/-- A cyclic torus and one actual reflection generate their supremum on its
native subgroup type. -/
theorem cyclic_sup_generators {G : Type*} [Group G]
    (T : Subgroup G) [IsCyclic T] (w : G)
    (hw : ∀ t : G, t ∈ T → w * t * w⁻¹ = t⁻¹) :
    ∃ a b : (T ⊔ Subgroup.zpowers w : Subgroup G),
      Subgroup.closure ({a, b} : Set (T ⊔ Subgroup.zpowers w : Subgroup G)) = ⊤ ∧
      b * a * b⁻¹ = a⁻¹ := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := T)
  have hT : T = Subgroup.zpowers (t : G) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨n, hn⟩ := ht ⟨s, hs⟩
      have he : (t : G) ^ n = s := congrArg Subtype.val hn
      rw [← he]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
    · exact Subgroup.zpowers_le.mpr t.property
  let D : Subgroup G := T ⊔ Subgroup.zpowers w
  let a : D := ⟨t, (show T ≤ D from le_sup_left) t.property⟩
  let b : D := ⟨w, (show Subgroup.zpowers w ≤ D from le_sup_right) (Subgroup.mem_zpowers w)⟩
  have hgen : Subgroup.closure ({(t : G), w} : Set G) = D := by
    change _ = T ⊔ Subgroup.zpowers w
    conv_rhs => rw [hT]
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    congr 1
  refine ⟨a, b, ?_, Subtype.ext (hw t t.property)⟩
  apply Subgroup.map_injective D.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hgen

/-- An actual odd-index two-generator inversion subgroup. This includes q=3;
no simplicity, lower field-size, or classification hypothesis is required. -/
theorem exists_odd_index_subgroup (hmod : Nat.card F % 4 = 3) :
    ∃ D : Subgroup (Q F), Odd D.index ∧
      ∃ a b : D, Subgroup.closure ({a, b} : Set D) = ⊤ ∧ b * a * b⁻¹ = a⁻¹ := by
  let : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  have hp := ringChar_ne_two F hmod
  obtain ⟨T, w, hcyclic, _, hTcard, _, _, _, hconj, hDcard⟩ :=
    OddPSLTwoNonsplitNormTorus.norm_torus_reflection_data F (ringChar F) hp
  let : IsCyclic T := hcyclic
  let D : Subgroup (Q F) := T ⊔ Subgroup.zpowers w
  have hcard : Nat.card D = Nat.card F + 1 := by
    change Nat.card (T ⊔ Subgroup.zpowers w : Subgroup (Q F)) = _
    rw [hDcard, mul_comm, hTcard]
  have hindex_card : D.index * (Nat.card F + 1) = Nat.card (Q F) := by
    rw [← hcard]
    exact D.index_mul_card
  have hqpos : 1 ≤ Nat.card F := (Finite.one_lt_card (α := F)).le
  have hfactor : (Nat.card F - 1) * (Nat.card F + 1) = Nat.card F ^ 2 - 1 := by
    simpa only [mul_comm] using (Nat.pow_two_sub_pow_two (Nat.card F) 1).symm
  have htwice : 2 * D.index = Nat.card F * (Nat.card F - 1) := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card F + 1)
    calc
      2 * D.index * (Nat.card F + 1) = 2 * Nat.card (Q F) := by
        rw [mul_assoc, hindex_card]
      _ = Nat.card F * (Nat.card F ^ 2 - 1) := twice_card_projective F hp
      _ = Nat.card F * (Nat.card F - 1) * (Nat.card F + 1) := by
        rw [← hfactor, mul_assoc]
  have hhalf : 2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by omega
  have hindex : D.index = Nat.card F * ((Nat.card F - 1) / 2) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    rw [htwice]
    calc
      Nat.card F * (Nat.card F - 1) = Nat.card F * (2 * ((Nat.card F - 1) / 2)) := by
        rw [hhalf]
      _ = 2 * (Nat.card F * ((Nat.card F - 1) / 2)) := by ring
  refine ⟨D, ?_, cyclic_sup_generators T w hconj⟩
  rw [hindex]
  exact (show Odd (Nat.card F) from ⟨2 * (Nat.card F / 4) + 1, by omega⟩).mul
    (show Odd ((Nat.card F - 1) / 2) from ⟨Nat.card F / 4, by omega⟩)

end Kourovka2135.OddPSLTwoNonsplitDihedral
