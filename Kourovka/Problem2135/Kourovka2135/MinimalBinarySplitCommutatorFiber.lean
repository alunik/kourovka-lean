import Kourovka2135.RelativeCommutatorFiber
import Kourovka2135.MinimalBinarySplitTorusTrace
import Kourovka2135.CharacterQuotientConjugacy

/-! Actual terminal nonspecial binary commutator fibers at nonidentity odd
split-torus lifts. Every nonlinear extension and character sum is constructed
by the imported proofs. No representation or character inequality is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

/-- The terminal nonspecial binary kernel admits every prescribed odd split
output in a relative commutator fiber over a generating pair. -/
theorem minimal_binary_split_commutator_fiber
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ N))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (n : N)
    (s : Fˣ) (hs : s ≠ 1)
    (himage : j.symm (QuotientGroup.mk' N (paperCommutator a b * (n : G))) =
      SLTwo.tor s)
    (hodd : Odd (orderOf (paperCommutator a b * (n : G)))) :
    ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) =
      paperCommutator a b * (n : G) := by
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  apply RelativeCommutatorFiber.exists_paperCommutator_eq N
    (commutator_eq_self_of_minimal_noncentral N hnc hmin) a b hgen n
  intro V _ _ _ ρ hirred hdim
  let : ρ.IsIrreducible := hirred
  obtain ⟨α, hα, _, htrace⟩ :=
    minimal_binary_nonlinear_character_extends_split_torus_trace
      N hN hmin hnonabelian hNΦ hnonspecial j f hcard hf ρ hdim
  refine ⟨α, hα, htrace s⁻¹ (inv_ne_one.mpr hs)
    (paperCommutator a b * (n : G))⁻¹ ?_ ?_⟩
  · rw [map_inv, map_inv, himage, SLTwo.tor_inv]
  · simpa only [orderOf_inv] using hodd

/-- The same fiber theorem for every conjugate of a nonidentity split-torus
element in the actual quotient. Only the quotient conjugator is chosen. -/
theorem minimal_binary_split_conjugate_commutator_fiber
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ N))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (n : N)
    (s : Fˣ) (hs : s ≠ 1)
    (himage : IsConj (j.symm (QuotientGroup.mk' N (paperCommutator a b * (n : G))))
      (SLTwo.tor s))
    (hodd : Odd (orderOf (paperCommutator a b * (n : G)))) :
    ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) =
      paperCommutator a b * (n : G) := by
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  apply RelativeCommutatorFiber.exists_paperCommutator_eq N
    (commutator_eq_self_of_minimal_noncentral N hnc hmin) a b hgen n
  intro V _ _ _ ρ hirred hdim
  let : ρ.IsIrreducible := hirred
  obtain ⟨α, hα, _, htrace⟩ :=
    minimal_binary_nonlinear_character_extends_split_torus_trace
      N hN hmin hnonabelian hNΦ hnonspecial j f hcard hf ρ hdim
  refine ⟨α, hα, ?_⟩
  apply CharacterQuotientConjugacy.eq_of_isConj
    (j.symm.toMonoidHom.comp (QuotientGroup.mk' N))
    (j.symm.surjective.comp (QuotientGroup.mk'_surjective N))
    α 1 (SLTwo.tor s⁻¹) (htrace s⁻¹ (inv_ne_one.mpr hs))
    (paperCommutator a b * (n : G))⁻¹
  · simpa only [orderOf_inv] using hodd
  · obtain ⟨z, hz⟩ := isConj_iff.mp himage
    apply isConj_iff.mpr
    refine ⟨z, ?_⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv,
      map_mul, mul_inv_rev, inv_inv, mul_assoc, SLTwo.tor_inv] using congrArg Inv.inv hz

end Kourovka2135
