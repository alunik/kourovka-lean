import Kourovka2135.MinimalFaithful
import Kourovka2135.NestedNormalExtension
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The conjugation image of a minimal nonabelian normal p-subgroup has the
same simple quotient as the original group. Its centralizer is contained in
the given normal p-subgroup, by the proved faithfulness on N/Z(N).
-/

set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative

/-- Faithfulness of the actual center-quotient representation forces every
element centralizing N into the kernel of the simple quotient. -/
theorem minimal_centralizer_le_pSubgroup
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
    [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] :
    Subgroup.centralizer (N : Set G) ≤ R := by
  intro g hg
  apply (QuotientGroup.eq_one_iff (N := R) g).mp
  apply minimal_center_representation_injective_of_perfect N hN hmin hnonabelian R hR
  rw [map_one]
  apply LinearMap.ext
  intro x
  change normalQuotientRepresentation N (Subgroup.center N) p g
    (Additive.ofMul x.toMul) = Additive.ofMul x.toMul
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
  rw [← hn, normalQuotientRepresentation_apply_mk]
  have hnfix : MulAut.conjNormal g n = n := by
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = n
    rw [← (Subgroup.mem_centralizer_iff.mp hg) n n.property,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [hnfix]

end Kourovka2135
