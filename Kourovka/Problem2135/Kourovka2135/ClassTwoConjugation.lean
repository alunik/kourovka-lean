import Kourovka2135.ClassTwoAdditiveMaps
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Conjugation in the corrected additive structure. -/

set_option autoImplicit false
universe u
namespace Kourovka2135.ClassTwoAdditive
variable {G : Type u} [Group G] (D : ClassTwoData G)

theorem ofMul_conj_eq_add (n x : G) :
    ofMul D (n * x * n⁻¹) = ofMul D x +
      centralEmbedding D (commutator G) D.central
        (Additive.ofMul ⟨paperCommutator n x, paperCommutator_mem_commutator n x⟩) := by
  apply toMul_injective D
  change n * x * n⁻¹ = classTwoSum D.halfExponent x (paperCommutator n x)
  have hc : Commute x (paperCommutator n x) :=
    Subgroup.mem_center_iff.mp (D.central (paperCommutator_mem_commutator n x)) x
  rw [classTwoSum_of_commute _ _ _ hc]
  have hn : Commute n (paperCommutator n x) :=
    Subgroup.mem_center_iff.mp (D.central (paperCommutator_mem_commutator n x)) n
  have hrel : n * x = x * n * paperCommutator n x := by
    simp only [paperCommutator]
    group
  rw [hrel, mul_assoc x n, hn.eq]
  group

/-- Ambient conjugation transported to the corrected additive group of a normal subgroup. -/
abbrev normalConjugationAction (N : Subgroup G) [N.Normal] (E : ClassTwoData N) :
    MulAction G (ClassTwoAdditive E) :=
  MulAction.compHom _ ((mapPermHom E).comp (MulAut.conjNormal : G →* MulAut N))

theorem normalConjugation_fixed_of_center
    (N : Subgroup G) [N.Normal] (E : ClassTwoData N)
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (g : G) (x : ClassTwoAdditive E) (hx : toMul E x ∈ Subgroup.center N) :
    mapAut E (MulAut.conjNormal g) x = x := by
  apply toMul_injective E
  apply Subtype.ext
  have hc : Commute g ((toMul E x : N) : G) := Subgroup.mem_center_iff.mp
    (hZ (Subgroup.mem_map_of_mem N.subtype hx)) g
  change g * ((toMul E x : N) : G) * g⁻¹ = ((toMul E x : N) : G)
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

end Kourovka2135.ClassTwoAdditive
