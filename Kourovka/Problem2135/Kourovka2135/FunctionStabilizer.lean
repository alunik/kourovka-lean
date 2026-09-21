import Kourovka2135.SolubleStructure

/-! An orbit correction criterion for escaping the Frattini subgroup. -/

set_option autoImplicit false
universe u v w
namespace Kourovka2135
variable {G : Type u} [Group G] {A : Type v} {B : Type w} [MulAction G A]

/-- Elements whose action preserves a given function. -/
def functionStabilizer (f : A → B) : Subgroup G where
  carrier := {g | ∀ x, f (g • x) = f x}
  one_mem' := by intro x; rw [one_smul]
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    rw [smul_inv_smul] at h
    exact h.symm

theorem functionStabilizer_sup_eq_top_of_correction (f : A → B) (N : Subgroup G)
    (hc : ∀ g : G, ∃ n ∈ N, ∀ x : A, f (g • x) = f (n • x)) :
    functionStabilizer f ⊔ N = ⊤ := by
  apply top_le_iff.mp
  intro g _
  obtain ⟨n, hn, heq⟩ := hc g
  have hh : g * n⁻¹ ∈ functionStabilizer f := by
    intro x
    rw [mul_smul, heq, smul_inv_smul]
  have hm := (functionStabilizer f ⊔ N).mul_mem
    ((show functionStabilizer f ≤ functionStabilizer f ⊔ N from le_sup_left) hh)
    ((show N ≤ functionStabilizer f ⊔ N from le_sup_right) hn)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

theorem functionStabilizer_eq_top_of_frattini_correction [Finite G]
    (f : A → B) (N : Subgroup G) (hN : N ≤ frattini G)
    (hc : ∀ g : G, ∃ n ∈ N, ∀ x : A, f (g • x) = f (n • x)) :
    functionStabilizer (G := G) f = ⊤ := by
  apply frattini_nongenerating
  apply top_le_iff.mp
  rw [← functionStabilizer_sup_eq_top_of_correction f N hc]
  exact sup_le_sup_left hN _

end Kourovka2135
