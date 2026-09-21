import Kourovka2135.FunctionStabilizer
import Kourovka2135.LinearDualCorrection
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
A normal subgroup contained in the Frattini subgroup acts trivially on an
extension of a simple prime-field module by a trivial module if it already
acts trivially on the quotient. The proof uses a functional stabilizer,
avoiding any assumed splitting or cohomology theorem.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {M : Type v} [AddCommGroup M] [Module (ZMod p) M]
variable [FiniteDimensional (ZMod p) M]

def linearDeviation (ρ : Representation (ZMod p) G M)
    (ell : Module.Dual (ZMod p) M) (g : G) : Module.Dual (ZMod p) M :=
  ell.comp (ρ g) - ell

omit [Finite G] [FiniteDimensional (ZMod p) M] in
@[simp] theorem linearDeviation_apply (ρ : Representation (ZMod p) G M)
    (ell : Module.Dual (ZMod p) M) (g : G) (x : M) :
    linearDeviation ρ ell g x = ell (ρ g x - x) := by
  simp [linearDeviation]

theorem frattini_trivial_action_of_simple_quotient
    (ρ : Representation (ZMod p) G M) (W : Submodule (ZMod p) M)
    (hW : ∀ g x, x ∈ W → ρ g x = x)
    (hirr : ∀ U : Submodule (ZMod p) M, W ≤ U →
      (∀ g x, x ∈ U → ρ g x ∈ U) → U = W ∨ U = ⊤)
    (R : Subgroup G) [R.Normal] (hRΦ : R ≤ frattini G)
    (hR : ∀ (r : R) x, ρ (r : G) x - x ∈ W)
    (r : R) (x : M) : ρ (r : G) x = x := by
  classical
  by_contra hne
  obtain ⟨ell, hell⟩ := exists_linear_functional_ne_zero
    (K := ZMod p) (sub_ne_zero.mpr hne)
  let d := linearDeviation ρ ell
  have happly (g h : G) (y : M) : ρ (g * h) y = ρ g (ρ h y) := by
    rw [map_mul]; rfl
  have hmul (a b : R) : d (a * b : R) = d (a : G) + d (b : G) := by
    apply LinearMap.ext
    intro y
    have he : ρ ((a : G) * b) y - y =
        (ρ (a : G) y - y) + (ρ (b : G) y - y) := by
      calc
        _ = ρ (a : G) (ρ (b : G) y - y) + (ρ (a : G) y - y) := by
          rw [happly, map_sub]; abel
        _ = _ := by rw [hW (a : G) _ (hR b y)]; abel
    change ell (ρ ((a : G) * b) y) - ell y =
      (ell (ρ (a : G) y) - ell y) + (ell (ρ (b : G) y) - ell y)
    simpa only [map_sub, map_add, sub_add_eq_add_sub] using congrArg ell he
  let F : R →* Multiplicative (Module.Dual (ZMod p) M) := {
    toFun := fun a => Multiplicative.ofAdd (d (a : G))
    map_one' := by
      change d (1 : G) = 0
      ext y
      simp [d, linearDeviation]
    map_mul' := hmul }
  let L : Submodule (ZMod p) (Module.Dual (ZMod p) M) :=
    AddSubgroup.toZModSubmodule p F.range.toAddSubgroup'
  have hL (f : Module.Dual (ZMod p) M) : f ∈ L ↔ ∃ a : R, d (a : G) = f := Iff.rfl
  let U := L.dualCoannihilator
  have hU (y : M) : y ∈ U ↔ ∀ a : R, d (a : G) y = 0 := by
    constructor
    · intro hy a
      exact (Submodule.mem_dualCoannihilator _).mp hy _ ((hL _).mpr ⟨a, rfl⟩)
    · intro hy
      apply (Submodule.mem_dualCoannihilator _).mpr
      intro f hf
      obtain ⟨a, rfl⟩ := (hL f).mp hf
      exact hy a
  have hWU : W ≤ U := by
    intro y hy
    apply (hU y).mpr
    intro a
    simp only [d, linearDeviation_apply, hW (a : G) y hy, sub_self, map_zero]
  have hconj (g : G) (a : R) (y : M) :
      d (a : G) (ρ g y) =
        d (g⁻¹ * a * g) y := by
    let a' : R := ⟨g⁻¹ * a * g, by
      simpa only [inv_inv] using (inferInstance : R.Normal).conj_mem a a.property g⁻¹⟩
    have he : ρ (a : G) (ρ g y) - ρ g y = ρ g (ρ (a' : G) y - y) := by
      rw [map_sub]
      congr 1
      rw [← happly, ← happly]
      congr 2
      change (a : G) * g = g * (g⁻¹ * a * g)
      group
    simp only [d, linearDeviation_apply]
    rw [he, hW g _ (hR a' y)]
  have hUinv : ∀ g y, y ∈ U → ρ g y ∈ U := by
    intro g y hy
    apply (hU _).mpr
    intro a
    rw [hconj]
    exact (hU y).mp hy ⟨g⁻¹ * a * g, by
      simpa only [inv_inv] using (inferInstance : R.Normal).conj_mem a a.property g⁻¹⟩
  have hUeq : U = W := by
    rcases hirr U hWU hUinv with h | h
    · exact h
    · have hxU : x ∈ U := h ▸ Submodule.mem_top
      apply (hell ?_).elim
      simpa only [d, linearDeviation_apply] using (hU x).mp hxU r
  have hLeq : L = W.dualAnnihilator := by
    have hh : L.dualCoannihilator.dualAnnihilator = L :=
      Subspace.dualCoannihilator_dualAnnihilator_eq
    rw [← hh]
    exact congrArg Submodule.dualAnnihilator hUeq
  let act : MulAction G M := {
    smul := fun g y => ρ g y
    one_smul := by intro y; change ρ 1 y = y; rw [map_one]; rfl
    mul_smul := happly }
  have hc : ∀ g : G, ∃ a ∈ R, ∀ y : M, ell (g • y) = ell (a • y) := by
    intro g
    have hd : d g ∈ L := by
      rw [hLeq]
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro y hy
      simp only [d, linearDeviation_apply, hW g y hy, sub_self, map_zero]
    obtain ⟨a, ha⟩ := (hL _).mp hd
    refine ⟨a, a.property, ?_⟩
    intro y
    have he := congrArg (fun f : Module.Dual (ZMod p) M => f y) ha
    change ell (ρ g y) = ell (ρ (a : G) y)
    change ell (ρ (a : G) y) - ell y = ell (ρ g y) - ell y at he
    exact (sub_left_inj.mp he).symm
  have hstab := functionStabilizer_eq_top_of_frattini_correction (fun y : M => ell y) R hRΦ hc
  have hr : (r : G) ∈ functionStabilizer (fun y : M => ell y) := by
    rw [hstab]; trivial
  apply hell
  rw [map_sub]
  exact sub_eq_zero.mpr (hr x)

end Kourovka2135
