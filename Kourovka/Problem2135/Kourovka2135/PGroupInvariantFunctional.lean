import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Fixed vectors for finite p-groups in characteristic p, without a
finite-dimensionality hypothesis. The proof applies the ordinary finite-set
p-group fixed-point theorem to the finite prime-field span of one orbit.
The algebraic-dual corollary supplies actual invariant linear functionals. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.PGroupInvariantFunctional

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Every nonzero representation of a finite p-group in characteristic p
contains an actual nonzero fixed vector. -/
theorem exists_nonzero_fixed [Nontrivial V]
    (ρ : Representation k G V) (hG : IsPGroup p G) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range (fun g : G => ρ g v))
  have hvW : v ∈ W := by
    apply Submodule.subset_span (R := ZMod p)
    exact ⟨1, by simp⟩
  have hstable (g : G) (x : V) (hx : x ∈ W) : ρ g x ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        apply Submodule.subset_span (R := ZMod p)
        exact ⟨g * h, congrArg (fun T : Module.End k V => T v) (ρ.map_mul g h)⟩
    | zero => simpa only [map_zero] using W.zero_mem
    | add x y hx hy hix hiy =>
        simpa only [map_add] using W.add_mem hix hiy
    | smul a x hx hix =>
        rw [ZMod.map_smul (ρ g)]
        exact W.smul_mem a hix
  let : MulAction G W := {
    smul g x := ⟨ρ g x.val, hstable g x.val x.property⟩
    one_smul x := Subtype.ext (by change ρ 1 x.val = x.val; simp)
    mul_smul g h x := Subtype.ext
      (congrArg (fun T : Module.End k V => T x.val) (ρ.map_mul g h)) }
  let : Module.Finite (ZMod p) W :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_range (fun g : G => ρ g v))
  let : Finite W := Module.finite_of_finite (ZMod p)
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (by
    intro hW
    have he : v = 0 := by simpa only [hW, Submodule.mem_bot] using hvW
    exact hv he)
  have hdim : 0 < Module.finrank (ZMod p) W := Module.finrank_pos
  have hcard : p ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_eq_fintype_card,
      ZMod.card]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdim)
    rw [hn, pow_succ]
    exact dvd_mul_left p _
  have hzero : (0 : W) ∈ MulAction.fixedPoints G W := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    exact map_zero (ρ g)
  obtain ⟨x, hx, hne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard hzero
  refine ⟨x.val, ?_, ?_⟩
  · intro he
    exact hne (Subtype.ext he.symm)
  · intro g
    exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hx) g)

/-- The actual algebraic dual has a nonzero invariant functional. -/
theorem exists_nonzero_invariant_functional [Nontrivial V]
    (ρ : Representation k G V) (hG : IsPGroup p G) :
    ∃ ell : Module.Dual k V, ell ≠ 0 ∧
      ∀ (g : G) (v : V), ell (ρ g v) = ell v := by
  let : Nontrivial (Module.Dual k V) := (Module.nontrivial_dual_iff k).mpr inferInstance
  obtain ⟨ell, hell, hfix⟩ := exists_nonzero_fixed ρ.dual hG
  refine ⟨ell, hell, ?_⟩
  intro g v
  have he := congrArg (fun l : Module.Dual k V => l (ρ g v)) (hfix g)
  change ell ((ρ g⁻¹ * ρ g) v) = ell (ρ g v) at he
  rw [← map_mul, inv_mul_cancel, map_one] at he
  exact he.symm

end Kourovka2135.PGroupInvariantFunctional
