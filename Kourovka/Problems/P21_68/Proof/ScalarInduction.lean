import Kourovka.External.TauCeti.RepresentationTheory.Induction.Mackey.Irreducible
import Kourovka.Problems.P21_68.Proof.Obstruction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

open CategoryTheory

namespace Kourovka.P21_68

set_option backward.isDefEq.respectTransparency.types false

/-- Distinct scalar actions of a normal subgroup kill every unwanted Mackey
intertwiner. This is the little-group irreducibility argument used below. -/
theorem mackeyDisjoint_of_scalar {G : Type} [Group G]
    (N I : Subgroup G) [N.Normal] (hNI : N ≤ I)
    (lam : N →* ℂˣ) (V : FDRep ℂ I)
    (hscalar : ∀ (n : N) v, V.ρ (Subgroup.inclusion hNI n) v = (lam n : ℂ) • v)
    (s : G) (n : N)
    (hne : lam n ≠ lam (MulAut.conjNormal s⁻¹ n)) :
    TauCeti.MackeyDisjoint V s := by
  apply TauCeti.mackeyDisjoint_of_forall_eq_zero
  intro φ
  let f : V →ₗ[ℂ] V := φ.hom.hom.hom
  let n' : N := MulAut.conjNormal s⁻¹ n
  have hn' : s⁻¹ * (n : G) * s ∈ I := by
    simpa [n', MulAut.conjNormal_apply] using hNI n'.property
  let t : (TauCeti.mackeySubgroup s I I).subgroupOf I :=
    ⟨Subgroup.inclusion hNI n, by
      rw [Subgroup.mem_subgroupOf, TauCeti.mem_mackeySubgroup_iff]
      exact ⟨hNI n.property, hn'⟩⟩
  have ht : TauCeti.mackeyToH s I I t = Subgroup.inclusion hNI n' := by
    apply Subtype.ext
    simp [t, n']
  have hzero : ∀ v : V, f v = 0 := by
    intro v
    have hc := congrArg (fun f => f.hom.hom v) (φ.comm t)
    change f (V.ρ (Subgroup.inclusion hNI n) v) =
      V.ρ (TauCeti.mackeyToH s I I t) (f v) at hc
    rw [ht, hscalar, hscalar, map_smul] at hc
    have hcoeff : (lam n : ℂ) ≠ (lam n' : ℂ) := fun h => hne (Units.ext h)
    exact ((smul_eq_zero.mp (by
      rw [sub_smul, hc, sub_self] : ((lam n : ℂ) - (lam n' : ℂ)) • f v = 0)).resolve_left
        (sub_ne_zero.mpr hcoeff))
  ext v
  exact hzero v

/-- Irreducibility of induction from the inertia subgroup of a scalar normal
subgroup character. -/
theorem simple_ind_of_scalar {G : Type} [Group G] [Finite G]
    (N I : Subgroup G) [N.Normal] (hNI : N ≤ I)
    (lam : N →* ℂˣ) (V : FDRep ℂ I) [Simple V]
    (hscalar : ∀ (n : N) v, V.ρ (Subgroup.inclusion hNI n) v = (lam n : ℂ) • v)
    (hinertia : linearCharacterInertia N lam = I) :
    Simple (TauCeti.indFDRep V) := by
  apply (TauCeti.simple_indFDRep_iff V).mpr
  refine ⟨inferInstance, fun s hs => ?_⟩
  have hs' : s⁻¹ ∉ linearCharacterInertia N lam := by
    rw [hinertia]
    simpa only [Subgroup.inv_mem_iff] using hs
  change ¬ ∀ n, lam (MulAut.conjNormal s⁻¹ n) = lam n at hs'
  push Not at hs'
  obtain ⟨n, hn⟩ := hs'
  exact mackeyDisjoint_of_scalar N I hNI lam V hscalar s n (Ne.symm hn)

end Kourovka.P21_68
