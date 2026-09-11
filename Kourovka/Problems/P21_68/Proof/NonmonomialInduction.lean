import Kourovka.Problems.P21_68.Proof.ConjugateInertia
import Kourovka.Problems.P21_68.Proof.Obstruction.LinearInduction
import Kourovka.Problems.P21_68.Proof.Obstruction.InducedCoordinates

/-!
# Nonmonomiality of the scalar-induced representation

This packages the complete obstruction: a degree-two inducing representation
with a scalar normal-subgroup character, the correct inertia subgroup, and an
inertia quotient without index-two subgroups.
-/

namespace Kourovka.P21_68

variable {G H : Type} [Group G] [Group H] [Finite G]

/-- A degree-two representation with scalar normal-subgroup character induces
a nonmonomial representation when the inducing index is coprime to the normal
subgroup order and the inertia quotient has no index-two subgroup. -/
theorem not_isMonomial_ind_of_scalar
    (N I : Subgroup G) [N.Normal] (hNI : N ≤ I)
    (lam : N →* ℂˣ) (V : FDRep ℂ I) (hdimV : Module.finrank ℂ V = 2)
    (hscalar : ∀ n : N, ∀ v : V,
      V.ρ ((Subgroup.inclusion hNI) n) v = (lam n : ℂ) • v)
    (hinertia : linearCharacterInertia N lam = I)
    (q : I →* H) (hq : Function.Surjective q)
    (hker : q.ker ≤ N.subgroupOf I)
    (hcop : (Nat.card N).Coprime (2 * I.index))
    (hH : ∀ K : Subgroup H, K.index ≠ 2) :
    ¬ IsMonomialRepresentation (TauCeti.indFDRep V) := by
  classical
  let e := MulEquiv.subgroupCongr hinertia
  let q₀ := q.comp e.toMonoidHom
  have hq₀ : Function.Surjective q₀ := hq.comp e.surjective
  have hker₀ : q₀.ker ≤ N.subgroupOf (linearCharacterInertia N lam) := by
    intro x hx
    exact hker hx
  choose q' hq' hker' using fun g =>
    exists_conjugate_inertia_projection N lam q₀ hq₀ hker₀ g
  apply not_isMonomialRepresentation_of_weights N (TauCeti.indFDRep V)
    (inducedCoordinate V) (inducedCoordinate_detects_zero V)
    (fun g => lam.comp (MulAut.conjNormal g).toMonoidHom)
    (fun n g v => inducedCoordinate_scalar N hNI V lam hscalar n g v)
    I.index Subgroup.index_ne_zero_of_finite
    (by rw [TauCeti.finrank_indFDRep, hdimV, Nat.mul_comm]) hcop
    (fun g => (weightInertia_index N lam g).trans (congrArg Subgroup.index hinertia))
    q' hq' hker' hH

end Kourovka.P21_68
