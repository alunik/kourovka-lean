import Kourovka.Problems.P21_68.Statement
import Kourovka.Problems.P21_68.Proof.Obstruction
import Mathlib.RepresentationTheory.Induced

/-!
# Linear induction supplies a linear-character eigenvector

The proof uses Mathlib's linear Frobenius reciprocity.  This makes the eventual
nonmonomiality argument independent of a chosen model of induction.
-/

open CategoryTheory

namespace Kourovka.P21_68

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- A representation isomorphic to one induced from a linear character has a
nonzero eigenvector for that character on the inducing subgroup. -/
theorem exists_eigenvector_of_iso_indLinear (L : Subgroup G) (θ : L →* kˣ)
    (V : FDRep k G) [Nontrivial V]
    (e : V ≅ TauCeti.indFDRep (FDRep.ofLinearCharacter θ)) :
    ∃ v : V, v ≠ 0 ∧ ∀ l : L, V.ρ l v = (θ l : k) • v := by
  rw [FDRep.ofLinearCharacter_def] at e
  let A := FDRep.of (Representation.ofLinearCharacter θ)
  let F := forget₂ (FDRep k G) (Rep k G)
  let e' := (F.mapIso e).trans (TauCeti.indFDRepForgetIso A)
  have he : e'.inv ≠ 0 := by
    intro he
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h := ConcreteCategory.congr_hom e'.hom_inv_id v
    rw [he] at h
    change (0 : V) = v at h
    exact hv h.symm
  let E := Rep.indResHomEquiv L.subtype
    ((forget₂ (FDRep k L) (Rep k L)).obj A) (F.obj V)
  let f := E e'.inv
  have hf : f ≠ 0 := by
    exact fun h => he (E.injective (h.trans E.map_zero.symm))
  let fl : k →ₗ[k] V := f.hom.toLinearMap
  have hfone : fl 1 ≠ 0 := by
    intro hzero
    have hfl : fl = 0 := by
      apply LinearMap.ext
      intro x
      change fl x = 0
      calc
        fl x = fl (x • (1 : k)) := by simp only [smul_eq_mul, mul_one]
        _ = x • fl 1 := map_smul _ _ _
        _ = 0 := by rw [hzero, smul_zero]
    apply hf
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hfl
  refine ⟨fl 1, hfone, fun l => ?_⟩
  have h := Rep.hom_comm_apply f l (1 : k)
  change fl ((θ l : k) * 1) = V.ρ l (fl 1) at h
  rw [mul_one] at h
  rw [← h]
  simpa only [smul_eq_mul, mul_one] using fl.map_smul (θ l : k) (1 : k)

end Kourovka.P21_68

namespace Kourovka.P21_68

variable {G H U X : Type} [Group G] [Group H] [Finite G]
  [AddCommGroup U] [Module ℂ U]

/-- The general obstruction used by the counterexample. A normal subgroup of
coprime order forces an inducing subgroup to preserve one weight. The weight
inertia quotient then would have a subgroup of index two. -/
theorem not_isMonomialRepresentation_of_weights
    (N : Subgroup G) [N.Normal] (V : FDRep ℂ G)
    (coordinate : X → V →ₗ[ℂ] U)
    (hcoordinate : ∀ v, (∀ x, coordinate x v = 0) → v = 0)
    (weight : X → N →* ℂˣ)
    (hscalar : ∀ (n : N) x v,
      coordinate x (V.ρ n v) = (weight x n : ℂ) • coordinate x v)
    (m : ℕ) (hm : m ≠ 0) (hdim : Module.finrank ℂ V = 2 * m)
    (hcop : (Nat.card N).Coprime (2 * m))
    (hindex : ∀ x, (linearCharacterInertia N (weight x)).index = m)
    (q : ∀ x, linearCharacterInertia N (weight x) →* H)
    (hq : ∀ x, Function.Surjective (q x))
    (hker : ∀ x, (q x).ker ≤ N.subgroupOf (linearCharacterInertia N (weight x)))
    (hH : ∀ K : Subgroup H, K.index ≠ 2) :
    ¬ IsMonomialRepresentation V := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by
    rw [hdim]
    exact Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hm))
  rintro ⟨L, θ, ⟨e⟩⟩
  have hL : L.index = 2 * m := by
    have h := (FDRep.isoToLinearEquiv e).finrank_eq
    rw [hdim, TauCeti.finrank_indFDRep, FDRep.finrank_ofLinearCharacter, mul_one] at h
    exact h.symm
  have hNL : N ≤ L := le_of_coprime_card_index N L (hL ▸ hcop)
  obtain ⟨v, hv, heigen⟩ := exists_eigenvector_of_iso_indLinear L θ V e
  obtain ⟨x, hx⟩ := exists_le_weightInertia_of_eigenvector N L hNL V.ρ
    coordinate hcoordinate weight hscalar θ v hv heigen
  exact false_of_index_eq_twice (q x) (hq x)
    (fun a ha => hNL (hker x ha)) hx hm (hindex x) hL hH

end Kourovka.P21_68
