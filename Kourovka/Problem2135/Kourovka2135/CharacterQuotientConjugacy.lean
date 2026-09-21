import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.OrderOfElement

/-! Transfer an actual character formula along conjugacy in a quotient.
The quotient conjugator is lifted using the given surjection; ordinary
character conjugacy invariance and exact order preservation do the rest.
-/

set_option autoImplicit false

namespace Kourovka2135.CharacterQuotientConjugacy

theorem eq_of_isConj
    {G Q k V : Type*} [Group G] [Group Q] [Field k]
    [AddCommGroup V] [Module k V]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (ρ : Representation k G V) (c : k) (t : Q)
    (hvalue : ∀ x : G, pi x = t → Odd (orderOf x) → ρ.character x = c)
    (g : G) (hodd : Odd (orderOf g)) (hconj : IsConj (pi g) t) :
    ρ.character g = c := by
  obtain ⟨s, hs⟩ := isConj_iff.mp hconj
  obtain ⟨z, hz⟩ := hpi s
  have himage : pi (z * g * z⁻¹) = t := by
    simpa only [map_mul, map_inv, hz] using hs
  have horder : orderOf (z * g * z⁻¹) = orderOf g :=
    (MulAut.conj z).orderOf_eq g
  have hodd' : Odd (orderOf (z * g * z⁻¹)) := by rw [horder]; exact hodd
  simpa only [Representation.char_conj] using hvalue _ himage hodd'

end Kourovka2135.CharacterQuotientConjugacy
