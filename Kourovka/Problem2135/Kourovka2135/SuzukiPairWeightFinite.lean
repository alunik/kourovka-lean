import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! Three bounded certificates for the uniform Suzuki pair-weight argument.
The 12-vertex graph is independent of the field parameter; its use requires
an actual proof of the cyclic-binary-interval difference constraints. The
second certificate is precisely the finite f=5 base case, with every shift
and every nonzero twist gap checked. The third checks the two mixed
differences at f=7. None extrapolates to arbitrary field exponents or
assumes a cohomology theorem.
-/

set_option autoImplicit false
namespace Kourovka2135.SuzukiPairWeightFinite

/-- Undirected difference graph on the twelve exceptional-gap weights. -/
def adjacent (i j : Fin 12) : Prop :=
  ((![6, 173, 27, 182, 1516, 218, 1456, 890, 1744, 3456, 2896, 1536] : Fin 12 → ℕ) i).testBit j.val = true

instance (i j : Fin 12) : Decidable (adjacent i j) := inferInstanceAs
  (Decidable ((((![6, 173, 27, 182, 1516, 218, 1456, 890, 1744, 3456, 2896, 1536] : Fin 12 → ℕ) i).testBit j.val) = true))

/-- The four repeated exceptional-gap weights have multiplicity two. -/
def multiplicity (i : Fin 12) : ℕ := if i ∈ ({3, 5, 6, 8} : Finset (Fin 12)) then 2 else 1

def badQuadruples : Finset (Finset (Fin 12)) :=
  {{1, 3, 5, 7}, {3, 4, 5, 7}, {4, 5, 6, 7}, {4, 6, 7, 8}, {4, 6, 8, 10}}

set_option maxRecDepth 8192 in
/-- Every clique avoiding the five explicit non-Sidon quadruples has total
multiplicity at most five. This is one finite graph fact, valid independently
of any field parameter or embedding. -/
theorem weighted_clique_le_five :
    ∀ S : Finset (Fin 12),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → adjacent i j) →
      (∀ T ∈ badQuadruples, ¬ T ⊆ S) →
      ∑ i ∈ S, multiplicity i ≤ 5 := by
  decide +kernel

/-- The f=5 natural weight multiset, in increasing signed order modulo31. -/
def smallWeight (i : Fin 4) : ZMod 31 := ![-5, -4, 4, 5] i

def smallFrobenius : Finset (ZMod 31) := {1, 2, 4, 8, 16}

/-- All four nonzero twist gaps and all31 shifts, with pair multiplicity. -/
theorem five_exponent_pair_bound :
    ∀ (j : Fin 4) (s : ZMod 31),
      ((Finset.univ : Finset (Fin 4 × Fin 4)).filter fun p =>
        s + smallWeight p.1 + (2 : ZMod 31) ^ (j.val + 1) * smallWeight p.2 ∈
          smallFrobenius).card ≤ 5 := by
  decide +kernel

/-- The only small support-cardinality coincidence in the mixed-row
argument occurs at `m=3`. Neither of its two required differences is a
rotated natural difference. This checks seven rotations and sixteen
ordered differences, not an unbounded field-parameter range. -/
def eightWeight (i : Fin 4) : ZMod 127 := ![-9, -8, 8, 9] i

theorem seven_exponent_no_mixed_difference :
    ∀ (j : Fin 7) (a b : Fin 4),
      (2 : ZMod 127)^j.val * (eightWeight a - eightWeight b) ≠ 14 ∧
      (2 : ZMod 127)^j.val * (eightWeight a - eightWeight b) ≠ 31 := by
  decide +kernel

end Kourovka2135.SuzukiPairWeightFinite
