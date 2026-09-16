import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Ordinary spread

The definitions use ordinary subgroup generation. In particular, they do not
mean normal generation, topological generation, or generation in an ambient group.

Donoven and Harper, *Infinite 3/2-generated groups*, Question 2 (2020), ask for
an infinite group of spread one. The unrestricted existence question is also
Kourovka Notebook Problem 21.38.
-/

namespace Kourovka.P21_38

variable {G : Type*} [Group G]

/-- The two elements generate the whole group as an ordinary subgroup. -/
def GeneratesPair (a b : G) : Prop :=
  Subgroup.closure ({a, b} : Set G) = ⊤

/-- Every `k` nonidentity elements have a common generating companion. -/
def HasSpreadAtLeast (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∀ x : Fin k → G, (∀ i, x i ≠ 1) → ∃ y : G, ∀ i, GeneratesPair (x i) y

/-- Ordinary spread is exactly one: the properties for one and two elements differ. -/
def HasSpreadExactlyOne (G : Type*) [Group G] : Prop :=
  HasSpreadAtLeast G 1 ∧ ¬ HasSpreadAtLeast G 2

@[simp]
theorem hasSpreadAtLeast_zero : HasSpreadAtLeast G 0 := by
  intro x _
  exact ⟨1, fun i => Fin.elim0 i⟩

theorem hasSpreadAtLeast_one_iff :
    HasSpreadAtLeast G 1 ↔ ∀ x : G, x ≠ 1 → ∃ y : G, GeneratesPair x y := by
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := h (fun _ => x) (fun _ => hx)
    exact ⟨y, hy 0⟩
  · intro h x hx
    obtain ⟨y, hy⟩ := h (x 0) (hx 0)
    refine ⟨y, ?_⟩
    intro i
    fin_cases i
    exact hy

theorem hasSpreadAtLeast_two_iff :
    HasSpreadAtLeast G 2 ↔
      ∀ a b : G, a ≠ 1 → b ≠ 1 →
        ∃ y : G, GeneratesPair a y ∧ GeneratesPair b y := by
  constructor
  · intro h a b ha hb
    let x : Fin 2 → G := fun i => if i = 0 then a else b
    have hx : ∀ i, x i ≠ 1 := by
      intro i
      dsimp [x]
      split <;> assumption
    obtain ⟨y, hy⟩ := h x hx
    refine ⟨y, ?_, ?_⟩
    · simpa [x] using hy 0
    · simpa [x] using hy 1
  · intro h x hx
    obtain ⟨y, ha, hb⟩ := h (x 0) (x 1) (hx 0) (hx 1)
    refine ⟨y, ?_⟩
    intro i
    fin_cases i
    · exact ha
    · exact hb

/-- Exact spread one, stated without tuple notation. -/
theorem hasSpreadExactlyOne_iff :
    HasSpreadExactlyOne G ↔
      (∀ x : G, x ≠ 1 → ∃ y : G, GeneratesPair x y) ∧
      ∃ a b : G, a ≠ 1 ∧ b ≠ 1 ∧
        ∀ y : G, ¬ (GeneratesPair a y ∧ GeneratesPair b y) := by
  classical
  simp only [HasSpreadExactlyOne, hasSpreadAtLeast_one_iff,
    hasSpreadAtLeast_two_iff]
  push Not
  rfl

end Kourovka.P21_38
