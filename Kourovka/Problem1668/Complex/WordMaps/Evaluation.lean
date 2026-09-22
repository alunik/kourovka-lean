import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Conj

set_option autoImplicit false

namespace WordMaps

variable {α G H : Type*} [Group G] [Group H]

/-- Word evaluation commutes with group homomorphisms. -/
theorem map_word (φ : G →* H) (g : α → G) (w : FreeGroup α) :
    φ (FreeGroup.lift g w) = FreeGroup.lift (fun i => φ (g i)) w := by
  exact FreeGroup.lift_unique (φ.comp (FreeGroup.lift g)) (by intro i; simp)

/-- Word images are closed under conjugacy. -/
theorem word_value_of_isConj (w : FreeGroup α) {a b : G} (hab : IsConj a b)
    (ha : ∃ g : α → G, FreeGroup.lift g w = a) :
    ∃ g : α → G, FreeGroup.lift g w = b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  obtain ⟨g, rfl⟩ := ha
  refine ⟨fun i => c * g i * c⁻¹, ?_⟩
  have h := map_word (MulAut.conj c).toMonoidHom g w
  exact h.symm.trans hc

/-- Conjugating a word does not change whether its word map is surjective. -/
theorem word_surjective_of_isConj {w v : FreeGroup α} (hwv : IsConj w v)
    (hv : Function.Surjective (fun g : α → G => FreeGroup.lift g v)) :
    Function.Surjective (fun g : α → G => FreeGroup.lift g w) := by
  intro b
  obtain ⟨g, hg⟩ := hv b
  exact word_value_of_isConj w (hg ▸ (FreeGroup.lift g).map_isConj hwv) ⟨g, rfl⟩

theorem power_word_surjective [DecidableEq α] (i : α) (m : ℤ)
    (hm : Function.Surjective (fun x : G => x ^ m)) :
    Function.Surjective (fun g : α → G => FreeGroup.lift g (FreeGroup.of i ^ m)) := by
  intro b
  obtain ⟨x, hx⟩ := hm b
  exact ⟨fun j => if j = i then x else 1, by simpa using hx⟩

theorem word_one (w : FreeGroup α) :
    FreeGroup.lift (fun _ : α => (1 : G)) w = 1 := by
  exact (FreeGroup.lift_unique (1 : FreeGroup α →* G) (by intro i; simp)).symm

end WordMaps
