import Kourovka.Problems.P21_40.Statement
import Mathlib.Data.Fintype.Card

/-!
# Finite orbit sets and roots

An injective equivariant self-map of a type with finitely many group-action
orbits is surjective. Applied to a power map and the action of the full
automorphism group, this supplies a coherent sequence of roots.
-/

namespace Kourovka.P21_40

/-- An injective equivariant self-map is surjective when the action has finitely many orbits. -/
theorem surjective_of_injective_equivariant
    {H X : Type*} [Group H] [MulAction H X]
    [Finite (MulAction.orbitRel.Quotient H X)]
    (f : X → X) (hf : Function.Injective f)
    (hequiv : ∀ (h : H) (x : X), f (h • x) = h • f x) : Function.Surjective f := by
  let F : MulAction.orbitRel.Quotient H X → MulAction.orbitRel.Quotient H X :=
    Quotient.map f (by
      rintro a b ⟨h, hh⟩
      exact ⟨h, (hequiv h b).symm.trans (congrArg f hh)⟩)
  have hF : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        apply Quotient.sound
        obtain ⟨h, hh⟩ := Quotient.exact hab
        exact ⟨h, hf ((hequiv h b).trans hh)⟩
  have hsurj := Finite.surjective_of_injective hF
  intro b
  obtain ⟨a, ha⟩ := hsurj (Quotient.mk _ b)
  induction a using Quotient.inductionOn with
  | _ a =>
    obtain ⟨h, hh⟩ := Quotient.exact ha
    change h • b = f a at hh
    refine ⟨h⁻¹ • a, ?_⟩
    rw [hequiv, ← hh, inv_smul_smul]

/-- Finite automorphism-orbit count turns uniqueness of roots into existence of roots. -/
theorem surjective_pow_of_injective {H : Type*} [Group H]
    (hH : HasFiniteAutomorphismOrbits H) {p : ℕ}
    (hp : Function.Injective (fun h : H => h ^ p)) :
    Function.Surjective (fun h : H => h ^ p) := by
  let : Finite (MulAction.orbitRel.Quotient (MulAut H) H) := hH
  exact surjective_of_injective_equivariant (H := MulAut H) (fun h : H => h ^ p) hp
    (fun α h => (map_pow α h p).symm)

/-- Surjectivity of a power map supplies a coherent root sequence starting at any element. -/
theorem exists_root_chain {H : Type*} [Group H] {p : ℕ}
    (hp : Function.Surjective (fun h : H => h ^ p)) (g : H) :
    ∃ b : ℕ → H, b 0 = g ∧ ∀ k, b (k + 1) ^ p = b k := by
  classical
  choose root hroot using hp
  refine ⟨fun k => root^[k] g, rfl, ?_⟩
  intro k
  change (root^[k + 1] g) ^ p = root^[k] g
  rw [Function.iterate_succ_apply']
  exact hroot _

/-- The later terms of a coherent root chain are roots of every earlier term. -/
theorem root_chain_pow {H : Type*} [Monoid H] {p : ℕ} {b : ℕ → H}
    (hb : ∀ k, b (k + 1) ^ p = b k) (k m : ℕ) :
    b (k + m) ^ (p ^ m) = b k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, pow_succ, Nat.mul_comm (p ^ m) p, pow_mul, hb, ih]

end Kourovka.P21_40
