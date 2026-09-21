import Kourovka2135.CentralExtensionEquivalence
import Kourovka2135.GroupCohomologyFieldExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

/-! Perfect central extensions with the same actual C2 kernel and quotient
are uniquely isomorphic when scalar H2 has dimension at most one. The
extension equivalence is constructed from actual cocycles, not assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.CentralBinaryExtensionUniqueness

open AbelianExtensionCocycle CentralExtensionCocycle

/-- A binary vector space of dimension at most one has at most one nonzero vector. -/
theorem eq_of_ne_zero_of_finrank_le_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V ≤ 1)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  let : Nontrivial V := ⟨⟨x, 0, hx⟩⟩
  have hdim1 : Module.finrank (ZMod 2) V = 1 :=
    Nat.le_antisymm hdim (Module.finrank_pos (R := ZMod 2) (M := V))
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim1 y
  have ha01 : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha01 with h | h
  · exact False.elim (hy (by simpa only [h, zero_smul] using ha.symm))
  · simpa only [h, one_smul] using ha

/-- The actual class of a perfect central C2 extension is nonzero. -/
theorem characterClass_ne_zero
    {G Q : Type} [Group G] [Group Q] [Group.IsPerfect G]
    (S : GroupExtension (Multiplicative (ZMod 2)) G Q)
    (hc : S.inl.range ≤ Subgroup.center G) :
    characterClass (k := ZMod 2) S hc (AddMonoidHom.id (ZMod 2)) ≠ 0 := by
  intro hz
  obtain ⟨d, hd⟩ := exists_hom_of_characterClass_eq_zero
    (k := ZMod 2) S hc (AddMonoidHom.id (ZMod 2)) hz
  have h := hom_eq_one_of_perfect d (embed S (1 : ZMod 2))
  rw [hd] at h
  exact one_ne_zero (show (1 : ZMod 2) = 0 from h)

/-- The quotient and embedded C2 are preserved by the resulting actual isomorphism. -/
theorem exists_equiv
    {G H Q : Type} [Group G] [Group H] [Group Q] [Finite Q]
    [Group.IsPerfect G] [Group.IsPerfect H]
    (S : GroupExtension (Multiplicative (ZMod 2)) G Q)
    (T : GroupExtension (Multiplicative (ZMod 2)) H Q)
    (hS : S.inl.range ≤ Subgroup.center G) (hT : T.inl.range ≤ Subgroup.center H)
    (hH2 : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) Q (ZMod 2))) 2) ≤ 1) :
    ∃ e : G ≃* H, (∀ g, T.rightHom (e g) = S.rightHom g) ∧
      ∀ w, e (embed S w) = embed T w := by
  let : FiniteDimensional (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) Q (ZMod 2))) 2) :=
    GroupCohomologyFieldExtension.finiteDimensional_groupCohomology
      (Representation.trivial (ZMod 2) Q (ZMod 2)) 1
  apply CentralExtensionEquivalence.exists_equiv_of_characterClass_eq (k := ZMod 2) S T hS hT
  exact eq_of_ne_zero_of_finrank_le_one hH2
    (characterClass_ne_zero S hS) (characterClass_ne_zero T hT)

end Kourovka2135.CentralBinaryExtensionUniqueness
