import Kourovka2135.MinimalIrreducibleCharacter
import Kourovka2135.IrreducibleCharacterEquiv
import Kourovka2135.RepresentationGroupEquiv
import Kourovka2135.DeterminantOneIntertwinerGroup

/-! Actual equivalences implementing ambient conjugation on a nonlinear
irreducible representation of the minimal binary kernel. The determinant
is then an actual conjugation-invariant character, and the equation
[N,G]=N forces it to be trivial.

Character invariance, composed irreducibility, and determinant invariance
are proved. None is an extra premise. For perfect ambient groups the
moving-kernel equation is also derived from minimality and nonabelianity.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.MinimalCharacterEquivalence

open scoped IsMulCommutative

section InvariantHom

/-- A homomorphism fixed by ambient conjugation kills every actual
commutator generator, so [N,G]=N forces it to be the trivial homomorphism.
The target need not even be commutative. -/
theorem conjugationInvariantHom_eq_one_of_moving
    {G A : Type*} [Group G] [Group A] (N : Subgroup G) [N.Normal]
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N) (χ : N →* A)
    (hχ : ∀ (g : G) (n : N), χ (MulAut.conjNormal g n) = χ n) : χ = 1 := by
  have hkill : ⁅N, (⊤ : Subgroup G)⁆ ≤ χ.ker.map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    let n : N := ⟨a, ha⟩
    refine ⟨n * MulAut.conjNormal g n⁻¹, ?_, ?_⟩
    · change χ (n * MulAut.conjNormal g n⁻¹) = 1
      rw [map_mul, hχ, map_inv, mul_inv_cancel]
    · change a * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      simp only [mul_assoc]
  rw [hmove] at hkill
  apply MonoidHom.ext
  intro n
  obtain ⟨m, hm, hmn⟩ := hkill n.property
  have hmn' : m = n := Subtype.ext hmn
  subst m
  exact hm

end InvariantHom

variable {k G V : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable [Group G] [Finite G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (ρ : Representation k N V) [ρ.IsIrreducible]
variable (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1)

include hN hmin hnonabelian hderived

/-- The actual original representation is equivalent to its actual
ambient conjugate. Irreducibility of the conjugate is derived by pullback. -/
theorem nonempty_equiv_conjNormal (g : G) :
    Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom)) := by
  let σ : Representation k N V := ρ.comp (MulAut.conjNormal g).toMonoidHom
  let : σ.IsIrreducible :=
    RepresentationGroupEquiv.isIrreducible_comp ρ (MulAut.conjNormal g)
  have hc : ¬ ringChar k ∣ Nat.card N := by
    simpa only [ringChar.eq_zero, zero_dvd_iff] using (Nat.card_pos (α := N)).ne'
  have hchar : σ.character = ρ.character :=
    MinimalIrreducibleCharacter.character_comp_conjNormal_of_twoGroup
      N hN hmin ρ hderived hnonabelian g
  exact IrreducibleCharacterEquiv.equiv_of_irreducible_char_eq (ρ := σ) (σ := ρ) hc hchar

/-- Determinant invariance follows from the actual conjugation intertwiner. -/
theorem coefficientAut_det_conjNormal (g : G) (n : N) :
    LinearEquiv.det (DeterminantOneIntertwinerGroup.coefficientAut ρ
      (MulAut.conjNormal g n)) =
      LinearEquiv.det (DeterminantOneIntertwinerGroup.coefficientAut ρ n) := by
  obtain ⟨T⟩ := nonempty_equiv_conjNormal N hN hmin hnonabelian ρ hderived g
  have hT : DeterminantOneIntertwinerGroup.Intertwines N ρ g T.toLinearEquiv := by
    intro x
    exact T.isIntertwining' x
  have h := congrArg LinearEquiv.det
    ((DeterminantOneIntertwinerGroup.intertwines_iff_aut N ρ g T.toLinearEquiv).mp hT n)
  rw [map_mul, map_mul] at h
  exact (mul_left_cancel (h.trans (mul_comm _ _))).symm

/-- The actual unit-valued determinant character is trivial on a moving kernel. -/
theorem coefficientAut_det_eq_one
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N) (n : N) :
    LinearEquiv.det (DeterminantOneIntertwinerGroup.coefficientAut ρ n) = 1 := by
  let χ : N →* kˣ := LinearEquiv.det.comp
    (DeterminantOneIntertwinerGroup.coefficientAut ρ)
  have hχ : χ = 1 := conjugationInvariantHom_eq_one_of_moving N hmove χ
    (coefficientAut_det_conjNormal N hN hmin hnonabelian ρ hderived)
  exact congrArg (fun f : N →* kˣ => f n) hχ

/-- The original linear-map determinant, with no change of coefficient space. -/
theorem det_eq_one (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N) (n : N) :
    LinearMap.det (ρ n) = 1 :=
  (DeterminantOneIntertwinerGroup.coefficientAut_det_eq_one_iff ρ n).mp
    (coefficientAut_det_eq_one N hN hmin hnonabelian ρ hderived hmove n)

/-- In the intended perfect ambient group the moving-kernel equation
is derived, so the actual coefficient graph has determinant one. -/
theorem coefficientAut_det_eq_one_of_perfect [Group.IsPerfect G] (n : N) :
    LinearEquiv.det (DeterminantOneIntertwinerGroup.coefficientAut ρ n) = 1 := by
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  exact coefficientAut_det_eq_one N hN hmin hnonabelian ρ hderived
    (commutator_eq_self_of_minimal_noncentral N hnc hmin) n

/-- Determinant one for every actual kernel operator in the perfect case. -/
theorem det_eq_one_of_perfect [Group.IsPerfect G] (n : N) :
    LinearMap.det (ρ n) = 1 :=
  (DeterminantOneIntertwinerGroup.coefficientAut_det_eq_one_iff ρ n).mp
    (coefficientAut_det_eq_one_of_perfect N hN hmin hnonabelian ρ hderived n)

end Kourovka2135.MinimalCharacterEquivalence
