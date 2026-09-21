import Kourovka2135.MinimalSymplecticForm
import Kourovka2135.CenterSupportedCharacterDegree

/-! Characters of actual nonlinear irreducible representations of a
minimal noncentral soluble normal subgroup vanish off its center and
are invariant under ambient conjugation.

Nonlinearity is used as the concrete hypothesis that some element of the
actual derived subgroup acts nontrivially. Solvability is explicit in the
generic minimal-subgroup statements and is derived for finite 2-kernels.
No extraspecial, center-exponent, character-degree, or character-uniqueness
statement is assumed. The argument works in arbitrary characteristic when
the displayed nontrivial derived action exists.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalIrreducibleCharacter

open scoped IsMulCommutative

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- A scalar commutator with scalar different from one forces trace zero.
This elementary trace statement needs no irreducibility or centrality premise. -/
theorem character_eq_zero_of_scalar_paperCommutator
    {H : Type*} [Group H] (ρ : Representation k H V)
    (n y d : H) (α : k) (hc : paperCommutator n y = d)
    (hd : ρ d = α • (1 : Module.End k V)) (hα : α ≠ 1) :
    ρ.character n = 0 := by
  have hconj : y⁻¹ * n * y = n * d := by
    rw [← hc]
    simp only [paperCommutator, mul_assoc, mul_inv_cancel_left]
  have htrace : ρ.character (n * d) = ρ.character n := by
    rw [← hconj]
    simpa only [inv_inv] using ρ.char_conj n y⁻¹
  have hscale : ρ.character (n * d) = α * ρ.character n := by
    simp only [Representation.character, map_mul, hd, mul_smul_comm,
      mul_one, map_smul, smul_eq_mul]
  have hzero : (α - 1) * ρ.character n = 0 := by
    rw [sub_mul, one_mul, ← hscale, htrace, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hα)

variable [FiniteDimensional k V]

section Minimal

variable [IsAlgClosed k]
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (ρ : Representation k N V) [ρ.IsIrreducible]
variable (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1)

include hmin hderived in
/-- Every noncentral element moves the actual whole derived subgroup,
so its character is killed by a nontrivial derived scalar. -/
theorem character_eq_zero_of_not_mem_center (n : N) (hn : n ∉ Subgroup.center N) :
    ρ.character n = 0 := by
  obtain ⟨d, hd⟩ := hderived
  have hdc : (d : N) ∈ Subgroup.center N :=
    minimal_noncentral_commutator_le_internal_center N hmin d.property
  obtain ⟨α, hα⟩ :=
    CenterSupportedCharacterDegree.center_apply_eq_smul_id_of_irreducible ρ hdc
  have hαne : α ≠ 1 := by
    intro h
    apply hd
    rw [hα, h, one_smul]
  obtain ⟨y, hy⟩ := exists_paperCommutator_eq_of_minimal_noncentral N hmin n hn d
  exact character_eq_zero_of_scalar_paperCommutator ρ n y (d : N) α hy hα hαne

include hmin hderived in
/-- Ambient conjugation preserves this actual character: it fixes the
center pointwise, and both characters vanish outside the center. -/
theorem character_conjNormal (hnonabelian : ¬ IsMulCommutative N) (g : G) (n : N) :
    ρ.character (MulAut.conjNormal g n) = ρ.character n := by
  by_cases hn : n ∈ Subgroup.center N
  · have hc : (n : G) ∈ Subgroup.center G :=
      minimal_noncentral_center_le N hnonabelian hmin
        (Subgroup.mem_map_of_mem N.subtype hn)
    have hfix : MulAut.conjNormal g n = n := by
      apply Subtype.ext
      change g * (n : G) * g⁻¹ = (n : G)
      rw [Subgroup.mem_center_iff.mp hc g]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix]
  · have hgn : MulAut.conjNormal g n ∉ Subgroup.center N := by
      intro h
      apply hn
      apply Subgroup.mem_center_iff.mpr
      intro x
      apply (MulAut.conjNormal g).injective
      simpa only [map_mul] using Subgroup.mem_center_iff.mp h (MulAut.conjNormal g x)
    rw [character_eq_zero_of_not_mem_center N hmin ρ hderived _ hgn,
      character_eq_zero_of_not_mem_center N hmin ρ hderived n hn]

include hmin hderived in
/-- The actual transported representation has the same character. -/
theorem character_comp_conjNormal (hnonabelian : ¬ IsMulCommutative N) (g : G) :
    Representation.character (ρ.comp (MulAut.conjNormal g).toMonoidHom) = ρ.character := by
  funext n
  exact character_conjNormal N hmin ρ hderived hnonabelian g n

end Minimal

section TwoKernel

variable [IsAlgClosed k]
variable {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
variable (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (ρ : Representation k N V) [ρ.IsIrreducible]
variable (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1)

include hN hmin hderived in
/-- The finite 2-kernel version derives the required solvability. -/
theorem character_eq_zero_of_not_mem_center_of_twoGroup
    (n : N) (hn : n ∉ Subgroup.center N) : ρ.character n = 0 := by
  let : Group.IsNilpotent N := hN.isNilpotent
  exact character_eq_zero_of_not_mem_center N hmin ρ hderived n hn

include hN hmin hderived in
/-- Invariance for the actual finite minimal noncentral 2-kernel. -/
theorem character_comp_conjNormal_of_twoGroup
    (hnonabelian : ¬ IsMulCommutative N) (g : G) :
    Representation.character (ρ.comp (MulAut.conjNormal g).toMonoidHom) = ρ.character := by
  let : Group.IsNilpotent N := hN.isNilpotent
  exact character_comp_conjNormal N hmin ρ hderived hnonabelian g

end TwoKernel

end Kourovka2135.MinimalIrreducibleCharacter
