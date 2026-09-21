import Kourovka2135.MinimalBinaryScalarIrreducible
import Kourovka2135.IrreducibleCentralCharacter
import Kourovka2135.IrreducibleCharacterEquiv

/-! Recognize an actual representation of the minimal nonspecial binary
kernel from its forced degree and its actual scalar action on the center.
Irreducibility and equivalence are conclusions, not hypotheses on the new
representation. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative
open IrreducibleCentralCharacter

theorem minimal_binary_equiv_of_degree_and_central_action
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    {k V W : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1)
    (σ : Representation k N W) (hdim : Module.finrank k W = 2 ^ f)
    (hcenter : ∀ z : Subgroup.center N,
      σ (z : N) = (centralCharacter ρ z : k) • (1 : Module.End k W)) :
    Nonempty (σ.Equiv ρ) := by
  let : Group.IsNilpotent N := hN.isNilpotent
  obtain ⟨d, hd⟩ := hderived
  let z : Subgroup.center N :=
    ⟨d, minimal_noncentral_commutator_le_internal_center N hmin d.property⟩
  have hc : (centralCharacter ρ z : k) ≠ 1 := by
    intro h
    exact hd ((centralCharacter_eq_one_iff ρ z).mp (Units.ext h))
  let : σ.IsIrreducible := minimal_binary_isIrreducible_of_scalar_derived_action
    N hN hmin hnonabelian R hR hRΦ hnonspecial e f hcard hf σ hdim d
    (centralCharacter ρ z : k) hc (hcenter z)
  have hcentralChar : centralCharacter σ = centralCharacter ρ := by
    apply MonoidHom.ext
    intro w
    apply Units.ext
    exact scalar_unique σ w (centralCharacter ρ w : k) (hcenter w)
  have hdσ : σ (d : N) ≠ 1 := by
    intro h
    have hz : centralCharacter σ z = 1 := (centralCharacter_eq_one_iff σ z).mpr h
    rw [hcentralChar] at hz
    exact hc (congrArg (fun u : kˣ => (u : k)) hz)
  have hdimρ : Module.finrank k V = 2 ^ f :=
    minimal_binary_nonlinear_character_degree N hN hmin hnonabelian R hR hRΦ
      hnonspecial e f hcard hf ρ ⟨d, hd⟩
  have hchar : ρ.character = σ.character := by
    funext n
    by_cases hn : n ∈ Subgroup.center N
    · change ρ.character (⟨n, hn⟩ : Subgroup.center N) =
        σ.character (⟨n, hn⟩ : Subgroup.center N)
      rw [character_center, character_center, hcentralChar, hdimρ, hdim]
    · rw [MinimalIrreducibleCharacter.character_eq_zero_of_not_mem_center_of_twoGroup
        N hN hmin ρ ⟨d, hd⟩ n hn,
        MinimalIrreducibleCharacter.character_eq_zero_of_not_mem_center_of_twoGroup
        N hN hmin σ ⟨d, hdσ⟩ n hn]
  have hcross : ¬ ringChar k ∣ Nat.card N := by
    simpa only [ringChar.eq_zero, zero_dvd_iff] using (Nat.card_pos (α := N)).ne'
  exact IrreducibleCharacterEquiv.equiv_of_irreducible_char_eq hcross hchar

end Kourovka2135
