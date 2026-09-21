import Kourovka2135.CentralExtensionCocycle
import Kourovka2135.NormalSubgroupExtension
import Kourovka2135.FinitePGroupCharacter
import Kourovka2135.BinarySLTwoPrimeFieldH2
import Kourovka2135.RepresentationGroupEquiv

/-! A perfect group cannot have a nontrivial central p-group kernel above a
quotient whose ordinary scalar-trivial mod-p H2 vanishes. The argument uses an
actual character of the entire kernel, so it does not assume the kernel is
elementary abelian or use a Schur-multiplier classification.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.CentralPGroupH2Obstruction

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]

/-- The general obstruction for the actual normal-subgroup quotient. -/
theorem eq_bot_of_H2_vanishes (p : ℕ) (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hcentral : N ≤ Subgroup.center G)
    [Subsingleton
      (groupCohomology (Rep.of (Representation.trivial (ZMod p) (G ⧸ N) (ZMod p))) 2)] :
    N = ⊥ := by
  let : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_center_iff.mp (hcentral b.property) a)⟩⟩
  by_contra hne
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  obtain ⟨χ, hχ, _⟩ := FinitePGroupCharacter.exists_nontrivial_surjective p hp N hN
  have hf : χ.toAdditiveLeft = 0 :=
    CentralExtensionCocycle.character_eq_zero_of_H2_vanishes
      (k := ZMod p) (NormalSubgroupExtension.extension N)
      (by simpa only [NormalSubgroupExtension.extension_inl_range] using hcentral)
      χ.toAdditiveLeft
  apply hχ
  ext n
  exact congrArg (fun l : Additive N →+ ZMod p => l (Additive.ofMul n)) hf

/-- There is no nontrivial perfect central 2-cover of SL2(2^f) for f≥3,
proved from the actual ordinary H2 calculation. -/
theorem binary_eq_bot (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hcentral : N ≤ Subgroup.center G)
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : SLTwo.SL2 F ≃* G ⧸ N) : N = ⊥ := by
  let ρ : Representation (ZMod 2) (G ⧸ N) (ZMod 2) :=
    Representation.trivial (ZMod 2) (G ⧸ N) (ZMod 2)
  let : Subsingleton
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2))) 2) :=
    BinarySLTwoPrimeFieldH2.subsingleton_H2 F f hcard hf
  have hpull : ρ.comp e.toMonoidHom =
      Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2) := by
    ext g
    rfl
  let : Subsingleton (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 2) := by
    rw [hpull]
    infer_instance
  let : Subsingleton (groupCohomology (Rep.of ρ) 2) :=
    (RepresentationGroupEquiv.cohomologyIso ρ e 2).toLinearEquiv.symm.injective.subsingleton
  exact eq_bot_of_H2_vanishes 2 Nat.prime_two N hN hcentral

end Kourovka2135.CentralPGroupH2Obstruction
