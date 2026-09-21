import Kourovka2135.CentralMaximalCover
import Kourovka2135.CentralReferenceGoodSet
import Kourovka2135.SuzukiLargeCentralKernel

/-! Actual generating good sets descend from a maximal central cover.
The large-Suzuki central base is obtained directly from its trivial-kernel
theorem. The small-Suzuki reference still has to be constructed separately.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135

theorem HasOddGeneratingGoodSetOver.image_over
    {E F Q : Type*} [Group E] [Group F] [Group Q]
    (π : E →* Q) (τ : F →* Q) (f : F →* E)
    (hf : Function.Surjective f) (hcompat : π.comp f = τ)
    {B : Set Q} (h : HasOddGeneratingGoodSetOver τ B) :
    HasOddGeneratingGoodSetOver π B := by
  obtain ⟨Y, hY, hsub, y, hy, hodd⟩ := h
  refine ⟨f '' Y, hY.image_of_surjective f hf, ?_, f y, ⟨y, hy, rfl⟩, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    change π (f z) ∈ B
    rw [show π (f z) = τ z from DFunLike.congr_fun hcompat z]
    exact hsub hz
  · exact hodd.of_dvd_nat (orderOf_map_dvd f y)

namespace CentralMaximalGoodSet
open BinaryFrattiniFullFiberInduction

theorem centralBase {Q F : Type} [Group Q] [Group F] [Finite F] [Group.IsPerfect F]
    (n : ℕ) (hbound : CentralMaximalCover.KernelBound 2 n Q)
    (τ : F →* Q) (hτ : Function.Surjective τ)
    (hcτ : τ.ker ≤ Subgroup.center F) (hpτ : IsPGroup 2 τ.ker)
    (hcard : Nat.card τ.ker = n) (B : Set Q)
    (hgood : HasOddGeneratingGoodSetOver τ B) : CentralBase Q B := by
  intro E _ _ _ π hπ hp hc
  obtain ⟨f, hf, hcompat⟩ := CentralMaximalCover.exists_surjective_over
    2 n hbound π τ hπ hτ hc hcτ hp hpτ hcard
  exact hgood.image_over π τ f hf hcompat

/-- A checked trivial central kernel supplies the central-base step. -/
theorem suzuki_large (m : ℕ) (hm : 2 ≤ m) (B : Set (SuzukiGeometry.G m))
    (hgood : HasOddGeneratingGoodSetOver (MonoidHom.id (SuzukiGeometry.G m)) B) :
    CentralBase (SuzukiGeometry.G m) B := by
  intro E _ _ _ π hπ hp hc
  have hz := SuzukiLargeCentralKernel.ker_eq_bot m hm π hπ hc hp
  let e : E ≃* SuzukiGeometry.G m := MulEquiv.ofBijective π
    ⟨(MonoidHom.ker_eq_bot_iff π).mp hz, hπ⟩
  exact hgood.of_equiv e

end CentralMaximalGoodSet
end Kourovka2135
