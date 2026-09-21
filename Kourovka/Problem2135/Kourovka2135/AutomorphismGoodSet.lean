import Kourovka2135.GeneratingGoodSetPerfect
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A generating pair and one automorphism-conjugate commutator certify
a generating good set. This also allows outer automorphisms of the actual
group, as needed for the three order-seven classes in the Suzuki cover.
-/

set_option autoImplicit false
namespace Kourovka2135

variable {G : Type*} [Group G]

def automorphismOrbit (x : G) : Set G := Set.range (fun a : MulAut G => a x)

theorem mem_automorphismOrbit (x : G) : x ∈ automorphismOrbit x :=
  ⟨MulEquiv.refl G, rfl⟩

theorem orderOf_mem_automorphismOrbit (x : G) {y : G}
    (hy : y ∈ automorphismOrbit x) : orderOf y = orderOf x := by
  obtain ⟨a, rfl⟩ := hy
  exact a.orderOf_eq x

theorem isGeneratingGoodSet_automorphismOrbit (x : G) (s t : MulAut G)
    (hcomm : paperCommutator x (s x) = t x)
    (hgen : Subgroup.closure ({x, s x} : Set G) = ⊤) :
    IsGeneratingGoodSet (automorphismOrbit x) := by
  rintro y ⟨a, rfl⟩
  let b : MulAut G := t.symm.trans a
  refine ⟨b x, ⟨b, rfl⟩, b (s x), ⟨s.trans b, rfl⟩, ?_, ?_⟩
  · calc
      paperCommutator (b x) (b (s x)) = b (paperCommutator x (s x)) := by
        simp only [paperCommutator, map_mul, map_inv]
      _ = b (t x) := congrArg b hcomm
      _ = a x := congrArg a (t.symm_apply_apply x)
  · change Subgroup.closure ({b.toMonoidHom x, b.toMonoidHom (s x)} : Set G) = ⊤
    rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective b.toMonoidHom b.surjective

theorem isPerfect_of_automorphism_certificate (x : G) (s t : MulAut G)
    (hcomm : paperCommutator x (s x) = t x)
    (hgen : Subgroup.closure ({x, s x} : Set G) = ⊤) : Group.IsPerfect G :=
  (isGeneratingGoodSet_automorphismOrbit x s t hcomm hgen).isPerfect
    ⟨x, mem_automorphismOrbit x⟩

end Kourovka2135
