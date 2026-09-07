import Kourovka.Problems.P21_29.Proof.FiniteModel
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.BigOperators.Pi

/-! Two diagonal differences isolate one coordinate; rotations give all coordinates. -/

namespace Kourovka.P21_29

open scoped BigOperators

theorem diagonal3_smul (v : V) (x : Coord) :
    (groupElement 3 • v) x = if x = 0 ∨ x = 3 then -v x else v x := by
  have hc : ∀ x : Coord,
      (signUnit ((groupElement 3).left.1 x) : ZMod 3) =
        if x = 0 ∨ x = 3 then -1 else 1 := by decide +kernel
  rw [h_smul_apply, hc x]
  have hp : (groupElement 3).right = 1 := rfl
  rw [hp, inv_one, one_smul]
  split_ifs <;> simp

theorem diagonal1_smul (v : V) (x : Coord) :
    (groupElement 1 • v) x = if x = 0 ∨ x = 6 then -v x else v x := by
  have hc : ∀ x : Coord,
      (signUnit ((groupElement 1).left.1 x) : ZMod 3) =
        if x = 0 ∨ x = 6 then -1 else 1 := by decide +kernel
  rw [h_smul_apply, hc x]
  have hp : (groupElement 1).right = 1 := rfl
  rw [hp, inv_one, one_smul]
  split_ifs <;> simp

theorem coordinate_projection (v : V) :
    (v - groupElement 3 • v) - groupElement 1 • (v - groupElement 3 • v) =
      Pi.single 0 (v 0) := by
  have scalar_identity : ∀ (x : Coord) (t : ZMod 3),
      (t - (if x = 0 ∨ x = 3 then -t else t)) -
        (if x = 0 ∨ x = 6 then -(t - (if x = 0 ∨ x = 3 then -t else t))
         else t - (if x = 0 ∨ x = 3 then -t else t)) =
      if x = 0 then t else 0 := by decide +kernel
  funext x
  simp only [Pi.sub_apply, diagonal1_smul, diagonal3_smul, Pi.single_apply]
  rw [scalar_identity]
  split_ifs with hx
  · subst x; rfl
  · rfl

def rotation (a : Coord) : H := ⟨1, .r a⟩

theorem rotation_smul (a : Coord) (v : V) (x : Coord) :
    (rotation a • v) x = v (x - a) := by
  change (signUnit 1 : ZMod 3) * v ((DihedralGroup.r a)⁻¹ • x) = v (x - a)
  rw [signUnit_one, DihedralGroup.inv_r]
  change 1 * v (-a + x) = v (x - a)
  simp [sub_eq_add_neg, add_comm]

theorem rotation_single (a : Coord) :
    rotation a • (Pi.single 0 (1 : ZMod 3) : V) = Pi.single a 1 := by
  funext x
  rw [rotation_smul]
  simp [Pi.single_apply, sub_eq_zero]

theorem invariant_submodule (W : Submodule (ZMod 3) V)
    (stable : ∀ g : H, ∀ v ∈ W, g • v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hW
  obtain ⟨i, hi⟩ : ∃ i : Coord, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  let u := rotation (-i) • v
  have hu : u ∈ W := stable _ _ hv
  have hu0 : u 0 ≠ 0 := by
    change (rotation (-i) • v) 0 ≠ 0
    rw [rotation_smul]
    simpa using hi
  have hd : u - groupElement 3 • u ∈ W := W.sub_mem hu (stable _ _ hu)
  have hp : Pi.single 0 (u 0) ∈ W := by
    rw [← coordinate_projection]
    exact W.sub_mem hd (stable _ _ hd)
  have he : (Pi.single 0 (1 : ZMod 3) : V) ∈ W := by
    have hm := W.smul_mem (u 0)⁻¹ hp
    convert hm using 1
    funext x
    by_cases hx : x = 0 <;> simp [hx, hu0]
  have hb (a : Coord) : (Pi.single a (1 : ZMod 3) : V) ∈ W := by
    simpa only [rotation_single] using stable (rotation a) _ he
  apply top_unique
  intro w _
  rw [← Finset.univ_sum_single w]
  apply W.sum_mem
  intro a _
  have hm := W.smul_mem (w a) (hb a)
  convert hm using 1
  funext x
  by_cases hx : x = a <;> simp [hx]

theorem linear_irreducible :
    Representation.IsIrreducible
      (Representation.ofDistribMulAction (ZMod 3) H V) := by
  let ρ := Representation.ofDistribMulAction (ZMod 3) H V
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hsub := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule (ZMod 3) V) = ⊤ at hsub
    exact bot_ne_top hsub
  refine { toNontrivial := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro W
  have h := invariant_submodule W.toSubmodule
    (fun g _ hv => W.apply_mem_toSubmodule g hv)
  exact h.imp
    (fun hbot => Subrepresentation.toSubmodule_injective hbot)
    (fun htop => Subrepresentation.toSubmodule_injective htop)

end Kourovka.P21_29
