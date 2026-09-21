import Kourovka2135.BinaryTensorSLTwoWeyl
import Kourovka2135.GroupCohomologyScalarRestriction
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.ZMod

/-! The genuine natural binary module, and its injections into singleton twists.

The natural module is the actual action of SL2(F) on F², restricted to F2.
Its simplicity follows from upper-root differences and the genuine Weyl
matrix, even when F is infinite. The maps into singleton tensor modules
are the actual coordinatewise field/Frobenius maps, followed by the actual
singleton tensor equivalence. No classification or uniqueness is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryNaturalPrimeField

open scoped TensorProduct PiTensorProduct CharTwo

variable (F : Type) [Field F] [CharP F 2]

local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The native natural module, with its actual action restricted to the prime field. -/
def representation : Representation (ZMod 2) (SLTwo.SL2 F) (Fin 2 → F) :=
  GroupCohomologyScalarRestriction.restrict (ZMod 2)
    (BinaryTensorSLTwo.naturalTwist F (RingHom.id F) 0)

/-- The native action is the ordinary matrix-vector product. -/
theorem representation_apply (g : SLTwo.SL2 F) (x : Fin 2 → F) (j : Fin 2) :
    representation F g x j = ∑ l : Fin 2, g.val j l * x l := by
  simpa only [representation, GroupCohomologyScalarRestriction.restrict_apply,
    RingHom.id_apply, pow_zero, pow_one] using
    BinaryTensorSLTwo.naturalTwist_apply F (RingHom.id F) 0 g x j

/-- Actual upper-root action on native coordinates. -/
theorem representation_uni (t : F) (x : Fin 2 → F) :
    representation F (SLTwo.uni t) x = ![x 0 + t * x 1, x 1] := by
  simpa only [representation, GroupCohomologyScalarRestriction.restrict_apply,
    RingHom.id_apply, pow_zero, pow_one] using
    BinaryTensorSLTwo.naturalTwist_uni F (RingHom.id F) 0 t x

/-- In characteristic two the actual Weyl matrix exchanges the coordinates. -/
theorem representation_weyl (x : Fin 2 → F) :
    representation F (SLTwo.weyl F) x = ![x 1, x 0] :=
  BinaryTensorSLTwo.naturalTwist_weyl F (RingHom.id F) 0 x

/-- Every nonzero binary subspace stable under the actual SL2 action is the whole space. -/
theorem eq_top_of_stable (W : Submodule (ZMod 2) (Fin 2 → F))
    (hne : ∃ x ∈ W, x ≠ 0)
    (hstable : ∀ (g : SLTwo.SL2 F) (x : Fin 2 → F),
      x ∈ W → representation F g x ∈ W) : W = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := hne
  have hv : ∃ v ∈ W, v 1 ≠ 0 := by
    by_cases hx1 : x 1 = 0
    · have hxfirst : x 0 ≠ 0 := by
        intro h
        apply hx0
        funext j
        fin_cases j <;> simp [h, hx1]
      refine ⟨representation F (SLTwo.weyl F) x,
        hstable (SLTwo.weyl F) x hx, ?_⟩
      simpa only [representation_weyl, Matrix.cons_val_one, Matrix.cons_val_zero] using hxfirst
    · exact ⟨x, hx, hx1⟩
  obtain ⟨v, hv, hv1⟩ := hv
  have hfirst (s : F) : ![s, 0] ∈ W := by
    have h := W.sub_mem (hstable (SLTwo.uni (s / v 1)) v hv) hv
    have heq : representation F (SLTwo.uni (s / v 1)) v - v = ![s, 0] := by
      rw [representation_uni]
      funext j
      fin_cases j
      · change v 0 + (s / v 1) * v 1 - v 0 = s
        rw [div_mul_cancel₀ _ hv1, add_sub_cancel_left]
      · exact sub_self (v 1)
    rwa [heq] at h
  have hsecond (s : F) : ![0, s] ∈ W := by
    have h := hstable (SLTwo.weyl F) _ (hfirst s)
    simpa only [representation_weyl, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  apply le_antisymm le_top
  intro y _
  have h := W.add_mem (hfirst (y 0)) (hsecond (y 1))
  have heq : ![y 0, 0] + ![0, y 1] = y := by
    funext j
    fin_cases j <;> simp
  rwa [heq] at h

/-- The genuine native natural module is irreducible over F2, without a finiteness assumption. -/
theorem isIrreducible : (representation F).IsIrreducible := by
  let ρ := representation F
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have he : (![1, 0] : Fin 2 → F) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [h]
      trivial
    have he0 : (![1, 0] : Fin 2 → F) = 0 := he
    have hz := congrFun he0 0
    exact one_ne_zero hz
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hex : ∃ v ∈ W.toSubmodule, v ≠ 0 := by
    by_contra h
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    by_contra hne
    exact h ⟨v, hv, hne⟩
  apply Subrepresentation.toSubmodule_injective
  exact eq_top_of_stable F W.toSubmodule hex (fun g _ hv => W.apply_mem_toSubmodule g hv)

section Embedding

variable (k : Type) [Field k] [CharP k 2] (σ : F →+* k)

local instance coefficientPrimeAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- Coordinatewise field embedding followed by the actual binary Frobenius iterate. -/
def twistAdditive (n : ℕ) : (Fin 2 → F) →+ (Fin 2 → k) where
  toFun x j := BinaryTensorSLTwo.twistEmbedding k σ n (x j)
  map_zero' := by funext j; exact map_zero _
  map_add' x y := by funext j; exact map_add _ _ _

/-- Any additive map of these binary vector spaces is canonically F2-linear. -/
def twistLinear (n : ℕ) : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → k) :=
  (twistAdditive F k σ n).toZModLinearMap 2

@[simp] theorem twistLinear_apply (n : ℕ) (x : Fin 2 → F) (j : Fin 2) :
    twistLinear F k σ n x j = (σ (x j)) ^ (2 ^ n) := rfl

/-- The actual coordinatewise twist is injective. -/
theorem twistLinear_injective (n : ℕ) : Function.Injective (twistLinear F k σ n) := by
  intro x y h
  funext j
  exact (BinaryTensorSLTwo.twistEmbedding k σ n).injective (congrFun h j)

/-- The concrete coordinatewise twist intertwines every actual SL2 matrix. -/
theorem twistLinear_action (n : ℕ) (g : SLTwo.SL2 F) (x : Fin 2 → F) :
    twistLinear F k σ n (representation F g x) =
      BinaryTensorSLTwo.naturalTwist k σ n g (twistLinear F k σ n x) := by
  funext j
  rw [BinaryTensorSLTwo.naturalTwist_apply]
  change BinaryTensorSLTwo.twistEmbedding k σ n (representation F g x j) = _
  rw [representation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul]
  rfl

/-- The actual F2-intertwiner into an individual Frobenius-twisted natural module. -/
def twistIntertwiner (n : ℕ) : Representation.IntertwiningMap (representation F)
    (GroupCohomologyScalarRestriction.restrict (ZMod 2)
      (BinaryTensorSLTwo.naturalTwist k σ n)) where
  toLinearMap := twistLinear F k σ n
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact twistLinear_action F k σ n g x

/-- Injectivity of the bundled native-to-twist intertwiner. -/
theorem twistIntertwiner_injective (n : ℕ) :
    Function.Injective (twistIntertwiner F k σ n) := twistLinear_injective F k σ n

variable {f : ℕ} (i : Fin f)

/-- The actual single-factor tensor equivalence, followed by the existing coefficient equivalence. -/
def singletonEquiv : (Fin 2 → k) ≃ₗ[k] BinaryTensorCoefficient.Carrier k {i} :=
  (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : ({i} : Finset (Fin f)) =>
    Fin 2 → k) ⟨i, Finset.mem_singleton_self i⟩).symm.trans
      (BinaryTensorSLTwo.tensorEquiv k {i})

omit [CharP k 2] in
/-- The single-factor equivalence sends a vector to its genuine pure tensor. -/
theorem singletonEquiv_apply (x : Fin 2 → k) :
    singletonEquiv k i x = BinaryTensorSLTwo.tensorEquiv k {i}
      (PiTensorProduct.tprod k (fun _ : ({i} : Finset (Fin f)) => x)) := by
  simp only [singletonEquiv, LinearEquiv.trans_apply,
    PiTensorProduct.subsingletonEquiv_symm_apply']

omit [CharP F 2] in
/-- This actual single-factor equivalence intertwines the full matrix group action. -/
theorem singletonEquiv_action (g : SLTwo.SL2 F) (x : Fin 2 → k) :
    BinaryTensorSLTwo.representation k σ {i} g (singletonEquiv k i x) =
      singletonEquiv k i (BinaryTensorSLTwo.naturalTwist k σ i.val g x) := by
  rw [singletonEquiv_apply, BinaryTensorSLTwo.representation_tensorEquiv,
    BinaryTensorSLTwo.tensorRepresentation_tprod, singletonEquiv_apply]
  apply congrArg (BinaryTensorSLTwo.tensorEquiv k {i})
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  have hj : j.val = i := Finset.mem_singleton.mp j.property
  simp only [hj]

set_option maxRecDepth 2048 in
omit [CharP F 2] in
/-- The actual single-factor representation equivalence, before restriction to the prime field. -/
def singletonRepresentationEquiv : Representation.Equiv
    (BinaryTensorSLTwo.naturalTwist k σ i.val)
    (BinaryTensorSLTwo.representation k σ {i}) where
  toLinearEquiv := singletonEquiv k i
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (singletonEquiv_action F k σ i g x).symm

set_option maxRecDepth 2048 in
/-- The native natural module embeds into the actual singleton tensor module over any extension. -/
def singletonIntertwiner : Representation.IntertwiningMap (representation F)
    (GroupCohomologyScalarRestriction.restrict (ZMod 2)
      (BinaryTensorSLTwo.representation k σ {i})) where
  toLinearMap := ((singletonEquiv k i).restrictScalars (ZMod 2)).toLinearMap.comp
    (twistLinear F k σ i.val)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change singletonEquiv k i (twistLinear F k σ i.val (representation F g x)) =
      BinaryTensorSLTwo.representation k σ {i} g
        (singletonEquiv k i (twistLinear F k σ i.val x))
    rw [twistLinear_action, singletonEquiv_action]

/-- The native-to-singleton intertwiner is an actual injection. -/
theorem singletonIntertwiner_injective :
    Function.Injective (singletonIntertwiner F k σ i) :=
  (singletonEquiv k i).injective.comp (twistLinear_injective F k σ i.val)

end Embedding

end Kourovka2135.BinaryNaturalPrimeField
