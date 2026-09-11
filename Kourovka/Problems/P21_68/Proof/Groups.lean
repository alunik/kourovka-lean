import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# Explicit groups of orders 24 and 96

The quaternion group is extended by its order-three automorphism to form `H`.
It embeds in the even signed permutations `W = E ⋊ (V4 ⋊ C3)`. Both layers of
the latter extension have abelian kernels. The finite identities are checked
by Lean's kernel; the no-index-two proof uses the displayed generator relations.

This realizes the complement/subgroup pair described by Kida, *On semiabelian
groups* (2025), p. 710, without using a small-group catalogue identification.
-/

namespace Kourovka.P21_68

abbrev Q := QuaternionGroup 2
abbrev C3 := Multiplicative (ZMod 3)

/-- The automorphism cycling the three quaternion units. -/
def qCycleFun : Q → Q
  | .a n => if n = 0 then .a 0 else if n = 1 then .xa 0
      else if n = 2 then .a 2 else .xa 2
  | .xa n => if n = 0 then .xa 3 else if n = 1 then .a 3
      else if n = 2 then .xa 1 else .a 1

def qCycle : MulAut Q where
  toFun := qCycleFun
  invFun := qCycleFun ∘ qCycleFun
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

theorem qCycle_cube : qCycle ^ 3 = 1 := by
  ext x
  revert x
  decide +kernel

def qAction : C3 →* MulAut Q where
  toFun c := qCycle ^ c.toAdd.val
  map_one' := by ext x; rfl
  map_mul' := by
    intro a b
    ext x
    revert a b x
    decide +kernel

abbrev H := Q ⋊[qAction] C3

instance : Fintype H := Fintype.ofEquiv (Q × C3)
  { toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => (x.left, x.right)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def qI : H := SemidirectProduct.inl (QuaternionGroup.a 1)
def qJ : H := SemidirectProduct.inl (QuaternionGroup.xa 0)
def sigma : H := SemidirectProduct.inr (Multiplicative.ofAdd 1)

theorem card_H : Fintype.card H = 24 := by decide +kernel

theorem sigma_cube : sigma ^ 3 = 1 := by decide +kernel
theorem sigma_conj_qI : sigma * qI * sigma⁻¹ = qJ := by decide +kernel
theorem sigma_conj_qJ : sigma * qJ * sigma⁻¹ = qI * qJ := by decide +kernel

/-- Every element is a short word in the three displayed generators. -/
theorem H_normal_form (h : H) :
    ∃ (a : Fin 2) (b : Fin 4) (c : Fin 3),
      h = qJ ^ a.val * qI ^ b.val * sigma ^ c.val := by
  revert h
  decide +kernel

theorem H_no_index_two (K : Subgroup H) : K.index ≠ 2 := by
  intro hk
  have hs : sigma ∈ K := by
    have hp : sigma ^ 2 * sigma ∈ K := by
      rw [← pow_succ, sigma_cube]
      exact K.one_mem
    exact (K.mul_mem_cancel_left (K.sq_mem_of_index_two hk sigma)).mp hp
  have hij : qI ∈ K ↔ qJ ∈ K := by
    rw [← sigma_conj_qI, K.mul_mem_cancel_right (K.inv_mem hs),
      K.mul_mem_cancel_left hs]
  have hjij : qJ ∈ K ↔ qI * qJ ∈ K := by
    rw [← sigma_conj_qJ, K.mul_mem_cancel_right (K.inv_mem hs),
      K.mul_mem_cancel_left hs]
  have hi : qI ∈ K := by
    by_contra hn
    have hn' := mt hij.mpr hn
    have hp : qI * qJ ∈ K := (K.mul_mem_iff_of_index_two hk).mpr (by tauto)
    exact hn' (hjij.mpr hp)
  have hj := hij.mp hi
  have ht : K = ⊤ := by
    apply top_unique
    intro h _
    obtain ⟨a, b, c, rfl⟩ := H_normal_form h
    exact K.mul_mem (K.mul_mem (K.pow_mem hj _) (K.pow_mem hi _)) (K.pow_mem hs _)
  simp [ht] at hk

abbrev V4 := Multiplicative (ZMod 2 × ZMod 2)

def vCycle : MulAut V4 where
  toFun x := Multiplicative.ofAdd (x.toAdd.2, x.toAdd.1 + x.toAdd.2)
  invFun x := Multiplicative.ofAdd (x.toAdd.1 + x.toAdd.2, x.toAdd.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def vAction : C3 →* MulAut V4 where
  toFun c := vCycle ^ c.toAdd.val
  map_one' := by apply MulEquiv.ext; intro x; rfl
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    revert a b x
    decide +kernel

/-- The middle group is constructed directly as a Klein four group by a cyclic group of order 3. -/
abbrev T := V4 ⋊[vAction] C3

instance : Fintype T := Fintype.ofEquiv (V4 × C3) SemidirectProduct.equivProd.symm

def affine : T →* Equiv.Perm V4 where
  toFun t :=
    { toFun := fun x => t.left * vAction t.right x
      invFun := fun x => (vAction t.right).symm (t.left⁻¹ * x)
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  map_one' := by apply Equiv.ext; intro x; simp
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro x
    simp [mul_assoc]

def signSum : (V4 → ZMod 2) →+ ZMod 2 where
  toFun f := ∑ x, f x
  map_zero' := by simp
  map_add' := by intro f g; simp [Finset.sum_add_distrib]

/-- The even sign vectors on four points. -/
abbrev E := Multiplicative signSum.ker

instance : Fintype E := inferInstanceAs (Fintype signSum.ker)

def eReindex (t : T) (e : E) : E :=
  Multiplicative.ofAdd ⟨fun x => e.toAdd.val ((affine t).symm x), by
    change (∑ x, e.toAdd.val ((affine t).symm x)) = 0
    rw [(affine t).symm.sum_comp]
    exact e.toAdd.property⟩

def eAction : T →* MulAut E where
  toFun t :=
    { toFun := eReindex t
      invFun := eReindex t⁻¹
      left_inv := by
        intro e
        apply Subtype.ext
        funext x
        change e.toAdd.val ((affine t)⁻¹ ((affine t⁻¹)⁻¹ x)) = e.toAdd.val x
        simp
      right_inv := by
        intro e
        apply Subtype.ext
        funext x
        change e.toAdd.val ((affine t⁻¹)⁻¹ ((affine t)⁻¹ x)) = e.toAdd.val x
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        funext x
        rfl }
  map_one' := by
    ext e x
    change e.toAdd.val ((affine 1)⁻¹ x) = e.toAdd.val x
    simp
  map_mul' := by
    intro a b
    ext e x
    change e.toAdd.val ((affine (a * b))⁻¹ x) =
      e.toAdd.val ((affine b)⁻¹ ((affine a)⁻¹ x))
    simp

/-- The semiabelian complement of order 96. -/
abbrev W := E ⋊[eAction] T

instance : Fintype W := Fintype.ofEquiv (E × T) SemidirectProduct.equivProd.symm

theorem card_V4 : Fintype.card V4 = 4 := by decide +kernel
theorem card_T : Fintype.card T = 12 := by decide +kernel
theorem card_E : Fintype.card E = 8 := by decide +kernel
theorem card_W : Fintype.card W = 96 := by
  rw [Fintype.card_congr SemidirectProduct.equivProd, Fintype.card_prod, card_E, card_T]

/-- Quaternion units modulo their central sign. -/
def qQuot : Q →* V4 where
  toFun
    | .a n => Multiplicative.ofAdd (if n = 0 ∨ n = 2 then 0 else 1, 0)
    | .xa n => Multiplicative.ofAdd (if n = 0 ∨ n = 2 then 0 else 1, 1)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def hProjection : H →* T := SemidirectProduct.map qQuot (MonoidHom.id C3) (by
  intro c
  apply MonoidHom.ext
  intro q
  revert c q
  decide +kernel)

/-- The positively signed quaternion basis, indexed by its image in the Klein four group. -/
def qBasis (v : V4) : Q :=
  if v.toAdd.1 = 0 then
    if v.toAdd.2 = 0 then .a 0 else .xa 0
  else if v.toAdd.2 = 0 then .a 1 else .xa 3

/-- The sign of a quaternion unit in the displayed basis. -/
def qSign : Q → ZMod 2
  | .a n => if n = 0 ∨ n = 1 then 0 else 1
  | .xa n => if n = 0 ∨ n = 3 then 0 else 1

def qSigns (q : Q) : E := Multiplicative.ofAdd
  ⟨fun v => qSign (q * qBasis ((qQuot q)⁻¹ * v)), by
    change (∑ v, qSign (q * qBasis ((qQuot q)⁻¹ * v))) = 0
    revert q
    decide +kernel⟩

/-- The faithful signed permutation embedding of the binary tetrahedral group. -/
def hEmbed : H →* W where
  toFun h := ⟨qSigns h.left, hProjection h⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      funext x
      revert x
      decide +kernel
    · exact hProjection.map_one
  map_mul' := by
    intro a b
    apply SemidirectProduct.ext
    · apply Subtype.ext
      funext x
      revert a b x
      decide +kernel
    · exact hProjection.map_mul a b

theorem hEmbed_injective : Function.Injective hEmbed := by
  intro a b hab
  have hr : hProjection a = hProjection b := congrArg SemidirectProduct.right hab
  have he : (qSigns a.left).toAdd.val 1 = (qSigns b.left).toAdd.val 1 :=
    congrArg (fun w : W => w.left.toAdd.val 1) hab
  have hc : ∀ a b : H,
      hProjection a = hProjection b →
      (qSigns a.left).toAdd.val 1 = (qSigns b.left).toAdd.val 1 → a = b := by
    decide +kernel
  exact hc a b hr he

def Hsub : Subgroup W := hEmbed.range

noncomputable def hEquivHsub : H ≃* Hsub :=
  MulEquiv.ofBijective hEmbed.rangeRestrict
    ⟨fun _ _ h => hEmbed_injective (congrArg Subtype.val h), hEmbed.rangeRestrict_surjective⟩

theorem card_Hsub : Nat.card Hsub = 24 := by
  rw [← Nat.card_congr hEquivHsub.toEquiv, Nat.card_eq_fintype_card, card_H]

theorem Hsub_index : Hsub.index = 4 := by
  have h := Hsub.card_mul_index
  rw [card_Hsub, Nat.card_eq_fintype_card, card_W] at h
  omega

theorem Hsub_no_index_two (K : Subgroup Hsub) : K.index ≠ 2 := by
  have hi := K.index_comap_of_surjective hEquivHsub.surjective
  exact hi ▸ H_no_index_two (K.comap hEquivHsub.toMonoidHom)


end Kourovka.P21_68
