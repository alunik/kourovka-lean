import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.OrderOfElement

/-!
# Difference homomorphisms on finite abelian groups

The difference of an automorphism and the identity is a group homomorphism
when the group is abelian. Its range supplies the moving subgroup. Subgroup
closures give the generation statements needed for conditional centralization,
without introducing a vector-space structure.
-/

set_option autoImplicit false

universe u

namespace Kourovka2135.AbelianDifference

variable {V : Type u} [CommGroup V]

/-- The multiplicative difference of an automorphism and the identity. -/
def delta (a : MulAut V) : V →* V where
  toFun v := v⁻¹ * a v
  map_one' := by simp
  map_mul' v w := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

@[simp]
theorem delta_apply (a : MulAut V) (v : V) :
    delta a v = v⁻¹ * a v := rfl

/-- The subgroup moved by a single automorphism. -/
def movingSubgroup (a : MulAut V) : Subgroup V :=
  (delta a).range

@[simp]
theorem mem_movingSubgroup (a : MulAut V) (v : V) :
    v ∈ movingSubgroup a ↔ ∃ w : V, delta a w = v := Iff.rfl

theorem delta_eq_one_iff (a : MulAut V) (v : V) :
    delta a v = 1 ↔ a v = v := by
  change v⁻¹ * a v = 1 ↔ a v = v
  rw [inv_mul_eq_one, eq_comm]

/-- Commuting automorphisms commute with the difference homomorphism. -/
theorem map_delta_of_commute {a b : MulAut V} (hab : Commute a b) (v : V) :
    b (delta a v) = delta a (b v) := by
  have hba : b (a v) = a (b v) := by
    simpa only [MulAut.mul_apply] using
      congrArg (fun f : MulAut V => f v) hab.eq.symm
  simp only [delta_apply, map_mul, map_inv, hba]

/-- An automorphism commuting with a preserves its moving subgroup. -/
theorem map_movingSubgroup_eq_of_commute
    {a b : MulAut V} (hab : Commute a b) :
    (movingSubgroup a).map b.toMonoidHom = movingSubgroup a := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨v, rfl⟩
    exact ⟨b v, (map_delta_of_commute hab v).symm⟩
  · rintro y ⟨v, rfl⟩
    obtain ⟨z, rfl⟩ := b.surjective v
    exact ⟨delta a z, ⟨z, rfl⟩, map_delta_of_commute hab z⟩

/-- A finite coprime-order automorphism moves its moving subgroup onto itself. -/
theorem map_delta_movingSubgroup_eq [Finite V]
    (a : MulAut V) (n : ℕ) (ha : a ^ n = 1)
    (hcop : n.Coprime (Nat.card V)) :
    (movingSubgroup a).map (delta a) = movingSubgroup a := by
  let M := movingSubgroup a
  let f : M →* M := {
    toFun := fun m => ⟨delta a (m : V), ⟨(m : V), rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      exact map_one (delta a)
    map_mul' := by
      intro m k
      apply Subtype.ext
      exact map_mul (delta a) (m : V) (k : V) }
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro m hm
    have hdelta : delta a (m : V) = 1 := congrArg Subtype.val hm
    have hfix : a (m : V) = (m : V) := (delta_eq_one_iff a (m : V)).mp hdelta
    obtain ⟨v, hv⟩ := m.property
    have hav : a v = v * (m : V) := by
      have hh := congrArg (fun z : V => v * z) hv
      simpa only [delta_apply, mul_inv_cancel_left] using hh
    have hpow : ∀ j : ℕ, (a ^ j) v = v * (m : V) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hav, hfix]
          simp only [pow_succ', mul_assoc]
    have hmn : (m : V) ^ n = 1 := by
      have hh := hpow n
      rw [ha, MulAut.one_apply] at hh
      apply mul_left_cancel (a := v)
      simpa only [mul_one] using hh.symm
    have horder : orderOf (m : V) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_iff_pow_eq_one.mpr hmn) (orderOf_dvd_natCard (m : V))
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp horder
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  apply le_antisymm
  · rintro y ⟨v, _, rfl⟩
    exact ⟨v, rfl⟩
  · intro y hy
    obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
    exact ⟨(z : V), z.property, congrArg Subtype.val hz⟩

/-- Differences on a generating set, for the inverses of the chosen operators. -/
def differenceSet (T : Set V) (B : Set (MulAut V)) : Set V :=
  {z | ∃ b ∈ B, ∃ t ∈ T, z = delta (b⁻¹) t}

/-- Automorphisms preserving M and inducing the identity modulo U on M. -/
def modFixer (M U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {b | (∀ v : V, v ∈ M ↔ b v ∈ M) ∧
    ∀ v ∈ M, delta b v ∈ U}
  one_mem' := by
    constructor
    · intro v
      rfl
    · intro v _
      simp only [delta_apply, MulAut.one_apply, inv_mul_cancel]
      exact U.one_mem
  mul_mem' := by
    intro b c hb hc
    constructor
    · intro v
      exact (hc.1 v).trans (hb.1 (c v))
    · intro v hv
      have hprod := U.mul_mem (hc.2 v hv) (hb.2 (c v) ((hc.1 v).mp hv))
      simpa only [delta_apply, MulAut.mul_apply, mul_assoc, mul_inv_cancel_left]
        using hprod
  inv_mem' := by
    intro b hb
    constructor
    · intro v
      simpa only [MulAut.apply_inv_self] using (hb.1 (b⁻¹ v)).symm
    · intro v hv
      have hvinv : b⁻¹ v ∈ M :=
        (hb.1 (b⁻¹ v)).mpr (by simpa only [MulAut.apply_inv_self] using hv)
      have hh := U.inv_mem (hb.2 (b⁻¹ v) hvinv)
      simpa only [delta_apply, MulAut.apply_inv_self, mul_inv_rev, inv_inv] using hh

@[simp]
theorem mem_modFixer (M U : Subgroup V) (b : MulAut V) :
    b ∈ modFixer M U ↔
      (∀ v : V, v ∈ M ↔ b v ∈ M) ∧ ∀ v ∈ M, delta b v ∈ U := Iff.rfl

/-- Equality of the mapped subgroup gives both directions of invariance. -/
theorem mem_iff_apply_mem_of_map_eq
    (M : Subgroup V) (b : MulAut V) (hb : M.map b.toMonoidHom = M) (v : V) :
    v ∈ M ↔ b v ∈ M := by
  constructor
  · intro hv
    rw [← hb]
    exact ⟨v, hv, rfl⟩
  · intro hv
    have hv' : b v ∈ M.map b.toMonoidHom := by
      rw [hb]
      exact hv
    obtain ⟨w, hw, heq⟩ := hv'
    exact b.injective heq ▸ hw

/-- If the chosen operators generate an operator moving M onto itself, their
differences on any generating set of M generate M. -/
theorem closure_differenceSet_eq
    (M : Subgroup V) (T : Set V) (B : Set (MulAut V)) (a : MulAut V)
    (hT : Subgroup.closure T = M)
    (hB : ∀ b ∈ B, M.map b.toMonoidHom = M)
    (ha : a ∈ Subgroup.closure B)
    (hmove : M.map (delta a) = M) :
    Subgroup.closure (differenceSet T B) = M := by
  let U := Subgroup.closure (differenceSet T B)
  have hUM : U ≤ M := by
    apply (Subgroup.closure_le M).mpr
    rintro y ⟨b, hb, t, ht, rfl⟩
    have htM : t ∈ M := hT ▸ Subgroup.subset_closure ht
    have hstable := mem_iff_apply_mem_of_map_eq M b (hB b hb)
    have htinv : b⁻¹ t ∈ M :=
      (hstable (b⁻¹ t)).mpr (by simpa only [MulAut.apply_inv_self] using htM)
    exact M.mul_mem (M.inv_mem htM) htinv
  have hBfix : B ⊆ modFixer M U := by
    intro b hb
    have hstable := mem_iff_apply_mem_of_map_eq M b (hB b hb)
    have hinv : b⁻¹ ∈ modFixer M U := by
      constructor
      · intro v
        simpa only [MulAut.apply_inv_self] using (hstable (b⁻¹ v)).symm
      · intro v hv
        have hmap : M.map (delta (b⁻¹)) ≤ U := by
          rw [← hT, MonoidHom.map_closure]
          apply (Subgroup.closure_le U).mpr
          rintro y ⟨t, ht, rfl⟩
          exact Subgroup.subset_closure ⟨b, hb, t, ht, rfl⟩
        exact hmap ⟨v, hv, rfl⟩
    change b ∈ modFixer M U
    exact inv_inv b ▸ (modFixer M U).inv_mem hinv
  have hafix : a ∈ modFixer M U :=
    ((Subgroup.closure_le (modFixer M U)).mpr hBfix) ha
  have hmap : M.map (delta a) ≤ U := by
    rintro y ⟨v, hv, rfl⟩
    exact hafix.2 v hv
  rw [hmove] at hmap
  exact le_antisymm hUM hmap

/-- Fixing a generating set pointwise implies fixing its subgroup closure. -/
theorem fixes_closure (a : MulAut V) (T : Set V)
    (hT : ∀ t ∈ T, a t = t) :
    ∀ t ∈ Subgroup.closure T, a t = t := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem t ht => exact hT t ht
  | one => exact map_one a
  | mul t v _ _ ht hv => simp only [map_mul, ht, hv]
  | inv t _ ht => simp only [map_inv, ht]

/-- Operators generated by operators fixing M pointwise still fix M pointwise. -/
theorem fixes_of_mem_closure (M : Subgroup V) (B : Set (MulAut V))
    (hB : ∀ b ∈ B, ∀ t ∈ M, b t = t)
    {a : MulAut V} (ha : a ∈ Subgroup.closure B) :
    ∀ t ∈ M, a t = t := by
  induction ha using Subgroup.closure_induction with
  | mem b hb => exact hB b hb
  | one =>
      intro t _
      rfl
  | mul b c _ _ hb hc =>
      intro t ht
      change b (c t) = t
      rw [hc t ht, hb t ht]
  | inv b _ hb =>
      intro t ht
      apply b.injective
      simpa only [MulAut.apply_inv_self] using (hb t ht).symm

/-- If an operator fixes its moving subgroup and still moves that subgroup onto
itself, the moving subgroup is trivial. -/
theorem movingSubgroup_eq_bot_of_fixes
    (a : MulAut V)
    (hmove : (movingSubgroup a).map (delta a) = movingSubgroup a)
    (hfix : ∀ t ∈ movingSubgroup a, a t = t) :
    movingSubgroup a = ⊥ := by
  rw [← hmove]
  apply (Subgroup.map_eq_bot_iff (movingSubgroup a)).mpr
  intro t ht
  exact (delta_eq_one_iff a t).mpr (hfix t ht)

/-- An automorphism with trivial moving subgroup is the identity. -/
theorem eq_one_of_movingSubgroup_eq_bot
    (a : MulAut V) (h : movingSubgroup a = ⊥) : a = 1 := by
  apply MulEquiv.ext
  intro v
  have hv : delta a v ∈ movingSubgroup a := ⟨v, rfl⟩
  rw [h] at hv
  exact (delta_eq_one_iff a v).mp (Subgroup.mem_bot.mp hv)

end Kourovka2135.AbelianDifference
