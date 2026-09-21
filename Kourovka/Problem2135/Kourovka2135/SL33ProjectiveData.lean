import Kourovka2135.PSL33GoodSets
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Explicit coordinates for the actual PG(2,3) action. The finite producer
only supplies thirteen vectors and short matrix words. Every numerical
identity below is intended for ordinary kernel-checked `decide`.
The two named generators have projective permutations inverse to the ATLAS
right-row permutations; the resulting column action is inverse-transpose. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SL33ProjectiveData
open scoped MatrixGroups LinearAlgebra.Projectivization
abbrev S := SL33Witnesses.S
abbrev Q := PSL33GoodSets.Q
abbrev Point := ℙ (ZMod 3) (Fin 3 → ZMod 3)

def representative : Fin 13 → Fin 3 → ZMod 3 :=
  ![![0, 0, 1],
    ![0, 1, 0],
    ![1, 0, 2],
    ![1, 2, 1],
    ![1, 2, 0],
    ![0, 1, 2],
    ![1, 0, 1],
    ![1, 1, 1],
    ![1, 2, 2],
    ![0, 1, 1],
    ![1, 0, 0],
    ![1, 1, 2],
    ![1, 1, 0]]

theorem representative_ne_zero (i : Fin 13) : representative i ≠ 0 := by
  revert i
  decide

def point (i : Fin 13) : Point :=
  Projectivization.mk (ZMod 3) (representative i) (representative_ne_zero i)

theorem point_injective : Function.Injective point := by
  have hc : ∀ i j : Fin 13, (∃ c : ZMod 3, c • representative j = representative i) → i = j := by
    decide
  intro i j hij
  exact hc i j ((Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mp hij)

theorem point_surjective : Function.Surjective point := by
  have hc : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
      ∃ i : Fin 13, ∃ c : ZMod 3, c • v = representative i := by decide
  intro p
  obtain ⟨i, c, hi⟩ := hc p.rep p.rep_nonzero
  refine ⟨i, ?_⟩
  rw [← Projectivization.mk_rep p]
  exact (Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr ⟨c, hi⟩

def pointEquiv : Fin 13 ≃ Point := Equiv.ofBijective point ⟨point_injective, point_surjective⟩

/-- The actual PSL action, expressed in the listed coordinates. -/
def permutation : Q →* Equiv.Perm (Fin 13) where
  toFun g := pointEquiv.symm.permCongr (Projectivization.PSLAction.toPermHom g)
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp [Equiv.permCongr_apply]

theorem point_permutation (g : Q) (i : Fin 13) :
    point (permutation g i) = g • point i := by
  change pointEquiv (pointEquiv.symm (g • pointEquiv i)) = _
  exact pointEquiv.apply_symm_apply _

def a : S := ⟨!![0, 2, 0; 2, 0, 0; 2, 1, 2], by decide⟩
def b : S := ⟨!![2, 0, 1; 2, 0, 2; 0, 1, 1], by decide⟩

def permA : Equiv.Perm (Fin 13) where
  toFun i := ![0, 2, 1, 4, 3, 6, 5, 7, 8, 10, 9, 11, 12] i
  invFun i := ![0, 2, 1, 4, 3, 6, 5, 7, 8, 10, 9, 11, 12] i
  left_inv := by decide
  right_inv := by decide

def permB : Equiv.Perm (Fin 13) where
  toFun i := ![3, 0, 2, 1, 7, 4, 9, 5, 6, 8, 12, 10, 11] i
  invFun i := ![1, 3, 2, 0, 5, 7, 8, 4, 9, 6, 11, 12, 10] i
  left_inv := by decide
  right_inv := by decide

theorem a_point (i : Fin 13) :
    a • point i = point (permA i) := by
  have hc : ∀ j : Fin 13, ∃ c : ZMod 3,
      c • representative (permA j) = (a.val).mulVec (representative j) := by decide
  change Projectivization.mk (ZMod 3) _ _ = Projectivization.mk (ZMod 3) _ _
  apply (Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr
  exact hc i

theorem permutation_a : permutation (PSL33GoodSets.q a) = permA := by
  apply Equiv.ext
  intro i
  apply point_injective
  rw [point_permutation]
  exact a_point i

theorem b_point (i : Fin 13) :
    b • point i = point (permB i) := by
  have hc : ∀ j : Fin 13, ∃ c : ZMod 3,
      c • representative (permB j) = (b.val).mulVec (representative j) := by decide
  change Projectivization.mk (ZMod 3) _ _ = Projectivization.mk (ZMod 3) _ _
  apply (Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr
  exact hc i

theorem permutation_b : permutation (PSL33GoodSets.q b) = permB := by
  apply Equiv.ext
  intro i
  apply point_injective
  rw [point_permutation]
  exact b_point i

def a13Step0 : S := ⟨!![2, 0, 1; 2, 0, 2; 0, 1, 1], by decide⟩
def a13Step1 : S := ⟨!![2, 2, 2; 1, 0, 1; 1, 1, 2], by decide⟩
def a13Step2 : S := ⟨!![2, 2, 2; 2, 1, 2; 1, 2, 2], by decide⟩
def a13Step3 : S := ⟨!![2, 0, 1; 0, 0, 1; 2, 1, 1], by decide⟩
def a13Step4 : S := ⟨!![1, 1, 0; 0, 1, 1; 0, 1, 2], by decide⟩
def a13Step5 : S := ⟨!![1, 0, 0; 2, 1, 0; 2, 2, 1], by decide⟩
def a13Step6 : S := ⟨!![0, 2, 0; 2, 1, 0; 0, 2, 2], by decide⟩
def a13Step7 : S := ⟨!![1, 0, 1; 0, 0, 1; 1, 2, 0], by decide⟩
def a13Step8 : S := ⟨!![2, 0, 2; 2, 1, 2; 1, 2, 0], by decide⟩
def a13Step9 : S := ⟨!![1, 2, 1; 0, 2, 0; 0, 0, 2], by decide⟩
def a13Step10 : S := ⟨!![0, 0, 2; 1, 0, 0; 1, 2, 1], by decide⟩
def a13Step11 : S := ⟨!![0, 2, 2; 2, 0, 1; 0, 1, 0], by decide⟩
def a13Step12 : S := ⟨!![2, 2, 1; 2, 2, 2; 2, 0, 0], by decide⟩
def a13Step13 : S := ⟨!![2, 1, 1; 2, 2, 2; 1, 0, 2], by decide⟩
def a13Step14 : S := ⟨!![1, 2, 2; 2, 0, 1; 1, 1, 1], by decide⟩
def a13Step15 : S := ⟨!![0, 2, 1; 1, 1, 0; 1, 1, 1], by decide⟩
def a13Step16 : S := ⟨!![1, 1, 2; 1, 0, 0; 1, 1, 1], by decide⟩

theorem old_a13_mem (H : Subgroup S) (ha : a ∈ H) (hb : b ∈ H) :
    SL33Witnesses.a13 ∈ H := by
  have h0 : a13Step0 ∈ H := by
    have he : (1 : S) * b = a13Step0 := by decide
    exact he ▸ H.mul_mem H.one_mem hb
  have h1 : a13Step1 ∈ H := by
    have he : a13Step0 * a = a13Step1 := by decide
    exact he ▸ H.mul_mem h0 ha
  have h2 : a13Step2 ∈ H := by
    have he : a13Step1 * b = a13Step2 := by decide
    exact he ▸ H.mul_mem h1 hb
  have h3 : a13Step3 ∈ H := by
    have he : a13Step2 * a = a13Step3 := by decide
    exact he ▸ H.mul_mem h2 ha
  have h4 : a13Step4 ∈ H := by
    have he : a13Step3 * b = a13Step4 := by decide
    exact he ▸ H.mul_mem h3 hb
  have h5 : a13Step5 ∈ H := by
    have he : a13Step4 * b = a13Step5 := by decide
    exact he ▸ H.mul_mem h4 hb
  have h6 : a13Step6 ∈ H := by
    have he : a13Step5 * a = a13Step6 := by decide
    exact he ▸ H.mul_mem h5 ha
  have h7 : a13Step7 ∈ H := by
    have he : a13Step6 * b = a13Step7 := by decide
    exact he ▸ H.mul_mem h6 hb
  have h8 : a13Step8 ∈ H := by
    have he : a13Step7 * a = a13Step8 := by decide
    exact he ▸ H.mul_mem h7 ha
  have h9 : a13Step9 ∈ H := by
    have he : a13Step8 * b = a13Step9 := by decide
    exact he ▸ H.mul_mem h8 hb
  have h10 : a13Step10 ∈ H := by
    have he : a13Step9 * a = a13Step10 := by decide
    exact he ▸ H.mul_mem h9 ha
  have h11 : a13Step11 ∈ H := by
    have he : a13Step10 * b = a13Step11 := by decide
    exact he ▸ H.mul_mem h10 hb
  have h12 : a13Step12 ∈ H := by
    have he : a13Step11 * a = a13Step12 := by decide
    exact he ▸ H.mul_mem h11 ha
  have h13 : a13Step13 ∈ H := by
    have he : a13Step12 * b = a13Step13 := by decide
    exact he ▸ H.mul_mem h12 hb
  have h14 : a13Step14 ∈ H := by
    have he : a13Step13 * a = a13Step14 := by decide
    exact he ▸ H.mul_mem h13 ha
  have h15 : a13Step15 ∈ H := by
    have he : a13Step14 * b = a13Step15 := by decide
    exact he ▸ H.mul_mem h14 hb
  have h16 : a13Step16 ∈ H := by
    have he : a13Step15 * b = a13Step16 := by decide
    exact he ▸ H.mul_mem h15 hb
  have he : a13Step16 = SL33Witnesses.a13 := by decide
  exact he ▸ h16

def b13Step0 : S := ⟨!![2, 0, 1; 2, 0, 2; 0, 1, 1], by decide⟩
def b13Step1 : S := ⟨!![2, 2, 2; 1, 0, 1; 1, 1, 2], by decide⟩
def b13Step2 : S := ⟨!![2, 2, 2; 2, 1, 2; 1, 2, 2], by decide⟩
def b13Step3 : S := ⟨!![2, 0, 1; 0, 0, 1; 2, 1, 1], by decide⟩
def b13Step4 : S := ⟨!![1, 1, 0; 0, 1, 1; 0, 1, 2], by decide⟩
def b13Step5 : S := ⟨!![2, 2, 0; 1, 1, 2; 0, 2, 1], by decide⟩
def b13Step6 : S := ⟨!![2, 0, 0; 1, 2, 2; 1, 1, 2], by decide⟩
def b13Step7 : S := ⟨!![0, 1, 0; 2, 1, 1; 0, 1, 1], by decide⟩
def b13Step8 : S := ⟨!![2, 0, 2; 0, 1, 2; 2, 1, 0], by decide⟩
def b13Step9 : S := ⟨!![1, 2, 1; 2, 2, 1; 0, 0, 1], by decide⟩
def b13Step10 : S := ⟨!![0, 0, 2; 0, 2, 2; 2, 1, 2], by decide⟩
def b13Step11 : S := ⟨!![0, 2, 2; 1, 2, 0; 0, 2, 0], by decide⟩
def b13Step12 : S := ⟨!![2, 2, 1; 1, 2, 0; 1, 0, 0], by decide⟩
def b13Step13 : S := ⟨!![2, 1, 1; 0, 0, 2; 2, 0, 1], by decide⟩
def b13Step14 : S := ⟨!![1, 2, 2; 1, 2, 1; 2, 2, 2], by decide⟩
def b13Step15 : S := ⟨!![0, 2, 1; 0, 1, 0; 2, 2, 2], by decide⟩
def b13Step16 : S := ⟨!![0, 1, 2; 2, 0, 0; 2, 0, 1], by decide⟩
def b13Step17 : S := ⟨!![2, 2, 1; 1, 0, 2; 1, 1, 0], by decide⟩

theorem old_b13_mem (H : Subgroup S) (ha : a ∈ H) (hb : b ∈ H) :
    SL33Witnesses.b13 ∈ H := by
  have h0 : b13Step0 ∈ H := by
    have he : (1 : S) * b = b13Step0 := by decide
    exact he ▸ H.mul_mem H.one_mem hb
  have h1 : b13Step1 ∈ H := by
    have he : b13Step0 * a = b13Step1 := by decide
    exact he ▸ H.mul_mem h0 ha
  have h2 : b13Step2 ∈ H := by
    have he : b13Step1 * b = b13Step2 := by decide
    exact he ▸ H.mul_mem h1 hb
  have h3 : b13Step3 ∈ H := by
    have he : b13Step2 * a = b13Step3 := by decide
    exact he ▸ H.mul_mem h2 ha
  have h4 : b13Step4 ∈ H := by
    have he : b13Step3 * b = b13Step4 := by decide
    exact he ▸ H.mul_mem h3 hb
  have h5 : b13Step5 ∈ H := by
    have he : b13Step4 * a = b13Step5 := by decide
    exact he ▸ H.mul_mem h4 ha
  have h6 : b13Step6 ∈ H := by
    have he : b13Step5 * b = b13Step6 := by decide
    exact he ▸ H.mul_mem h5 hb
  have h7 : b13Step7 ∈ H := by
    have he : b13Step6 * a = b13Step7 := by decide
    exact he ▸ H.mul_mem h6 ha
  have h8 : b13Step8 ∈ H := by
    have he : b13Step7 * b = b13Step8 := by decide
    exact he ▸ H.mul_mem h7 hb
  have h9 : b13Step9 ∈ H := by
    have he : b13Step8 * b = b13Step9 := by decide
    exact he ▸ H.mul_mem h8 hb
  have h10 : b13Step10 ∈ H := by
    have he : b13Step9 * a = b13Step10 := by decide
    exact he ▸ H.mul_mem h9 ha
  have h11 : b13Step11 ∈ H := by
    have he : b13Step10 * b = b13Step11 := by decide
    exact he ▸ H.mul_mem h10 hb
  have h12 : b13Step12 ∈ H := by
    have he : b13Step11 * a = b13Step12 := by decide
    exact he ▸ H.mul_mem h11 ha
  have h13 : b13Step13 ∈ H := by
    have he : b13Step12 * b = b13Step13 := by decide
    exact he ▸ H.mul_mem h12 hb
  have h14 : b13Step14 ∈ H := by
    have he : b13Step13 * a = b13Step14 := by decide
    exact he ▸ H.mul_mem h13 ha
  have h15 : b13Step15 ∈ H := by
    have he : b13Step14 * b = b13Step15 := by decide
    exact he ▸ H.mul_mem h14 hb
  have h16 : b13Step16 ∈ H := by
    have he : b13Step15 * a = b13Step16 := by decide
    exact he ▸ H.mul_mem h15 ha
  have h17 : b13Step17 ∈ H := by
    have he : b13Step16 * b = b13Step17 := by decide
    exact he ▸ H.mul_mem h16 hb
  have he : b13Step17 = SL33Witnesses.b13 := by decide
  exact he ▸ h17

theorem generating : Subgroup.closure ({a, b} : Set S) = ⊤ := by
  apply top_unique
  rw [← SL33Witnesses.generating13]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  have ha : a ∈ Subgroup.closure ({a, b} : Set S) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a, b} : Set S) := Subgroup.subset_closure (by simp)
  rcases (show x = SL33Witnesses.a13 ∨ x = SL33Witnesses.b13 by simpa using hx) with rfl | rfl
  · exact old_a13_mem _ ha hb
  · exact old_b13_mem _ ha hb

theorem generating_projective :
    Subgroup.closure ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q) = ⊤ := by
  have h := congrArg (Subgroup.map PSL33GoodSets.q) generating
  have ht : (⊤ : Subgroup S).map PSL33GoodSets.q = ⊤ :=
    Subgroup.map_top_of_surjective PSL33GoodSets.q (QuotientGroup.mk'_surjective _)
  simpa only [MonoidHom.map_closure, Set.image_pair, ht] using h

end Kourovka2135.SL33ProjectiveData
