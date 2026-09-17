import Kourovka.Problem2153.Borel
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem

theorem N_le_normalizer_H : N ≤ Subgroup.normalizer (H : Set G) :=
  sup_le H.le_normalizer W_le_normalizer_H

instance B_subgroupOf_N_normal : (B.subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, B_inf_N]
  exact N_le_normalizer_H

abbrev WeylQuotient := N ⧸ B.subgroupOf N

def rN : N := ⟨r, (show W ≤ N from le_sup_right) r_mem_W⟩
def sN : N := ⟨s, (show W ≤ N from le_sup_right) s_mem_W⟩
def wN (i : Fin 16) : N := ⟨Weyl.rep i, (show W ≤ N from le_sup_right) (Weyl.rep_mem_W i)⟩
def hN (h : G) (hh : h ∈ H) : N := ⟨h, (show H ≤ N from le_sup_left) hh⟩
def quotientMap : N →* WeylQuotient := QuotientGroup.mk' (B.subgroupOf N)
def simpleImages : Set WeylQuotient := {quotientMap rN, quotientMap sN}

theorem quotient_hN (h : G) (hh : h ∈ H) : quotientMap (hN h hh) = 1 := by
  apply (QuotientGroup.eq_one_iff (N := B.subgroupOf N) _).mpr
  exact (show H ≤ B from le_sup_right) hh

private def wordN (l : List Bool) : N :=
  ⟨Weyl.evalWord l, (show W ≤ N from le_sup_right) (Weyl.evalWord_mem_W l)⟩

private theorem quotient_wordN_mem (l : List Bool) :
    quotientMap (wordN l) ∈ Subgroup.closure simpleImages := by
  induction l with
  | nil => exact (Subgroup.closure simpleImages).one_mem
  | cons b l ih =>
    have he : wordN (b :: l) = (if b then sN else rN) * wordN l := by
      apply Subtype.ext
      cases b <;> rfl
    rw [he, map_mul]
    apply (Subgroup.closure simpleImages).mul_mem _ ih
    apply Subgroup.subset_closure
    cases b <;> simp [simpleImages]

theorem closure_simpleImages : Subgroup.closure simpleImages = ⊤ := by
  apply ReeStructural.quotient_generated_of_factor_words quotientMap
    (QuotientGroup.mk'_surjective _) simpleImages wN
  · intro n
    obtain ⟨h,hh,i,he⟩ := N_factor n.property
    exact ⟨hN h hh,i,quotient_hN h hh,Subtype.ext he⟩
  · intro i
    exact quotient_wordN_mem (WeylData.words i)

end Kourovka.Problem2153.RootSystem
