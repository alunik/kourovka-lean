import Kourovka2135.MinimalException
import Kourovka2135.SolubleRadical
import Mathlib.GroupTheory.Subgroup.Simple

/-! The quotient of a smallest exception by its soluble radical is nonabelian simple. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.quotient_radical_isSimple
    (h : OrderMinimalException w p G) (hp : p.Prime) :
    IsSimpleGroup (G ⧸ solubleRadical G) := by
  let R := solubleRadical G
  let q := QuotientGroup.mk' R
  let : Nontrivial (G ⧸ R) :=
    QuotientGroup.nontrivial_iff.mpr (solubleRadical_ne_top (h.not_isSolvable hp))
  refine ⟨?_⟩
  intro C hC
  let : C.Normal := hC
  by_cases htop : C.comap q = ⊤
  · right
    exact Subgroup.comap_injective (QuotientGroup.mk'_surjective R)
      (htop.trans (Subgroup.comap_top q).symm)
  · left
    have hle : C.comap q ≤ R :=
      le_solubleRadical _ (h.proper_normal_isSolvable hp _ htop)
    apply bot_unique
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) C]
    exact ((C.comap q).map_eq_bot_iff.mpr (by
      simpa only [QuotientGroup.ker_mk'] using hle)).le

theorem OrderMinimalException.quotient_radical_not_isMulCommutative
    (h : OrderMinimalException w p G) (hp : p.Prime) :
    ¬ IsMulCommutative (G ⧸ solubleRadical G) := by
  let := h.isPerfect hp
  let := h.quotient_radical_isSimple hp
  exact Group.IsPerfect.not_isMulCommutative _

end Kourovka2135
