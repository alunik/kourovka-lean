import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Order.SupClosed
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Set.Finite.Lattice

/-! The soluble radical of a finite group, built from normal soluble subgroups. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem isSolvable_sup_of_normal (A B : Subgroup G) [B.Normal]
    (hA : Group.IsSolvable A) (hB : Group.IsSolvable B) :
    Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let : Group.IsSolvable A := hA
  let : Group.IsSolvable B := hB
  let q := QuotientGroup.mk' B
  let : Group.IsSolvable (A.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective A)
  let g : (A ⊔ B : Subgroup G) →* A.map q := {
    toFun := fun x => ⟨q (x : G), by
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp x.property
      refine ⟨a, ha, ?_⟩
      have hbq : q b = 1 := (QuotientGroup.eq_one_iff _).mpr hb
      rw [← hab, map_mul, hbq, mul_one]⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun _ _ => Subtype.ext (map_mul q _ _) }
  let f : B →* (A ⊔ B : Subgroup G) := Subgroup.inclusion le_sup_right
  apply Group.isSolvable_of_ker_le_range f g
  intro x hx
  have hxq : q (x : G) = 1 := congrArg Subtype.val hx
  have hxB : (x : G) ∈ B := (QuotientGroup.eq_one_iff _).mp hxq
  exact ⟨⟨x, hxB⟩, rfl⟩

def normalSolubleSubgroups (G : Type u) [Group G] : Set (Subgroup G) :=
  {H | H.Normal ∧ Group.IsSolvable H}

def solubleRadical (G : Type u) [Group G] : Subgroup G := sSup (normalSolubleSubgroups G)

theorem normalSolubleSubgroups_supClosed : SupClosed (normalSolubleSubgroups G) := by
  intro A hA B hB
  let : A.Normal := hA.1
  let : B.Normal := hB.1
  exact ⟨Subgroup.sup_normal A B, isSolvable_sup_of_normal A B hA.2 hB.2⟩

theorem solubleRadical_mem [Finite G] : solubleRadical G ∈ normalSolubleSubgroups G := by
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G))
    SetLike.coe_injective
  apply normalSolubleSubgroups_supClosed.sSup_mem_of_nonempty (Set.toFinite _) ?_ Set.Subset.rfl
  exact ⟨⊥, inferInstance, inferInstance⟩

instance solubleRadical_normal [Finite G] : (solubleRadical G).Normal := solubleRadical_mem.1

instance solubleRadical_isSolvable [Finite G] : Group.IsSolvable (solubleRadical G) :=
  solubleRadical_mem.2

theorem le_solubleRadical (H : Subgroup G) [H.Normal] (hH : Group.IsSolvable H) :
    H ≤ solubleRadical G := le_sSup ⟨inferInstance, hH⟩

theorem solubleRadical_ne_top [Finite G] (hG : ¬ Group.IsSolvable G) :
    solubleRadical G ≠ ⊤ := by
  intro heq
  have htop : Group.IsSolvable (⊤ : Subgroup G) := heq ▸ solubleRadical_isSolvable
  let := htop
  exact hG (Group.isSolvable_of_surjective (f := Subgroup.topEquiv.toMonoidHom)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).surjective)

instance solubleRadical_characteristic [Finite G] : (solubleRadical G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  have hN : ((solubleRadical G).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hS : Group.IsSolvable ((solubleRadical G).map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  exact le_sSup ⟨hN, hS⟩

end Kourovka2135
