import Kourovka2135.MinimalSimpleQuotient
import Kourovka2135.MinimalPerfectSubgroup
import Kourovka2135.PerfectSupplement
import Kourovka2135.RadicalCore

/-! The soluble radical of a smallest exception is its Frattini subgroup and p-core. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.radical_nongenerating
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (H : Subgroup G) (hH : H ⊔ solubleRadical G = ⊤) : H = ⊤ := by
  let : Group.IsPerfect G := h.isPerfect hp
  let R := solubleRadical G
  let P := pCore p G
  by_contra hne
  obtain ⟨K, hKH, hKR, hKperfect⟩ := exists_perfect_supplement R H hH
  let : Group.IsPerfect K := hKperfect
  have hKne : K ≠ ⊤ := fun heq => hne (top_le_iff.mp (heq ▸ hKH))
  let C := Subgroup.centralizer (P : Set G)
  have hKC : K ≤ C := h.proper_perfect_le_centralizer_pCore hp K hKne
  have hCR : C ⊔ R = ⊤ := top_le_iff.mp (hKR ▸ sup_le_sup_right hKC R)
  have hCtop : C = ⊤ := by
    by_contra hCne
    have hCsolv := h.proper_normal_isSolvable hp C hCne
    have hCRsolv := isSolvable_sup_of_normal C R hCsolv inferInstance
    rw [hCR] at hCRsolv
    let := hCRsolv
    exact h.not_isSolvable hp (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).surjective)
  have hPcenter : P ≤ Subgroup.center G := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
    exact (hg x hx).symm
  have hRcenter : R ≤ Subgroup.center G :=
    normal_soluble_le_center_of_pCore_le_center hp (h.pPrimeCore_eq_bot hp)
      hPcenter R inferInstance
  have hKnormal : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← hKR]
    exact sup_le K.le_normalizer (hRcenter.trans (Subgroup.center_le_normalizer _))
  let : K.Normal := hKnormal
  have hRcomm : IsMulCommutative R := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_center_iff.mp (hRcenter b.property) a)⟩⟩
  have hcommle : commutator G ≤ K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hKR hRcomm
  rw [Group.IsPerfect.commutator_eq_top] at hcommle
  exact hKne (top_le_iff.mp hcommle)

theorem OrderMinimalException.radical_le_frattini
    (h : OrderMinimalException w p G) (hp : p.Prime) : solubleRadical G ≤ frattini G := by
  apply le_iInf
  intro M
  apply le_iInf
  intro hM
  by_contra hn
  have hlt : M < M ⊔ solubleRadical G :=
    lt_of_le_of_ne le_sup_left (fun heq => hn (heq ▸ le_sup_right))
  have htop := hM.2 _ hlt
  exact hM.1 (h.radical_nongenerating hp M htop)

theorem OrderMinimalException.radical_eq_frattini
    (h : OrderMinimalException w p G) (hp : p.Prime) : solubleRadical G = frattini G := by
  apply le_antisymm (h.radical_le_frattini hp)
  let : Group.IsNilpotent (frattini G) := frattini_nilpotent
  exact le_solubleRadical _ inferInstance

theorem OrderMinimalException.radical_eq_pCore
    (h : OrderMinimalException w p G) (hp : p.Prime) : solubleRadical G = pCore p G := by
  let : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent (solubleRadical G) := by
    rw [h.radical_eq_frattini hp]
    exact frattini_nilpotent
  have hP : IsPGroup p (solubleRadical G) :=
    isPGroup_of_nilpotent_normal _ inferInstance hnil (h.pPrimeCore_eq_bot hp)
  apply le_antisymm
  · exact le_sSup (show (solubleRadical G).Normal ∧ IsPGroup p (solubleRadical G)
      from ⟨inferInstance, hP⟩)
  · let : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
    exact le_solubleRadical (pCore p G) inferInstance

end Kourovka2135
