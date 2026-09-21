import Kourovka2135.MinimalFrattini
import Kourovka2135.PerfectResidual

/-!
If the radical of a smallest exception is noncentral, its prime-to-p derived
values vanish and all proper subgroups are soluble. Excluding a central radical
is a separate, still outstanding obligation in the unrestricted proof.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.centralizer_radical_le
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G) :
    Subgroup.centralizer (solubleRadical G : Set G) ≤ solubleRadical G := by
  let C := Subgroup.centralizer (solubleRadical G : Set G)
  have hCne : C ≠ ⊤ := by
    intro heq
    apply hnoncentral
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hg : g ∈ C := heq ▸ Subgroup.mem_top g
    exact (hg x hx).symm
  exact le_solubleRadical C (h.proper_normal_isSolvable hp C hCne)

theorem OrderMinimalException.derivedValue_eq_one_of_coprime
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    {k : ℕ} (hk : w.height ≤ k) {x : G}
    (hx : x ∈ (OuterWord.derivedWord k).values G) (hxp : ¬ p ∣ orderOf x) : x = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let R := solubleRadical G
  have hR : IsPGroup p R := by
    change IsPGroup p (solubleRadical G)
    rw [h.radical_eq_pCore hp]
    exact pCore_isPGroup
  have hd : ProductOrderCondition (OuterWord.derivedWord k) p G := by
    intro a ha b hb hap hbp
    exact h.condition a (w.derivedWord_values_subset k hk ha)
      b (w.derivedWord_values_subset k hk hb) hap hbp
  have hxcent : x ∈ Subgroup.centralizer (R : Set G) := by
    intro g hg
    exact (hd.derivedValue_centralizes_pSubgroup hp R hR hx hxp
      (by rw [Subgroup.normalizer_eq_top]; trivial) g hg).eq
  have hxR := h.centralizer_radical_le hp hnoncentral hxcent
  by_contra hne
  have hneR : (⟨x, hxR⟩ : R) ≠ 1 := fun heq => hne (congrArg Subtype.val heq)
  exact hxp (by simpa only [Subgroup.orderOf_mk] using hR.dvd_orderOf hneR)

theorem OrderMinimalException.proper_perfect_eq_bot
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (H : Subgroup G) (hne : H ≠ ⊤) [Group.IsPerfect H] : H = ⊥ := by
  let d := OuterWord.derivedWord w.height
  have hcard := h.proper_perfect_coprime_card hp H hne
  have hv : d.verbalSubgroup H ≤ ⊥ := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    apply Subtype.ext
    apply h.derivedValue_eq_one_of_coprime hp hnoncentral le_rfl
      (d.map_mem_values H.subtype hx)
    intro hdiv
    change p ∣ orderOf (x : G) at hdiv
    rw [Subgroup.orderOf_coe x] at hdiv
    exact (hp.coprime_iff_not_dvd.mp hcard.symm)
      (hdiv.trans (orderOf_dvd_natCard x))
  apply bot_unique
  intro x hx
  change x = 1
  have hxD : (⟨x, hx⟩ : H) ∈ d.verbalSubgroup H := by
    rw [d.verbalSubgroup_eq_top_of_isPerfect]
    trivial
  exact congrArg Subtype.val (show (⟨x, hx⟩ : H) = 1 from hv hxD)

theorem OrderMinimalException.proper_subgroup_isSolvable
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (H : Subgroup G) (hne : H ≠ ⊤) : Group.IsSolvable H := by
  apply isSolvable_of_perfect_subgroups_trivial
  intro K hK
  let : Group.IsPerfect K := hK
  let : Group.IsPerfect (K.map H.subtype) := Group.IsPerfect.map H.subtype
  have hmapne : K.map H.subtype ≠ ⊤ := fun heq => hne (top_le_iff.mp
    (heq ▸ Subgroup.map_subtype_le K))
  have hbot := h.proper_perfect_eq_bot hp hnoncentral (K.map H.subtype) hmapne
  apply Subgroup.map_injective H.subtype_injective
  simpa only [Subgroup.map_bot] using hbot

end Kourovka2135
