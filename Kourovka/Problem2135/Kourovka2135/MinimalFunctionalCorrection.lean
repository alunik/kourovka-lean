import Kourovka2135.ClassTwoConjugation
import Kourovka2135.MinimalSymplecticForm
import Kourovka2135.LinearDualCorrection

/-! Correction of an ambient conjugation by an inner conjugation on one linear functional. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
open ClassTwoAdditive
variable {G : Type u} [Group G] [Finite G]

theorem exists_inner_functional_correction
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian p (commutator N)]
    (D : ClassTwoData N) [Module (ZMod p) (ClassTwoAdditive D)]
    (ell : ClassTwoAdditive D →ₗ[ZMod p] ZMod p)
    (hell : ell.comp ((centralEmbedding D (commutator N) D.central).toZModLinearMap p) ≠ 0)
    (g : G) :
    ∃ n : N, ∀ x : ClassTwoAdditive D,
      ell (mapAut D (MulAut.conjNormal g) x) =
        ell (mapAut D (MulAut.conjNormal (n : G)) x) := by
  let j := (centralEmbedding D (commutator N) D.central).toZModLinearMap p
  let lam := ell.comp j
  let q := (quotientMap D (QuotientGroup.mk' (Subgroup.center N))).toZModLinearMap p
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) v.toMul
    exact ⟨ofMul D a, ha⟩
  let d := ell.comp ((mapAut D (MulAut.conjNormal g)).toAddMonoidHom.toZModLinearMap p) - ell
  have hd : q.ker ≤ d.ker := by
    intro x hx
    have hxc : toMul D x ∈ Subgroup.center N := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact hx
    change ell (mapAut D (MulAut.conjNormal g) x) - ell x = 0
    rw [normalConjugation_fixed_of_center N D hZ g x hxc, sub_self]
  let B := scalarCommutatorForm
    (minimal_noncentral_commutator_le_internal_center N hmin) p lam
  have hB : ∀ x, (∀ y, B x y = 0) → x = 0 := by
    intro x hx
    exact minimal_noncentral_scalarCommutatorForm_nondegenerate N hmin p lam hell hx
  obtain ⟨v, hv⟩ := exists_bilinear_correction B hB q hq d hd
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) v.toMul
  refine ⟨n, ?_⟩
  intro x
  have hc := hv x
  have hvn : v = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) n) := hn.symm
  rw [hvn] at hc
  change ell (ofMul D (paperCommutator n (toMul D x))) =
    ell (mapAut D (MulAut.conjNormal g) x) - ell x at hc
  have hin : mapAut D (MulAut.conjNormal (n : G)) x =
      x + ofMul D (paperCommutator n (toMul D x)) := by
    exact ofMul_conj_eq_add D n (toMul D x)
  rw [hin, map_add]
  exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp hc) |>.symm

end Kourovka2135
