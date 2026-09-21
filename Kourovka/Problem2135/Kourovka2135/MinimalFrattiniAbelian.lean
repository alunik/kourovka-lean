import Kourovka2135.MinimalFunctionalCorrection
import Kourovka2135.FunctionStabilizer

/-! A functional stabilizer forces a minimal noncentral Frattini kernel with corrected prime-field addition to be abelian. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
open ClassTwoAdditive
variable {G : Type u} [Group G] [Finite G]

theorem minimal_frattini_isMulCommutative_of_classTwoModule
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hFrattini : N ≤ frattini G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian p (commutator N)]
    (D : ClassTwoData N) [Module (ZMod p) (ClassTwoAdditive D)] :
    IsMulCommutative N := by
  classical
  by_contra hnonabelian
  have hDne : commutator N ≠ ⊥ := by
    intro hbot
    exact hnonabelian ((commutator_eq_bot_iff N).mp hbot)
  let derivedNontrivial : Nontrivial (commutator N) := (Subgroup.nontrivial_iff_ne_bot _).mpr hDne
  obtain ⟨t, ht⟩ := exists_ne (1 : commutator N)
  have htadd : ofMul D (t : N) ≠ 0 := by
    intro h
    apply ht
    apply Subtype.ext
    exact congrArg (toMul D) h
  have hex : ∃ ell : ClassTwoAdditive D →ₗ[ZMod p] ZMod p,
      ell (ofMul D (t : N)) ≠ 0 := exists_linear_functional_ne_zero (K := ZMod p) htadd
  obtain ⟨ell, hellt⟩ := hex
  have hell : ell.comp ((centralEmbedding D (commutator N) D.central).toZModLinearMap p) ≠ 0 := by
    intro h
    apply hellt
    exact congrArg (fun f : Additive (commutator N) →ₗ[ZMod p] ZMod p =>
      f (Additive.ofMul t)) h
  have hZ := minimal_noncentral_center_le N hnonabelian hmin
  let f : ClassTwoAdditive D → ZMod p := ell
  let conjugationAction : MulAction G (ClassTwoAdditive D) := normalConjugationAction N D
  have hc : ∀ g : G, ∃ n ∈ N, ∀ x : ClassTwoAdditive D, f (g • x) = f (n • x) := by
    intro g
    obtain ⟨n, hn⟩ := exists_inner_functional_correction N hmin hZ p D ell hell g
    exact ⟨n, n.property, hn⟩
  have hH := functionStabilizer_eq_top_of_frattini_correction f N hFrattini hc
  have hfix (g : G) (x : ClassTwoAdditive D) : f (g • x) = f x := by
    have hg : g ∈ functionStabilizer f := by rw [hH]; trivial
    exact hg x
  have hnc : ∃ n : N, n ∉ Subgroup.center N := by
    by_contra h
    push Not at h
    apply hnonabelian
    apply Subgroup.center_eq_top_iff.mp
    exact top_le_iff.mp (fun n _ => h n)
  obtain ⟨n, hn⟩ := hnc
  obtain ⟨y, hy⟩ := exists_paperCommutator_eq_of_minimal_noncentral N hmin n hn t
  have heq : f (ofMul D y) + f (ofMul D (paperCommutator n y)) = f (ofMul D y) := by
    change ell (ofMul D y) + ell (ofMul D (paperCommutator n y)) = _
    rw [← ell.map_add]
    have hin := ofMul_conj_eq_add D n y
    change ofMul D (n * y * n⁻¹) = ofMul D y + ofMul D (paperCommutator n y) at hin
    change f (ofMul D y + ofMul D (paperCommutator n y)) = f (ofMul D y)
    rw [← hin]
    exact hfix (n : G) (ofMul D y)
  have hz : f (ofMul D (paperCommutator n y)) = 0 :=
    add_left_cancel (heq.trans (add_zero _).symm)
  rw [hy] at hz
  exact hellt hz

end Kourovka2135
