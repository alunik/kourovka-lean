import Kourovka2135.SuzukiPrincipalSeries
import Kourovka2135.CoinducedCharacterCyclic

/-! The actual two coordinates of root-fixed principal-series functions.
Bruhat decomposition determines such a function by its values at 1 and W.
The two torus weights are the inducing character and its inverse. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.SuzukiPrincipalSeriesCoordinates

open BenderSuzuki.MatrixGroups SuzukiGeometry SuzukiPrincipalSeriesBorel
open SuzukiPrincipalSeries SuzukiNaturalBorelFiltration
open scoped MatrixGroups

variable (m : ℕ) {k : Type u} [Field k] (σ : K m →+* k) (n : ℕ)

def weyl : G m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem weyl_mul_self : weyl m * weyl m = 1 :=
  Subtype.ext (suzukiWeylGL_mul_self m)

theorem weyl_not_mem_borel : weyl m ∉ borel m := by
  intro h
  have he := matrix_upper m (⟨weyl m, h⟩ : borel m) 3 0 (by decide)
  change (1 : K m) = 0 at he
  exact one_ne_zero he

/-- The audited matrix Bruhat decomposition, in the actual group and subgroups. -/
theorem bruhat (g : G m) :
    g ∈ borel m ∨ ∃ (b : borel m) (r : root m),
      g = (b : G m) * weyl m * (r : G m) := by
  rcases suzukiMatrixGroup_bruhat_decomposition m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    g.val g.property with hg | ⟨b, r, hb, hr, he⟩
  · exact Or.inl hg
  · refine Or.inr ⟨⟨⟨b, borelGL_le_group m hb⟩, hb⟩,
      ⟨⟨r, rootGL_le_group m hr⟩, hr⟩, ?_⟩
    exact Subtype.ext he

abbrev RootFixed (f : Space m σ n) : Prop :=
  ∀ r : root m, representation m σ n (r : G m) f = f

/-- Root invariance removes the final root coordinate of a Bruhat word. -/
theorem rootFixed_bruhat (f : Space m σ n) (hf : RootFixed m σ n f)
    (b : borel m) (r : root m) :
    f.val ((b : G m) * weyl m * (r : G m)) =
      (character m σ n b : k) * f.val (weyl m) := by
  rw [mul_assoc, covariance]
  have hr := congrArg (fun v : Space m σ n => v.val (weyl m)) (hf r)
  exact congrArg (fun x : k => (character m σ n b : k) * x) hr

/-- No coordinate equivalence is assumed: the actual Bruhat cells prove
injectivity of these two evaluations on the root-fixed subspace. -/
theorem rootFixed_ext (f h : Space m σ n)
    (hf : RootFixed m σ n f) (hh : RootFixed m σ n h)
    (h1 : f.val 1 = h.val 1) (hW : f.val (weyl m) = h.val (weyl m)) : f = h := by
  apply Subtype.ext
  funext g
  rcases bruhat m g with hg | ⟨b, r, rfl⟩
  · have hf' := covariance m σ n f (⟨g, hg⟩ : borel m) 1
    have hh' := covariance m σ n h (⟨g, hg⟩ : borel m) 1
    rw [h1] at hf'
    simpa only [mul_one] using hf'.trans hh'.symm
  · rw [rootFixed_bruhat m σ n f hf, rootFixed_bruhat m σ n h hh, hW]

def delta : Space m σ n := CoinducedCharacterCyclic.delta (borel m) (character m σ n)

@[simp] theorem delta_one : (delta m σ n).val 1 = 1 :=
  CoinducedCharacterCyclic.delta_one _ _

@[simp] theorem delta_weyl : (delta m σ n).val (weyl m) = 0 :=
  CoinducedCharacterCyclic.delta_apply_not_mem _ _ _ (weyl_not_mem_borel m)

theorem delta_rootFixed : RootFixed m σ n (delta m σ n) := by
  intro r
  have he := CoinducedCharacterCyclic.induced_delta (borel m) (character m σ n)
    (rootInBorel m r)
  change representation m σ n (r : G m) (delta m σ n) =
    (character m σ n (rootInBorel m r) : k) • delta m σ n at he
  simpa only [character_root, Units.val_one, one_smul] using he

theorem eq_top_of_delta_mem (W : Submodule k (Space m σ n))
    (hstable : ∀ (g : G m) (f : Space m σ n), f ∈ W → representation m σ n g f ∈ W)
    (hdelta : delta m σ n ∈ W) : W = ⊤ :=
  CoinducedCharacterCyclic.eq_top_of_delta_mem _ _ W hstable hdelta

/-- Root-fixed functions remain root-fixed under the actual torus. -/
theorem rootFixed_torus (f : Space m σ n) (hf : RootFixed m σ n f) (a : (K m)ˣ) :
    RootFixed m σ n (representation m σ n (SuzukiTorusMovingRank.torusHom m a) f) := by
  intro r
  let t := SuzukiTorusMovingRank.torusHom m a
  have hmem : t⁻¹ * (r : G m) * t ∈ root m := by
    have he := torus_conjugate_mem_root m a⁻¹ r
    simpa only [map_inv, inv_inv] using he
  let r' : root m := ⟨t⁻¹ * (r : G m) * t, hmem⟩
  have he : (r : G m) * t = t * (r' : G m) := by dsimp [r']; group
  change (representation m σ n (r : G m)) (representation m σ n t f) =
    representation m σ n t f
  calc
    _ = representation m σ n ((r : G m) * t) f :=
      congrArg (fun T : Module.End k (Space m σ n) => T f)
        ((representation m σ n).map_mul _ _).symm
    _ = representation m σ n (t * (r' : G m)) f := by rw [he]
    _ = representation m σ n t (representation m σ n (r' : G m) f) :=
      congrArg (fun T : Module.End k (Space m σ n) => T f)
        ((representation m σ n).map_mul _ _)
    _ = representation m σ n t f := by rw [hf r']

theorem torus_coordinate_one (f : Space m σ n) (a : (K m)ˣ) :
    (representation m σ n (SuzukiTorusMovingRank.torusHom m a) f).val 1 =
      σ ((a⁻¹ : (K m)ˣ) : K m) ^ n * f.val 1 := by
  have he := covariance m σ n f (torusInBorel m a) 1
  change f.val (SuzukiTorusMovingRank.torusHom m a * 1) =
    (character m σ n (torusInBorel m a) : k) * f.val 1 at he
  simpa only [SuzukiPrincipalSeries.representation_apply, one_mul, mul_one, character_torus] using he

theorem weyl_torus (a : (K m)ˣ) :
    weyl m * SuzukiTorusMovingRank.torusHom m a =
      SuzukiTorusMovingRank.torusHom m a⁻¹ * weyl m := by
  apply Subtype.ext
  change SuzukiWeylGL m * SuzukiTorusGL m a =
    SuzukiTorusGL m a⁻¹ * SuzukiWeylGL m
  have he := congrArg (fun g : GL (Fin 4) (K m) => g * SuzukiWeylGL m)
    (suzukiWeylGL_conj_torus m a)
  simpa only [mul_assoc, suzukiWeylGL_mul_self, mul_one] using he

theorem torus_coordinate_weyl (f : Space m σ n) (a : (K m)ˣ) :
    (representation m σ n (SuzukiTorusMovingRank.torusHom m a) f).val (weyl m) =
      σ (a : K m) ^ n * f.val (weyl m) := by
  rw [SuzukiPrincipalSeries.representation_apply, weyl_torus]
  have he := covariance m σ n f (torusInBorel m a⁻¹) (weyl m)
  change f.val (SuzukiTorusMovingRank.torusHom m a⁻¹ * weyl m) =
    (character m σ n (torusInBorel m a⁻¹) : k) * f.val (weyl m) at he
  simpa only [character_torus, inv_inv] using he

end Kourovka2135.SuzukiPrincipalSeriesCoordinates
