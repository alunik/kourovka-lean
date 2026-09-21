import Kourovka2135.PGroupInvariantFunctional
import Kourovka2135.SuzukiNaturalBorelFiltration
import Kourovka2135.EmbeddedFieldEigenvector
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Actual Borel characters and eigenfunctionals for the concrete Suzuki
group. The root group is genuinely nonabelian; its fixed functional is
obtained by the finite p-group theorem. A split finite-field annihilator
then gives a torus eigenfunctional, and actual root-times-torus coordinates
give covariance under the entire Borel. No irreducible-module
classification or finite-dimensionality premise is used. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SuzukiPrincipalSeriesBorel

open BenderSuzuki.MatrixGroups SuzukiGeometry SuzukiNaturalBorelFiltration
open scoped MatrixGroups

variable (m : ℕ)

/-- The actual root subgroup is a binary group, by its proved cardinality. -/
theorem root_isPGroup : IsPGroup 2 (root m) := by
  apply IsPGroup.of_card (n := (2 * m + 1) * 2)
  rw [card_root]
  exact (pow_mul 2 (2 * m + 1) 2).symm

/-- The first non-extreme diagonal entry, followed by the Tits automorphism,
recovers the genuine torus parameter. -/
def parameter : borel m →* (K m)ˣ :=
  (Units.map (tits m).toMonoidHom).comp (diagonalCharacter m 1)

@[simp] theorem parameter_root (r : root m) :
    parameter m (rootInBorel m r) = 1 := by
  simp only [parameter, MonoidHom.comp_apply, diagonalCharacter_root, map_one]

@[simp] theorem parameter_torus (a : (K m)ˣ) :
    parameter m (torusInBorel m a) = a := by
  apply Units.ext
  change tits m (diagonalCharacter m 1 (torusInBorel m a) : K m) = (a : K m)
  rw [diagonalCharacter_torus]
  exact SuzukiTorusMovingRank.tits_middle m (a : K m)

variable {k : Type u} [Field k] (σ : K m →+* k)

/-- The negative-exponent character matching forward functional covariance. -/
def character (n : ℕ) : borel m →* kˣ :=
  (powMonoidHom n).comp
    (invMonoidHom.comp ((Units.map σ.toMonoidHom).comp (parameter m)))

@[simp] theorem character_root (n : ℕ) (r : root m) :
    character m σ n (rootInBorel m r) = 1 := by
  simp [character]

@[simp] theorem character_torus (n : ℕ) (a : (K m)ˣ) :
    (character m σ n (torusInBorel m a) : k) = σ ((a⁻¹ : (K m)ˣ) : K m) ^ n := by
  simp [character]

variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (G m) V)

/-- Native invariant linear functionals for the entire actual root group. -/
def invariantDual : Submodule k (Module.Dual k V) where
  carrier := {ell | ∀ (r : root m) (v : V), ell (ρ (r : G m) v) = ell v}
  zero_mem' := by intro r v; rfl
  add_mem' := by
    intro ell ell' hell hell' r v
    change ell (ρ (r : G m) v) + ell' (ρ (r : G m) v) = ell v + ell' v
    rw [hell, hell']
  smul_mem' := by
    intro c ell hell r v
    change c * ell (ρ (r : G m) v) = c * ell v
    rw [hell]

theorem torus_conjugate_mem_root (a : (K m)ˣ) (r : root m) :
    SuzukiTorusMovingRank.torusHom m a * (r : G m) *
      (SuzukiTorusMovingRank.torusHom m a)⁻¹ ∈ root m := by
  have hn := torusGL_le_normalizer_rootGL m
    (Subgroup.subset_closure (show ∃ u : (K m)ˣ, SuzukiTorusGL m a = SuzukiTorusGL m u
      from ⟨a, rfl⟩))
  exact (Subgroup.mem_normalizer_iff.mp hn ((r : G m) : GL (Fin 4) (K m))).mp r.property

/-- Forward precomposition on root-invariant functionals. -/
def torusOperator (a : (K m)ˣ) : Module.End k (invariantDual m ρ) where
  toFun ell := ⟨ell.val.comp (ρ (SuzukiTorusMovingRank.torusHom m a)), by
    intro r v
    let t := SuzukiTorusMovingRank.torusHom m a
    let r' : root m := ⟨t * (r : G m) * t⁻¹, torus_conjugate_mem_root m a r⟩
    have he : t * (r : G m) = (r' : G m) * t := by dsimp [r']; group
    change ell.val (ρ t (ρ (r : G m) v)) = ell.val (ρ t v)
    calc
      _ = ell.val (ρ (t * (r : G m)) v) :=
        congrArg (fun T : Module.End k V => ell.val (T v)) (ρ.map_mul _ _).symm
      _ = ell.val (ρ ((r' : G m) * t) v) := by rw [he]
      _ = ell.val (ρ (r' : G m) (ρ t v)) :=
        congrArg (fun T : Module.End k V => ell.val (T v)) (ρ.map_mul _ _)
      _ = ell.val (ρ t v) := ell.property r' _⟩
  map_add' ell ell' := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl
  map_smul' c ell := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl

@[simp] theorem torusOperator_apply (a : (K m)ˣ) (ell : invariantDual m ρ) (v : V) :
    (torusOperator m ρ a ell).val v =
      ell.val (ρ (SuzukiTorusMovingRank.torusHom m a) v) := rfl

theorem torusOperator_one : torusOperator m ρ 1 = 1 := by
  apply LinearMap.ext
  intro ell
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ell.val (ρ (SuzukiTorusMovingRank.torusHom m 1) v) = ell.val v
  rw [map_one, map_one]
  rfl

theorem torusOperator_mul (a b : (K m)ˣ) :
    torusOperator m ρ (a * b) = torusOperator m ρ a * torusOperator m ρ b := by
  apply LinearMap.ext
  intro ell
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ell.val (ρ (SuzukiTorusMovingRank.torusHom m (a * b)) v) =
    ell.val (ρ (SuzukiTorusMovingRank.torusHom m b)
      (ρ (SuzukiTorusMovingRank.torusHom m a) v))
  rw [mul_comm a b, map_mul, map_mul]
  rfl

def torusAction : Representation k (K m)ˣ (invariantDual m ρ) where
  toFun := torusOperator m ρ
  map_one' := torusOperator_one m ρ
  map_mul' := torusOperator_mul m ρ

theorem torusAction_pow_card_sub_one [Fintype (K m)] (a : (K m)ˣ) :
    torusAction m ρ a ^ (Fintype.card (K m) - 1) = 1 := by
  classical
  have ha : a ^ (Fintype.card (K m) - 1) = 1 := by
    rw [← Fintype.card_units]
    exact pow_card_eq_one
  rw [← map_pow, ha, map_one]

variable [CharP k 2] [Nontrivial V]

theorem invariantDual_ne_bot : invariantDual m ρ ≠ ⊥ := by
  obtain ⟨ell, hell, hfix⟩ := PGroupInvariantFunctional.exists_nonzero_invariant_functional
    (ρ.comp (root m).subtype) (root_isPGroup m)
  intro he
  have hm : ell ∈ invariantDual m ρ := hfix
  rw [he, Submodule.mem_bot] at hm
  exact hell hm

/-- A nonzero root-fixed torus eigenfunctional with an actual finite-field exponent. -/
theorem exists_root_torus_functional :
    ∃ n : ℕ, n < Nat.card (K m) - 1 ∧
      ∃ ell : Module.Dual k V, ell ≠ 0 ∧
        (∀ (r : root m) (v : V), ell (ρ (r : G m) v) = ell v) ∧
        (∀ (a : (K m)ˣ) (v : V),
          ell (ρ (SuzukiTorusMovingRank.torusHom m a) v) =
            σ ((a⁻¹ : (K m)ˣ) : K m) ^ n * ell v) := by
  classical
  let : Fintype (K m) := Fintype.ofFinite (K m)
  let : Nontrivial (invariantDual m ρ) :=
    Submodule.nontrivial_iff_ne_bot.mpr (invariantDual_ne_bot m ρ)
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := (K m)ˣ)
  have hord : orderOf r = Fintype.card (K m) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨b, ell, hell, he⟩ :=
    EmbeddedFieldEigenvector.exists_unit_eigenvector_of_pow_card_sub_one
      (V := ↥(invariantDual m ρ)) σ (torusAction m ρ r)
      (torusAction_pow_card_sub_one m ρ r)
  obtain ⟨n, hn, hnb⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (hr b⁻¹))
  have hn' : n < Nat.card (K m) - 1 := by
    simpa only [hord, Nat.card_eq_fintype_card] using Finset.mem_range.mp hn
  have hb : b = (r⁻¹) ^ n := by rw [inv_pow, hnb, inv_inv]
  have hve : Module.End.HasEigenvector (torusAction m ρ r) (σ (b : K m)) ell :=
    ⟨Module.End.mem_eigenspace_iff.mpr he, hell⟩
  refine ⟨n, hn', ell.val, ?_, ell.property, ?_⟩
  · intro h
    exact hell (Subtype.ext h)
  · intro a v
    obtain ⟨j, _, hja⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp (hr a))
    have hbj : b ^ j = (a⁻¹) ^ n := by
      calc
        b ^ j = ((r⁻¹) ^ n) ^ j := by rw [hb]
        _ = ((r⁻¹) ^ j) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n j]
        _ = (a⁻¹) ^ n := by rw [inv_pow, hja]
    have hs : σ (b : K m) ^ j = σ ((a⁻¹ : (K m)ˣ) : K m) ^ n := by
      calc
        σ (b : K m) ^ j = σ ((b ^ j : (K m)ˣ) : K m) := by simp
        _ = σ (((a⁻¹) ^ n : (K m)ˣ) : K m) := congrArg (fun x : (K m)ˣ => σ (x : K m)) hbj
        _ = _ := by simp
    have hp := hve.pow_apply j
    rw [← map_pow, hja, hs] at hp
    exact congrArg (fun l : invariantDual m ρ => l.val v) hp

/-- Every nonzero module has a nonzero character functional for the entire
actual Borel. Irreducibility is needed separately to obtain an embedding. -/
theorem exists_borel_character :
    ∃ n : ℕ, n < Nat.card (K m) - 1 ∧
      ∃ ell : Module.Dual k V, ell ≠ 0 ∧
        ∀ (b : borel m) (v : V),
          ell (ρ (b : G m) v) = (character m σ n b : k) * ell v := by
  obtain ⟨n, hn, ell, hell, hroot, htor⟩ := exists_root_torus_functional m σ ρ
  refine ⟨n, hn, ell, hell, ?_⟩
  intro b v
  obtain ⟨a, c, u, hu⟩ := exists_root_torus m b
  let r : root m :=
    ⟨⟨SuzukiRootGL m a c, Subgroup.subset_closure (Or.inl ⟨a, c, rfl⟩)⟩,
      Subgroup.subset_closure ⟨a, c, rfl⟩⟩
  have hb : b = rootInBorel m r * torusInBorel m u := by
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  rw [hb]
  change ell (ρ ((r : G m) * SuzukiTorusMovingRank.torusHom m u) v) = _
  rw [map_mul, Module.End.mul_apply, hroot, htor]
  simp only [map_mul, character_root, one_mul, character_torus]

end Kourovka2135.SuzukiPrincipalSeriesBorel
