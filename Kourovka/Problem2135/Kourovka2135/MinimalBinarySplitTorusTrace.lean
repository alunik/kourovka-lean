import Kourovka2135.BinaryNaturalInduction
import Kourovka2135.MinimalBinaryCharacterRecognition
import Kourovka2135.RepresentationExtensionComparison
import Kourovka2135.IrreducibleDerivedKernel
import Kourovka2135.MinimalBinaryCharacterExtension

/-! Trace one at an actual nonidentity split-torus odd-order lift.

The actual native binary quotient is derived from the proved H1 type
uniqueness. Its actual coinduced representation is recognized by degree and
central scalar action, and comparison with the given extension uses the
actual restriction equivalence and determinant one only at the chosen lift.
No trace formula, coinduced irreducibility, or extension is assumed as a new
input to the final terminal-kernel existence statement.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative
open BinaryNaturalInvariantLine NormalJoinRightCosets CoinducedLinearCharacter

/-- An actual extension of a nonlinear kernel representation has trace one
at the specified nonidentity split-torus lift. Only its determinant at this
one lift is assumed to be one. -/
theorem minimal_binary_split_torus_trace_of_derived
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1)
    (α : Representation k G V) (hα : α.comp N.subtype = ρ)
    (u : Fˣ) (hu : u ≠ 1) (g : G)
    (hg : QuotientGroup.mk' R g = j (SLTwo.tor u))
    (hodd : Odd (orderOf g)) (hdet : LinearMap.det (α g) = 1) :
    α.character g = 1 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let ρmin := minimalCenterRepresentation N hN hmin R hR
  let : Representation.IsIrreducible ρmin :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let : Representation.IsIrreducible (ρmin.comp j.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp ρmin j
  have hH1 := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hmin R hR hnonabelian hRΦ hnonspecial
  have hH1' : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (ρmin.comp j.toMonoidHom)) 1) ≠ 0 := by
    rwa [RepresentationGroupEquiv.finrank_cohomology_comp ρmin j 1]
  let e := BinarySLTwoH1TypeUniqueness.naturalEquiv
    (ρmin.comp j.toMonoidHom) f hcard hf hH1'
  let A := centerLinePreimage F N e.toLinearEquiv
  let C := Subgroup.zpowers g
  let H : Subgroup G := N ⊔ C
  let S := Stabilizer N A C
  let t : H := includeC N C (⟨g, Subgroup.mem_zpowers g⟩ : C)
  obtain ⟨χ, hdimσ, hcenterσ, htraceσ, hdetσ⟩ :=
    BinaryNaturalInduction.exists_induced F N hN hmin hnonabelian R hR j e u g
      hg hu hodd (IrreducibleCentralCharacter.centralCharacter ρ)
  let W := Space S χ
  let σ : Representation k H W := induced S χ
  let : FiniteDimensional k W := by dsimp [W]; infer_instance
  have hdimσ' : Module.finrank k W = 2 ^ f := by
    change Module.finrank k W = Nat.card F at hdimσ
    rw [Nat.card_eq_fintype_card, hcard] at hdimσ
    exact hdimσ
  obtain ⟨eσ⟩ := minimal_binary_equiv_of_degree_and_central_action
    N hN hmin hnonabelian R hR hRΦ hnonspecial j f hcard hf
    ρ hderived (σ.comp (includeN N C)) hdimσ' hcenterσ
  let K : Subgroup H := N.subgroupOf H
  let eK : K ≃* N := Subgroup.subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
  let ρK : Representation k K V := ρ.comp eK.toMonoidHom
  let : K.Normal := by dsimp [K]; infer_instance
  let : ρK.IsIrreducible := RepresentationGroupEquiv.isIrreducible_comp ρ eK
  let eσK : Representation.Equiv (σ.comp K.subtype) ρK :=
    Representation.Equiv.mk eσ.toLinearEquiv (by
      intro n
      exact eσ.isIntertwining' (eK n))
  let αH : Representation k H V := α.comp H.subtype
  have hαK : αH.comp K.subtype = ρK := by
    apply MonoidHom.ext
    intro n
    exact DFunLike.congr_fun hα (eK n)
  have hdimρ : Module.finrank k V = 2 ^ f :=
    minimal_binary_nonlinear_character_degree N hN hmin hnonabelian R hR hRΦ
      hnonspecial j f hcard hf ρ hderived
  have htorder : orderOf t = orderOf g :=
    (orderOf_injective H.subtype Subtype.val_injective t).symm
  have htodd : Odd (orderOf t) := by rw [htorder]; exact hodd
  have hcompare := RepresentationExtensionComparison.character_eq_of_odd_orderOf
    K ρK αH hαK σ eσK f hdimρ t htodd hdet hdetσ
  calc
    α.character g = αH.character t := rfl
    _ = σ.character t := hcompare
    _ = 1 := htraceσ

/-- The standard degree-not-one condition supplies the actual nontrivial
derived action; the torus parameter is stated in inverse-quotient coordinates. -/
theorem minimal_binary_split_torus_trace
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hnonlinear : Module.finrank k V ≠ 1)
    (α : Representation k G V) (hα : α.comp N.subtype = ρ)
    (u : Fˣ) (hu : u ≠ 1) (g : G)
    (hg : j.symm (QuotientGroup.mk' R g) = SLTwo.tor u)
    (hodd : Odd (orderOf g)) (hdet : LinearMap.det (α g) = 1) :
    α.character g = 1 := by
  have hg' : QuotientGroup.mk' R g = j (SLTwo.tor u) := by
    simpa only [j.apply_symm_apply] using congrArg j hg
  exact minimal_binary_split_torus_trace_of_derived N hN hmin hnonabelian
    R hR hRΦ hnonspecial j f hcard hf ρ
    (IrreducibleDerivedKernel.exists_commutator_action_ne_one ρ hnonlinear)
    α hα u hu g hg' hodd hdet

/-- In the terminal-kernel case the actual extension is constructed, and that
single extension has trace one at every nonidentity split-torus odd-order lift. -/
theorem minimal_binary_nonlinear_character_extends_split_torus_trace
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (j : SLTwo.SL2 F ≃* (G ⧸ N))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hnonlinear : Module.finrank k V ≠ 1) :
    ∃ α : Representation k G V,
      α.comp N.subtype = ρ ∧
      (∀ g : G, LinearMap.det (α g) = 1) ∧
      ∀ (u : Fˣ), u ≠ 1 → ∀ g : G,
        j.symm (QuotientGroup.mk' N g) = SLTwo.tor u →
        Odd (orderOf g) → α.character g = 1 := by
  have hderived := IrreducibleDerivedKernel.exists_commutator_action_ne_one ρ hnonlinear
  obtain ⟨α, hα, hdet⟩ := minimal_binary_nonlinear_character_extends
    N hN hmin hnonabelian hNΦ hnonspecial j f hcard hf ρ hderived
  refine ⟨α, hα, hdet, ?_⟩
  intro u hu g hg hodd
  exact minimal_binary_split_torus_trace N hN hmin hnonabelian N hN hNΦ hnonspecial
    j f hcard (by omega) ρ hnonlinear α hα u hu g hg hodd (hdet g)

end Kourovka2135
