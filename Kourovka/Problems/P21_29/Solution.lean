import Kourovka.Problems.P21_29.Statement
import Kourovka.Problems.P21_29.Proof.Affine
import Kourovka.Problems.P21_29.Proof.Irreducible
import Kourovka.Problems.P21_29.Proof.Certificates.Checks

/-! A negative answer to Problem 21.29, directly in its permutation-action formulation. -/

namespace Kourovka.P21_29

abbrev A := AffineGroup H V

instance : Finite A := by
  let : Fintype (Multiplicative V) := Fintype.ofEquiv V Multiplicative.ofAdd
  exact Finite.of_equiv (Multiplicative V × H) SemidirectProduct.equivProd.symm

/-- The concrete affine action, realized as a subgroup of the symmetric group. -/
def permutationGroup : Subgroup (Equiv.Perm V) := (MulAction.toPermHom A V).range

def toPermutationGroup : A →* permutationGroup := (MulAction.toPermHom A V).rangeRestrict

theorem toPermutationGroup_surjective : Function.Surjective toPermutationGroup := by
  rintro ⟨g, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

@[simp] theorem toPermutationGroup_smul (g : A) (v : V) :
    toPermutationGroup g • v = g • v := rfl

instance : Finite permutationGroup := Finite.of_surjective _ toPermutationGroup_surjective

instance : MulAction.IsPreprimitive A V := by
  let : Representation.IsIrreducible
      (Representation.ofDistribMulAction (ZMod 3) H V) := linear_irreducible
  exact affine_primitive_of_irreducible H V 3

instance : MulAction.IsPreprimitive permutationGroup V := by
  let f : V →ₑ[toPermutationGroup] V :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective
    (f := f) Function.surjective_id

theorem pairStabilizer_iff {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (a b : Ω) :
    TrivialPairStabilizer G a b ↔ ∀ g : G, g • a = a → g • b = b → g = 1 := by
  constructor
  · intro h g ha hb
    have hg : g ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := ⟨ha, hb⟩
    rw [h] at hg
    exact Subgroup.mem_bot.mp hg
  · intro h
    apply le_antisymm ?_ bot_le
    intro g hg
    exact Subgroup.mem_bot.mpr (h g hg.1 hg.2)

theorem affine_pair_iff (x y : V) :
    (∀ g : A, g • x = x → g • y = y → g = 1) ↔
      ∀ h : H, h • (y - x) = y - x → h = 1 := by
  constructor
  · intro hbase h hdiff
    let g : A := ⟨Multiplicative.ofAdd (x - h • x), h⟩
    have hgx : g • x = x := by change (x - h • x) + h • x = x; abel
    have hgy : g • y = y := by
      change (x - h • x) + h • y = y
      rw [smul_sub] at hdiff
      calc
        x - h • x + h • y = x + (h • y - h • x) := by abel
        _ = x + (y - x) := by rw [hdiff]
        _ = y := by abel
    exact congrArg SemidirectProduct.right (hbase g hgx hgy)
  · intro hregular g hgx hgy
    have hdiff : g.right • (y - x) = y - x := by
      change g.left.toAdd + g.right • x = x at hgx
      change g.left.toAdd + g.right • y = y at hgy
      rw [smul_sub]
      calc
        g.right • y - g.right • x =
            (g.left.toAdd + g.right • y) - (g.left.toAdd + g.right • x) := by abel
        _ = y - x := by rw [hgy, hgx]
    have hr : g.right = 1 := hregular g.right hdiff
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change g.left.toAdd = 0
      change g.left.toAdd + g.right • x = x at hgx
      simpa [hr] using hgx
    · exact hr

theorem toPermutationGroup_eq_one_iff (g : A) : toPermutationGroup g = 1 ↔ g = 1 := by
  constructor
  · intro hg
    have hfix (v : V) : g • v = v := by
      have h := congrArg (fun k : permutationGroup => k • v) hg
      simpa only [toPermutationGroup_smul, one_smul] using h
    apply (affine_pair_iff 0 regularVector).mpr ?_ g (hfix 0) (hfix regularVector)
    simpa only [sub_zero] using regularVector_regular
  · rintro rfl
    exact map_one _

theorem pair_iff_regular_difference (a b : V) :
    TrivialPairStabilizer permutationGroup a b ↔
      ∀ h : H, h • (b - a) = b - a → h = 1 := by
  rw [pairStabilizer_iff, ← affine_pair_iff]
  constructor
  · intro h g ha hb
    apply (toPermutationGroup_eq_one_iff g).mp
    exact h (toPermutationGroup g) ha hb
  · intro h g ha hb
    obtain ⟨k, rfl⟩ := toPermutationGroup_surjective g
    exact (toPermutationGroup_eq_one_iff k).mpr (h k ha hb)

theorem has_regular_suborbit :
    ∃ a b : V, TrivialPairStabilizer permutationGroup a b := by
  refine ⟨0, regularVector, (pair_iff_regular_difference _ _).mpr ?_⟩
  simpa only [sub_zero] using regularVector_regular

theorem no_simultaneous_trivial_stabilizers (c : V) :
    ¬(TrivialPairStabilizer permutationGroup 0 c ∧
      TrivialPairStabilizer permutationGroup hole c) := by
  rintro ⟨h0, hw⟩
  have h0' := (pair_iff_regular_difference _ _).mp h0
  have hw' := (pair_iff_regular_difference _ _).mp hw
  rcases no_simultaneous_regular c with ⟨g, hne, hfix⟩ | ⟨g, hne, hfix⟩
  · exact hne (h0' g (by simpa only [sub_zero] using hfix))
  · exact hne (hw' g hfix)

/-- The notebook question is false, witnessed by this degree-19,683 action. -/
theorem not_notebookStatement : ¬NotebookStatement := by
  intro h
  obtain ⟨c, hc⟩ := h V permutationGroup inferInstance inferInstance
    has_regular_suborbit 0 hole
  exact no_simultaneous_trivial_stabilizers c hc

end Kourovka.P21_29
