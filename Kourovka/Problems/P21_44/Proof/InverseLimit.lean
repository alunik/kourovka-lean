import Kourovka.Problems.P21_44.Proof.Wreath
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Constructions

/-! # The full iterated alternating wreath group

The ambient group is the compatible-sequence subgroup of the product of its
finite wreath quotients, equipped with the induced product topology.
-/

namespace Kourovka.P21_44

@[reducible] private def tower : ℕ → Σ G : Type, Group G
  | 0 => ⟨PUnit, inferInstance⟩
  | n + 1 =>
    letI := (tower n).2
    ⟨Wreath (tower n).1, inferInstance⟩

/-- Automorphisms of the finite rooted tree of height `n` with alternating
local permutations. -/
abbrev Level (n : ℕ) : Type := (tower n).1
instance (n : ℕ) : Group (tower n).1 := (tower n).2

instance : Subsingleton (Level 0) := inferInstanceAs (Subsingleton PUnit)

/-- Forget the last level of the finite rooted tree. -/
def levelProj : (n : ℕ) → Level (n + 1) →* Level n
  | 0 => 1
  | n + 1 => Wreath.map (levelProj n)

/-- The finite-level directed generators. -/
def levelA : (n : ℕ) → Level n
  | 0 => 1
  | n + 1 => Wreath.genA (levelA n)
def levelB : (n : ℕ) → Level n
  | 0 => 1
  | n + 1 => Wreath.genB (levelB n)

@[simp] theorem levelProj_levelA (n : ℕ) : levelProj n (levelA (n+1)) = levelA n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Wreath.map (levelProj n) (Wreath.genA (levelA (n+1))) = Wreath.genA (levelA n)
    rw [Wreath.map_genA, ih]
@[simp] theorem levelProj_levelB (n : ℕ) : levelProj n (levelB (n+1)) = levelB n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Wreath.map (levelProj n) (Wreath.genB (levelB (n+1))) = Wreath.genB (levelB n)
    rw [Wreath.map_genB, ih]

@[simp] theorem levelA_cube (n : ℕ) : levelA n ^ 3 = 1 := by
  induction n with
  | zero => simp [levelA]
  | succ n ih => exact Wreath.genA_cube _ ih
@[simp] theorem levelB_cube (n : ℕ) : levelB n ^ 3 = 1 := by
  induction n with
  | zero => simp [levelB]
  | succ n ih => exact Wreath.genB_cube _ ih

/-- The inverse limit, expressed concretely as compatible finite actions. -/
def compatibleSubgroup : Subgroup (∀ n, Level n) where
  carrier := {g | ∀ n, levelProj n (g (n+1)) = g n}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh n; simp only [Pi.mul_apply, map_mul]; rw [hg n, hh n]
  inv_mem' := by intro g hg n; simp only [Pi.inv_apply, map_inv]; rw [hg n]

abbrev AutTree := compatibleSubgroup

/-- Restriction to a finite tree. -/
def levelEval (n : ℕ) : AutTree →* Level n :=
  (Pi.evalMonoidHom (fun n => Level n) n).comp compatibleSubgroup.subtype

@[simp] theorem levelEval_apply (n : ℕ) (g : AutTree) : levelEval n g = g.val n := rfl

/-- The first directed automorphism. -/
def a : AutTree := ⟨levelA, levelProj_levelA⟩
/-- The second directed automorphism. -/
def b : AutTree := ⟨levelB, levelProj_levelB⟩

@[simp] theorem eval_a (n : ℕ) : levelEval n a = levelA n := rfl
@[simp] theorem eval_b (n : ℕ) : levelEval n b = levelB n := rfl
@[simp] theorem a_cube : a ^ 3 = 1 := by apply Subtype.ext; funext n; exact levelA_cube n
@[simp] theorem b_cube : b ^ 3 = 1 := by apply Subtype.ext; funext n; exact levelB_cube n

/-- The root permutation of an infinite compatible automorphism. -/
def root (g : AutTree) : A5 := (g.val 1 : Wreath (Level 0)).right

/-- The action on the subtree rooted at `i`. -/
def treeSection (g : AutTree) (i : Alphabet) : AutTree :=
  ⟨fun n => (g.val (n+1) : Wreath (Level n)).left i, by
    intro n
    exact congrArg (fun x : Wreath (Level n) => x.left i) (g.property (n+1))⟩

@[simp] theorem section_eval (g : AutTree) (i : Alphabet) (n : ℕ) :
    levelEval n (treeSection g i) = (g.val (n+1) : Wreath (Level n)).left i := rfl

theorem level_root (g : AutTree) (n : ℕ) :
    (g.val (n+1) : Wreath (Level n)).right = root g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (fun x : Wreath (Level n) => x.right) (g.property (n+1))).trans ih

/-- Faithful decomposition into the root permutation and the five sections. -/
def decompose : AutTree →* Wreath AutTree where
  toFun g := ⟨treeSection g, root g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext i; apply Subtype.ext; funext n; rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext i; apply Subtype.ext; funext n
      change (g.val (n+1) * h.val (n+1) : Wreath (Level n)).left i =
        (g.val (n+1)).left i * (h.val (n+1)).left ((root g).val⁻¹ i)
      rw [Wreath.mul_left_apply, level_root]
    · rfl

theorem decompose_injective : Function.Injective decompose := by
  intro g h heq
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    apply SemidirectProduct.ext
    · funext i
      exact congrArg (fun x : Wreath AutTree => x.left i |>.val n) heq
    · exact (level_root g n).trans ((congrArg SemidirectProduct.right heq).trans (level_root h n).symm)

@[simp] theorem decompose_a : decompose a = Wreath.genA a := by
  apply SemidirectProduct.ext
  · funext i; apply Subtype.ext; funext n
    change (Wreath.genA (levelA n)).left i = ((Pi.mulSingle 3 a : Alphabet → AutTree) i).val n
    by_cases hi : i = 3 <;> simp [hi, a]
  · rfl
@[simp] theorem decompose_b : decompose b = Wreath.genB b := by
  apply SemidirectProduct.ext
  · funext i; apply Subtype.ext; funext n
    change (Wreath.genB (levelB n)).left i = ((Pi.mulSingle 0 b : Alphabet → AutTree) i).val n
    by_cases hi : i = 0 <;> simp [hi, b]
  · rfl

/-- Assemble compatible sections with an arbitrary alternating root action. -/
def assemble (x : Wreath AutTree) : AutTree :=
  ⟨fun n => match n with
    | 0 => 1
    | n + 1 => ⟨fun i => (x.left i).val n, x.right⟩, by
    intro n
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      apply SemidirectProduct.ext
      · funext i; exact (x.left i).property n
      · rfl⟩

@[simp] theorem decompose_assemble (x : Wreath AutTree) : decompose (assemble x) = x := by
  apply SemidirectProduct.ext
  · funext i; apply Subtype.ext; funext n; rfl
  · rfl

/-- Self-similar identification of the inverse limit with one further wreath
layer. Its multiplication is the inverse-reindexing convention of `Wreath`. -/
noncomputable def decomposeEquiv : AutTree ≃* Wreath AutTree :=
  MulEquiv.ofBijective decompose ⟨decompose_injective, fun x => ⟨assemble x, decompose_assemble x⟩⟩

/-- Every finite tree quotient is a finite group. -/
instance levelFinite : (n : ℕ) → Finite (Level n)
  | 0 => inferInstanceAs (Finite PUnit)
  | n + 1 =>
    letI := levelFinite n
    Finite.of_equiv ((Alphabet → Level n) × A5) SemidirectProduct.equivProd.symm

/-- Finite quotients carry their discrete topology. -/
instance (n : ℕ) : TopologicalSpace (Level n) := ⊥
instance (n : ℕ) : DiscreteTopology (Level n) := ⟨rfl⟩

/-- Equality at a deeper level implies equality at every shallower level. -/
theorem eval_eq_of_le (g h : AutTree) {n m : ℕ} (hnm : n ≤ m) :
    g.val m = h.val m → g.val n = h.val n := by
  induction m, hnm using Nat.le_induction with
  | base => exact id
  | succ m _ ih =>
    intro heq
    apply ih
    rw [← g.property m, ← h.property m, heq]

/-- A subgroup surjecting onto every finite tree quotient is dense in the
inverse-limit topology. -/
theorem dense_of_surjective_levels (H : Subgroup AutTree)
    (hH : ∀ n, Function.Surjective ((levelEval n).comp H.subtype)) :
    Dense (H : Set AutTree) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨g, hg⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hV g.val hg
  obtain ⟨h, hh⟩ := hH (I.sup id) (g.val (I.sup id))
  refine ⟨h.val, ?_, h.property⟩
  apply hsub
  intro i hi
  have hie : h.val.val i = g.val i :=
    eval_eq_of_le h.val g (Finset.le_sup (f := id) hi) hh
  rw [hie]
  exact (hu i hi).2

end Kourovka.P21_44
