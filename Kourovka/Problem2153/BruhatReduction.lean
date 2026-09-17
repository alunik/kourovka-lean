import Kourovka.Problem2153.Core

set_option autoImplicit false

namespace Kourovka.Problem2153

universe u v w z

/-- Right conjugation, matching the matrix-model convention `a^g = g⁻¹ a g`. -/
def rightConj {G : Type u} [Group G] (a g : G) : G := g⁻¹ * a * g

theorem rightConj_mul {G : Type u} [Group G] (a g h : G) :
    rightConj a (g * h) = rightConj (rightConj a g) h := by
  simp [rightConj, mul_assoc]

theorem rightConj_mul_elements {G : Type u} [Group G] (a b g : G) :
    rightConj (a * b) g = rightConj a g * rightConj b g := by
  simp [rightConj, mul_assoc]

theorem rightConj_inv_cancel {G : Type u} [Group G] (a g : G) :
    rightConj (rightConj a g) g⁻¹ = a := by
  simp [rightConj, mul_assoc]

theorem rightConj_fixed_iff {G : Type u} [Group G] (a g : G) :
    rightConj a g = a ↔ Commute a g := by
  change g⁻¹ * a * g = a ↔ a * g = g * a
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]

theorem orderOf_rightConj {G : Type u} [Group G] (a g : G) :
    orderOf (rightConj a g) = orderOf a := by
  symm
  apply orderOf_conjugate
  exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConj]⟩

/-- Constructive coverage is a hypothesis. No coverage of an actual matrix group is asserted. -/
def BruhatCoverage {G : Type u} [Group G] {I : Type v} {J : Type w} {K : Type z}
    (U : I → G) (H : J → G) (W : K → G) : Prop :=
  ∀ g : G, ∃ i j k l, g = U i * H j * W k * U l

/-- The right unipotent factor conjugates the entire tested product. -/
theorem product_bruhat_conjugate {G : Type u} [Group G] (x d u h w v : G)
    (hdu : Commute d u) (hxv : Commute x v) :
    x * rightConj d (u * h * w * v) = rightConj (x * rightConj d (h * w)) v := by
  rw [rightConj_mul, rightConj_mul, rightConj_mul,
    (rightConj_fixed_iff d u).mpr hdu, rightConj_mul,
    rightConj_mul_elements, (rightConj_fixed_iff x v).mpr hxv]

/-- Exact product orders reduce to the `H W` representatives. -/
theorem orderOf_product_bruhat {G : Type u} [Group G] (x d u h w v : G)
    (hdu : Commute d u) (hxv : Commute x v) :
    orderOf (x * rightConj d (u * h * w * v)) =
      orderOf (x * rightConj d (h * w)) := by
  rw [product_bruhat_conjugate x d u h w v hdu hxv, orderOf_rightConj]

/-- Membership in the ambient centralizer also reduces to an `H W` representative. -/
theorem commute_bruhat_iff {G : Type u} [Group G] (x u h w v : G)
    (hxu : Commute x u) (hxv : Commute x v) :
    Commute x (u * h * w * v) ↔ Commute x (h * w) := by
  rw [← rightConj_fixed_iff, ← rightConj_fixed_iff,
    rightConj_mul, rightConj_mul, rightConj_mul,
    (rightConj_fixed_iff x u).mpr hxu, rightConj_mul]
  constructor
  · intro heq
    have heq' := congrArg (fun a => rightConj a v⁻¹) heq
    rw [rightConj_inv_cancel] at heq'
    have hfix : rightConj x v⁻¹ = x := by
      have hh := congrArg (fun a => rightConj a v⁻¹) ((rightConj_fixed_iff x v).mpr hxv)
      simpa only [rightConj_inv_cancel] using hh.symm
    rwa [hfix] at heq'
  · intro heq
    rw [heq, (rightConj_fixed_iff x v).mpr hxv]

/-- Every vertex of the full ambient class has a representative with the same tested order. -/
theorem class_order_representative {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) (d x : G)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x (U i))
    (a : InvolutionClass d) :
    ∃ j k, orderOf (x * a.val) = orderOf (x * rightConj d (H j * W k)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp a.property
  obtain ⟨i, j, k, l, hdec⟩ := hCover g⁻¹
  refine ⟨j, k, ?_⟩
  have ha : a.val = rightConj d (U i * H j * W k * U l) := by
    rw [← hdec]
    simpa [rightConj] using hg.symm
  rw [ha]
  exact orderOf_product_bruhat x d (U i) (H j) (W k) (U l) (hdU i) (hxU l)

/-- The same representative works simultaneously for any two elements centralized by U. -/
theorem class_orders_representative {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) (d x y : G)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x (U i))
    (hyU : ∀ i, Commute y (U i)) (a : InvolutionClass d) :
    ∃ j k, orderOf (x * a.val) = orderOf (x * rightConj d (H j * W k)) ∧
      orderOf (y * a.val) = orderOf (y * rightConj d (H j * W k)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp a.property
  obtain ⟨i, j, k, l, hdec⟩ := hCover g⁻¹
  refine ⟨j, k, ?_, ?_⟩
  all_goals
    have ha : a.val = rightConj d (U i * H j * W k * U l) := by
      rw [← hdec]
      simpa [rightConj] using hg.symm
    rw [ha]
  · exact orderOf_product_bruhat x d (U i) (H j) (W k) (U l) (hdU i) (hxU l)
  · exact orderOf_product_bruhat y d (U i) (H j) (W k) (U l) (hdU i) (hyU l)

/-- A certificate on H/W representatives yields whole-class twin neighborhoods. -/
theorem colourTwins_of_bruhat_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) {d : G} (x y : InvolutionClass d) (t : ℕ)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x.val (U i))
    (hyU : ∀ i, Commute y.val (U i))
    (hTest : ∀ j k, orderOf (x.val * rightConj d (H j * W k)) = t ↔
      orderOf (y.val * rightConj d (H j * W k)) = t) : ColourTwins t x y := by
  intro a _ _
  obtain ⟨j, k, hxa, hya⟩ := class_orders_representative U H W hCover d x.val y.val
    hdU hxU hyU a
  rw [hxa, hya]
  exact hTest j k

/-- External-neighborhood certificates need no tests at the two swapped vertices.
Because U fixes x and y, being external is preserved on passing to a representative. -/
theorem colourTwins_of_external_bruhat_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) {d : G} (x y : InvolutionClass d) (t : ℕ)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x.val (U i))
    (hyU : ∀ i, Commute y.val (U i))
    (hTest : ∀ j k, rightConj d (H j * W k) ≠ x.val →
      rightConj d (H j * W k) ≠ y.val →
      (orderOf (x.val * rightConj d (H j * W k)) = t ↔
       orderOf (y.val * rightConj d (H j * W k)) = t)) : ColourTwins t x y := by
  intro a hax hay
  obtain ⟨g, hg⟩ := isConj_iff.mp a.property
  obtain ⟨i, j, k, l, hdec⟩ := hCover g⁻¹
  have ha : a.val = rightConj d (U i * H j * W k * U l) := by
    rw [← hdec]
    simpa [rightConj] using hg.symm
  have ha' : a.val = rightConj (rightConj d (H j * W k)) (U l) := by
    rw [ha, rightConj_mul, rightConj_mul, rightConj_mul,
      (rightConj_fixed_iff d (U i)).mpr (hdU i), rightConj_mul]
  have hx : rightConj d (H j * W k) ≠ x.val := by
    intro heq
    apply hax
    apply Subtype.ext
    rw [ha', heq, (rightConj_fixed_iff x.val (U l)).mpr (hxU l)]
  have hy : rightConj d (H j * W k) ≠ y.val := by
    intro heq
    apply hay
    apply Subtype.ext
    rw [ha', heq, (rightConj_fixed_iff y.val (U l)).mpr (hyU l)]
  rw [ha, orderOf_product_bruhat x.val d _ _ _ _ (hdU i) (hxU l),
    orderOf_product_bruhat y.val d _ _ _ _ (hdU i) (hyU l)]
  exact hTest j k hx hy

/-- Checking the root representative excludes an order everywhere on its whole class. -/
theorem no_class_product_order_of_bruhat_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) (d : G) (t : ℕ)
    (hdU : ∀ i, Commute d (U i))
    (hTest : ∀ j k, orderOf (d * rightConj d (H j * W k)) ≠ t) :
    ∀ a b : InvolutionClass d, orderOf (a.val * b.val) ≠ t := by
  intro a b hab
  obtain ⟨g, hg⟩ := isConj_iff.mp a.property
  have hag : rightConj a.val g = d := by
    rw [← hg]
    simp [rightConj, mul_assoc]
  have hbclass : IsConj d (rightConj b.val g) := by
    apply b.property.trans
    exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConj]⟩
  obtain ⟨j, k, hjk⟩ := class_order_representative U H W hCover d d hdU hdU
    ⟨rightConj b.val g, hbclass⟩
  apply hTest j k
  rw [← hjk]
  have ho := orderOf_rightConj (a.val * b.val) g
  rw [rightConj_mul_elements, hag] at ho
  exact ho.trans hab

/-- H-normalization permits a smaller certificate on root-family/W products.
The index type T may enumerate just the nonzero root parameters. -/
theorem no_class_product_order_of_root_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} {T : Type*}
    (U : I → G) (H : J → G) (W : K → G) (Z : T → G)
    (hCover : BruhatCoverage U H W) (d : G) (t : ℕ)
    (hdU : ∀ i, Commute d (U i))
    (hNormalize : ∀ j, ∃ r, rightConj d (H j) = Z r)
    (hTest : ∀ r k, orderOf (d * rightConj (Z r) (W k)) ≠ t) :
    ∀ a b : InvolutionClass d, orderOf (a.val * b.val) ≠ t := by
  apply no_class_product_order_of_bruhat_tests U H W hCover d t hdU
  intro j k
  obtain ⟨r, hr⟩ := hNormalize j
  rw [rightConj_mul, hr]
  exact hTest r k

/-- Centralizer tests require only H/W representatives once coverage and U-centrality hold. -/
theorem same_centralizer_of_bruhat_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) (x y : G)
    (hxU : ∀ i, Commute x (U i)) (hyU : ∀ i, Commute y (U i))
    (hTest : ∀ j k, Commute x (H j * W k) ↔ Commute y (H j * W k)) :
    ∀ g : G, Commute x g ↔ Commute y g := by
  intro g
  obtain ⟨i, j, k, l, rfl⟩ := hCover g
  rw [commute_bruhat_iff x _ _ _ _ (hxU i) (hxU l),
    commute_bruhat_iff y _ _ _ _ (hyU i) (hyU l)]
  exact hTest j k

/-- Complete swap criterion from finite representative tests and explicit coverage. -/
theorem swap_counterexample_of_bruhat_tests {G : Type u} [Group G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) {d : G} (hd : orderOf d = 2)
    [DecidableEq (InvolutionClass d)] (a x y : InvolutionClass d)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x.val (U i))
    (hyU : ∀ i, Commute y.val (U i))
    (hCentralizerTest : ∀ j k, Commute x.val (H j * W k) ↔ Commute y.val (H j * W k))
    (hThreeTest : ∀ j k, orderOf (d * rightConj d (H j * W k)) ≠ 3)
    (h5 : orderOf (a.val * x.val) = 5) (h7 : orderOf (a.val * y.val) = 7) :
    PreservesColour 2 (Equiv.swap x y) ∧ PreservesColour 3 (Equiv.swap x y) ∧
      ¬ PreservesAllColours (Equiv.swap x y) := by
  apply swap_counterexample hd a x y _ _ h5 h7
  · exact colourTwins_two_of_same_centralizer hd x y
      (same_centralizer_of_bruhat_tests U H W hCover x.val y.val hxU hyU hCentralizerTest)
  · intro b _ _
    have hn := no_class_product_order_of_bruhat_tests U H W hCover d 3 hdU hThreeTest
    exact iff_of_false (hn x b) (hn y b)

/-- Source-statement bridge: finite simple ambient realization is still required. -/
theorem not_statement_of_bruhat_tests {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {I : Type v} {J : Type w} {K : Type z} (U : I → G) (H : J → G) (W : K → G)
    (hCover : BruhatCoverage U H W) {d : G} (hd : orderOf d = 2)
    (hcard2 : 2 ∣ Nat.card G) (hcard3 : 3 ∣ Nat.card G)
    (a x y : InvolutionClass d)
    (hdU : ∀ i, Commute d (U i)) (hxU : ∀ i, Commute x.val (U i))
    (hyU : ∀ i, Commute y.val (U i))
    (hCentralizerTest : ∀ j k, Commute x.val (H j * W k) ↔ Commute y.val (H j * W k))
    (hThreeTest : ∀ j k, orderOf (d * rightConj d (H j * W k)) ≠ 3)
    (h5 : orderOf (a.val * x.val) = 5) (h7 : orderOf (a.val * y.val) = 7) :
    ¬ Statement.{u} := by
  apply not_statement_of_swap hd hcard2 hcard3 a x y _ _ h5 h7
  · exact colourTwins_two_of_same_centralizer hd x y
      (same_centralizer_of_bruhat_tests U H W hCover x.val y.val hxU hyU hCentralizerTest)
  · intro b _ _
    have hn := no_class_product_order_of_bruhat_tests U H W hCover d 3 hdU hThreeTest
    exact iff_of_false (hn x b) (hn y b)

#print axioms product_bruhat_conjugate
#print axioms orderOf_product_bruhat
#print axioms commute_bruhat_iff
#print axioms colourTwins_of_bruhat_tests
#print axioms colourTwins_of_external_bruhat_tests
#print axioms no_class_product_order_of_bruhat_tests
#print axioms no_class_product_order_of_root_tests
#print axioms same_centralizer_of_bruhat_tests
#print axioms swap_counterexample_of_bruhat_tests
#print axioms not_statement_of_bruhat_tests

end Kourovka.Problem2153
