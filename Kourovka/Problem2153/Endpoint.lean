import Kourovka.Problem2153.Simplicity.Concrete
import Kourovka.Problem2153.NormalGeneration.Witnesses
import Kourovka.Problem2153.WilsonModel.ClassTests.Centralizers
import Kourovka.Problem2153.WilsonModel.ClassTests.Products

set_option autoImplicit false
namespace Kourovka.Problem2153.Endpoint
open RootSystem

/-- The three certified involutions as vertices of the entire ambient conjugacy class. -/
def vertexX : InvolutionClass WilsonModel.X := ⟨WilsonModel.X, IsConj.refl _⟩
def vertexY : InvolutionClass WilsonModel.X := ⟨WilsonModel.Y, by
  apply isConj_iff.mpr
  exact ⟨WilsonModel.H⁻¹, by simpa using WilsonModel.Y_eq_conj_X.symm⟩⟩
def vertexA : InvolutionClass WilsonModel.X := ⟨WilsonModel.A, by
  apply isConj_iff.mpr
  exact ⟨WilsonModel.W⁻¹, by simpa using WilsonModel.A_eq_conj_X.symm⟩⟩

/-- A transposition on the whole class, fixing every vertex except the displayed pair. -/
noncomputable def classSwap : Equiv.Perm (InvolutionClass WilsonModel.X) := by
  classical
  exact Equiv.swap vertexX vertexY

/-- The displayed edge really changes from exact order five to exact order seven. -/
theorem changed_edge : vertexA ≠ vertexX ∧
    orderOf (vertexA.val * vertexX.val) = 5 ∧
    orderOf ((classSwap vertexA).val * (classSwap vertexX).val) = 7 := by
  classical
  have h5 : orderOf (vertexA.val * vertexX.val) = 5 :=
    WilsonModel.witness_orders.2.2.2.1
  have h7 : orderOf (vertexA.val * vertexY.val) = 7 :=
    WilsonModel.witness_orders.2.2.2.2
  obtain ⟨hax, hay, _⟩ := witness_ne WilsonModel.witness_orders.2.1 vertexA vertexX vertexY h5 h7
  refine ⟨hax, h5, ?_⟩
  unfold classSwap
  rw [Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_left]
  exact h7

abbrev Coverage : Prop := BruhatCoverage (fun u : U => (u : G))
  (fun h : H => (h : G)) Weyl.rep

/-- Reassociate exact U H W U coverage into the B W B form used for maximality. -/
theorem bwb_of_coverage (hc : Coverage) :
    ∀ g : G, ∃ b₁ ∈ B, ∃ k : Fin 16, ∃ b₂ ∈ B, g = b₁ * Weyl.rep k * b₂ := by
  intro g
  obtain ⟨u, h, k, v, hg⟩ := hc g
  exact ⟨u.val * h.val, B.mul_mem ((show U ≤ B from le_sup_left) u.property)
    ((show H ≤ B from le_sup_right) h.property), k, v.val,
      (show U ≤ B from le_sup_left) v.property, hg⟩

theorem centralizer_test (h : H) (k : Fin 16) :
    Commute WilsonModel.X (h.val * Weyl.rep k) ↔
      Commute WilsonModel.Y (h.val * Weyl.rep k) := by
  obtain ⟨c,d,he⟩ := exists_torus_of_mem_H h.property
  rw [he, witnessX_eq_root, witnessY_eq_root]
  exact (WilsonModel.ClassTests.commute_torus_weyl_uniform 1 c d k).symm

theorem order_three_test (h : H) (k : Fin 16) :
    orderOf (WilsonModel.X * rightConj WilsonModel.X (h.val * Weyl.rep k)) ≠ 3 := by
  obtain ⟨c,d,he⟩ := exists_torus_of_mem_H h.property
  rw [he, witnessX_eq_root]
  exact WilsonModel.ClassTests.product_torus_weyl_order_ne_three 0 c d k

/-- The finite representative checks imply equal centralizers in the whole ambient group. -/
theorem same_centralizer_of_coverage (hc : Coverage) :
    ∀ g : G, Commute WilsonModel.X g ↔ Commute WilsonModel.Y g :=
  same_centralizer_of_bruhat_tests _ _ _ hc _ _
    (fun u => witnessX_commute_U u.property) (fun u => witnessY_commute_U u.property)
    centralizer_test

/-- Order three is absent from every product of two vertices in the entire class. -/
theorem no_order_three_of_coverage (hc : Coverage) :
    ∀ a b : InvolutionClass WilsonModel.X, orderOf (a.val * b.val) ≠ 3 :=
  no_class_product_order_of_bruhat_tests _ _ _ hc _ 3
    (fun u => witnessX_commute_U u.property) order_three_test

/-- Complete whole-class counterexample once the separately constructed coverage is supplied. -/
theorem classSwap_counterexample_of_coverage (hc : Coverage) :
    PreservesColour 2 classSwap ∧ PreservesColour 3 classSwap ∧
      ¬ PreservesAllColours classSwap := by
  classical
  exact swap_counterexample_of_bruhat_tests _ _ _ hc WilsonModel.witness_orders.2.1
    vertexA vertexX vertexY (fun u => witnessX_commute_U u.property)
    (fun u => witnessX_commute_U u.property) (fun u => witnessY_commute_U u.property)
    centralizer_test order_three_test WilsonModel.witness_orders.2.2.2.1
    WilsonModel.witness_orders.2.2.2.2

/-- The public statement is unchanged; all mathematical assumptions other than coverage
have already been discharged for the actual finite ambient group. -/
theorem not_statement_of_coverage (hc : Coverage) : ¬ Statement.{0} := by
  letI : IsSimpleGroup G := ambient_isSimpleGroup_of_coverage (bwb_of_coverage hc)
  intro h
  have he := h G WilsonModel.ambient_nonabelian WilsonModel.X
    WilsonModel.witness_orders.2.1 3 WilsonModel.ambient_two_smallest_primes
  obtain ⟨h2,h3,hn⟩ := classSwap_counterexample_of_coverage hc
  exact hn ((Set.ext_iff.mp he classSwap).mpr ⟨h2,h3⟩)

#print axioms classSwap_counterexample_of_coverage
#print axioms not_statement_of_coverage
end Kourovka.Problem2153.Endpoint
