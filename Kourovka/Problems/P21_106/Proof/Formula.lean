import Kourovka.Problems.P21_106.Statement

/-!
# The counterexample formula in the ordinary language of groups

The formula has the positive prenex form `∃ a b, ∀ g h, ∃ u v, ...`, with
an equality-only conjunctive matrix. Its sole free variable is `x`.
The realization theorem proves the bridge from actual first-order syntax to
the group-theoretic condition used in the counterexample.
-/

namespace Kourovka.P21_106

/-- The inverse-first commutator convention used throughout this problem. -/
def commutator {G : Type*} [Group G] (a b : G) : G := a⁻¹ * b⁻¹ * a * b

/-- The group-theoretic meaning of the counterexample formula. -/
def FormulaCondition {G : Type*} [Group G] (x : G) : Prop :=
  ∃ a b, x = commutator a b ∧ ∀ g h, ∃ u v,
    commutator u a = 1 ∧ commutator v b = 1 ∧
    commutator u b = commutator g h ∧ commutator a v = commutator g h

open FirstOrder.Language

namespace GroupTerm

/-- The identity term. -/
def one {α : Type*} : groupLanguage.Term α :=
  .func GroupFunction.one Fin.elim0

/-- The inverse of a term. -/
def inv {α : Type*} (t : groupLanguage.Term α) : groupLanguage.Term α :=
  .func GroupFunction.inv (fun _ => t)

/-- The product of two terms. -/
def mul {α : Type*} (s t : groupLanguage.Term α) : groupLanguage.Term α :=
  .func GroupFunction.mul ![s, t]

/-- The inverse-first commutator term. -/
def comm {α : Type*} (s t : groupLanguage.Term α) : groupLanguage.Term α :=
  mul (mul (mul (inv s) (inv t)) s) t

@[simp] theorem realize_one {α G : Type*} [Group G] (v : α → G) :
    (one : groupLanguage.Term α).realize v = 1 := rfl

@[simp] theorem realize_inv {α G : Type*} [Group G] (v : α → G)
    (t : groupLanguage.Term α) : (inv t).realize v = (t.realize v)⁻¹ := rfl

@[simp] theorem realize_mul {α G : Type*} [Group G] (v : α → G)
    (s t : groupLanguage.Term α) : (mul s t).realize v = s.realize v * t.realize v := rfl

@[simp] theorem realize_comm {α G : Type*} [Group G] (v : α → G)
    (s t : groupLanguage.Term α) :
    (comm s t).realize v = commutator (s.realize v) (t.realize v) := rfl

end GroupTerm

/-- The equality-only matrix; the bound variables in order are `a,b,g,h,u,v`. -/
def counterexampleMatrix : groupLanguage.BoundedFormula Unit 6 :=
  let x : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inl ())
  let a : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 0)
  let b : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 1)
  let g : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 2)
  let h : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 3)
  let u : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 4)
  let v : groupLanguage.Term (Unit ⊕ Fin 6) := .var (.inr 5)
  x.bdEqual (GroupTerm.comm a b) ⊓
    (GroupTerm.comm u a).bdEqual GroupTerm.one ⊓
    (GroupTerm.comm v b).bdEqual GroupTerm.one ⊓
    (GroupTerm.comm u b).bdEqual (GroupTerm.comm g h) ⊓
    (GroupTerm.comm a v).bdEqual (GroupTerm.comm g h)

/-- A parameter-free positive `∃∃∀∀∃∃` group formula with one free variable. -/
def counterexampleFormula : groupLanguage.Formula Unit :=
  counterexampleMatrix.ex.ex.all.all.ex.ex

@[simp] theorem realize_counterexampleFormula {G : Type*} [Group G] (x : G) :
    counterexampleFormula.Realize (fun _ => x) ↔ FormulaCondition x := by
  simp only [counterexampleFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_all, counterexampleMatrix, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, GroupTerm.realize_comm, GroupTerm.realize_one,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  simp only [Fin.snoc, Fin.coe_ofNat_eq_mod, FormulaCondition, and_assoc]
  constructor
  · rintro ⟨a, b, h⟩
    obtain ⟨u, v, hx, _⟩ := h 1 1
    exact ⟨a, b, hx, fun g h' => by
      obtain ⟨u, v, _, huv⟩ := h g h'
      exact ⟨u, v, huv⟩⟩
  · rintro ⟨a, b, hx, h⟩
    exact ⟨a, b, fun g h' => by
      obtain ⟨u, v, huv⟩ := h g h'
      exact ⟨u, v, hx, huv⟩⟩

end Kourovka.P21_106
