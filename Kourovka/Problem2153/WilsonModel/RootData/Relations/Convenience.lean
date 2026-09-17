import Kourovka.Problem2153.WilsonModel.RootData.Relations.Structured
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations

private theorem inverse_lhs_formula : inverse_lhs = fun k =>
    [Atom.root (inverseData k).i (inverseData k).a] ++ coordinateWord (inverseData k).coords := by
  decide +kernel
private theorem inverse_rhs_formula : inverse_rhs = fun _ => [] := by decide +kernel
private theorem product_lhs_formula : product_lhs = fun k =>
    [Atom.root (productData k).i (productData k).a,
     Atom.root (productData k).i (productData k).b] := by decide +kernel
private theorem product_rhs_formula : product_rhs = fun k =>
    coordinateWord (productData k).coords := by decide +kernel
private theorem commutator_lhs_formula : commutator_lhs = fun k =>
    [Atom.root (commutatorData k).i (commutatorData k).a,
     Atom.root (commutatorData k).j (commutatorData k).b] := by decide +kernel
private theorem commutator_rhs_formula : commutator_rhs = fun k =>
    [Atom.root (commutatorData k).j (commutatorData k).b,
     Atom.root (commutatorData k).i (commutatorData k).a] ++
       coordinateWord (commutatorData k).coords := by decide +kernel

def weylAtom (b : Bool) : Atom := if b then Atom.sigma else Atom.rho
private theorem weyl_lhs_formula : weyl_lhs = fun k =>
    [weylAtom (weylData k).sigma, Atom.root (weylData k).i (weylData k).a,
     weylAtom (weylData k).sigma] := by decide +kernel
private theorem weyl_rhs_formula : weyl_rhs = fun k => coordinateWord (weylData k).coords := by
  decide +kernel

theorem atomGroup_weylAtom (b : Bool) : atomGroup (weylAtom b) = weylGenerator b := by
  cases b <;> rfl

theorem inverse_convenient (k : Fin 12)
    (h : wordGroup (inverse_lhs k) = wordGroup (inverse_rhs k)) :
    (RootSystem.root (inverseData k).i (inverseData k).a)⁻¹ =
      coordinateGroup (inverseData k).coords := by
  rw [inverse_lhs_formula, inverse_rhs_formula] at h
  simp only [wordGroup_append, wordGroup_cons, wordGroup_nil, mul_one,
    atomGroup, coordinateWord_group] at h
  have h' := congrArg ((RootSystem.root (inverseData k).i (inverseData k).a)⁻¹ * ·) h
  simpa [mul_assoc] using h'.symm

theorem product_convenient (k : Fin 84)
    (h : wordGroup (product_lhs k) = wordGroup (product_rhs k)) :
    RootSystem.root (productData k).i (productData k).a *
      RootSystem.root (productData k).i (productData k).b =
        coordinateGroup (productData k).coords := by
  rw [product_lhs_formula, product_rhs_formula] at h
  simpa only [wordGroup_cons, wordGroup_nil, mul_one, atomGroup, coordinateWord_group] using h

theorem commutator_convenient (k : Fin 90)
    (h : wordGroup (commutator_lhs k) = wordGroup (commutator_rhs k)) :
    (RootSystem.root (commutatorData k).i (commutatorData k).a)⁻¹ *
      (RootSystem.root (commutatorData k).j (commutatorData k).b)⁻¹ *
        RootSystem.root (commutatorData k).i (commutatorData k).a *
          RootSystem.root (commutatorData k).j (commutatorData k).b =
            coordinateGroup (commutatorData k).coords := by
  rw [commutator_lhs_formula, commutator_rhs_formula] at h
  simp only [wordGroup_append, wordGroup_cons, wordGroup_nil, mul_one,
    atomGroup, coordinateWord_group] at h
  let a := RootSystem.root (commutatorData k).i (commutatorData k).a
  let b := RootSystem.root (commutatorData k).j (commutatorData k).b
  change a⁻¹ * b⁻¹ * a * b = _
  change a * b = b * a * coordinateGroup (commutatorData k).coords at h
  calc a⁻¹ * b⁻¹ * a * b = (a⁻¹ * b⁻¹) * (a * b) := by simp [mul_assoc]
       _ = (a⁻¹ * b⁻¹) * (b * a * coordinateGroup (commutatorData k).coords) := by rw [h]
       _ = coordinateGroup (commutatorData k).coords := by simp [mul_assoc]

theorem weyl_convenient (k : Fin 21)
    (h : wordGroup (weyl_lhs k) = wordGroup (weyl_rhs k)) :
    rightConj (RootSystem.root (weylData k).i (weylData k).a)
      (weylGenerator (weylData k).sigma) = coordinateGroup (weylData k).coords := by
  rw [weyl_lhs_formula, weyl_rhs_formula] at h
  simp only [wordGroup_cons, wordGroup_nil, mul_one, coordinateWord_group] at h
  simp only [atomGroup_weylAtom] at h
  change weylGenerator (weylData k).sigma *
    (RootSystem.root (weylData k).i (weylData k).a * weylGenerator (weylData k).sigma) = _ at h
  simpa only [rightConj, weylGenerator_inv, mul_assoc] using h

end Kourovka.Problem2153.WilsonModel.RootData.Relations
