import Kourovka.Problem2153.RootRelations.Data
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Checked

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.RootRelations
open WilsonModel.RootData.Relations

theorem coordinateGroup_zero : coordinateGroup (fun _ => 0) = 1 := by
  simp [coordinateGroup]

theorem coordinateGroup_single (i : Fin 12) (a : Fin 8) :
    coordinateGroup (singleCoordinate i a) = root i a := by
  fin_cases i <;> simp [coordinateGroup, singleCoordinate, List.ofFn_succ]

theorem rightConj_listprod (l : List G) (h : G) :
    rightConj l.prod h = (l.map (fun g => rightConj g h)).prod := by
  induction l with
  | nil => simp [rightConj]
  | cons g l ih => simp only [List.prod_cons, List.map_cons, rightConj_mul_elements, ih]

theorem coordinateGroup_conj (v : Coordinates) (c d : Fin 7) :
    rightConj (coordinateGroup v) (torus c d) =
      coordinateGroup (transportCoordinates v (c,d)) := by
  simp only [coordinateGroup, rightConj_listprod, List.map_ofFn, Function.comp_def, root_conj_torus]
  rfl

theorem rightConj_inverse (g h : G) : rightConj g⁻¹ h = (rightConj g h)⁻¹ := by
  simp [rightConj, mul_inv_rev, mul_assoc]

/-- The representative inverse certificates cover every field parameter. -/
theorem root_inverse (i : Fin 12) (a : Fin 8) :
    (root i a)⁻¹ = coordinateGroup (inverseCoordinates i a) := by
  by_cases ha : a = 0
  · subst a
    simp [inverseCoordinates, coordinateGroup_zero]
  let k := inverseSelector i a
  obtain ⟨hki,hka⟩ := inverse_selector_check i a ha
  have ht := congrArg (fun g => rightConj g (torus k.2.1 k.2.2)) (inverse_identity k.1)
  rw [rightConj_inverse, root_conj_torus, coordinateGroup_conj] at ht
  simp only [inverseCoordinates, ha, ite_false]
  change (root i a)⁻¹ = coordinateGroup (transportCoordinates (inverseData k.1).coords k.2)
  simpa only [k, hki, hka] using ht

/-- The representative product certificates cover every pair of parameters. -/
theorem root_product (i : Fin 12) (a b : Fin 8) :
    root i a * root i b = coordinateGroup (productCoordinates i a b) := by
  by_cases ha : a = 0
  · subst a
    simp [productCoordinates, coordinateGroup_single]
  by_cases hb : b = 0
  · subst b
    simp [productCoordinates, ha, coordinateGroup_single]
  let k := productSelector i a b
  obtain ⟨hki,hka,hkb⟩ := product_selector_check i a b ha hb
  have ht := congrArg (fun g => rightConj g (torus k.2.1 k.2.2)) (product_identity k.1)
  rw [rightConj_mul_elements, root_conj_torus, root_conj_torus, coordinateGroup_conj] at ht
  simp only [productCoordinates, ha, hb, ite_false]
  change root i a * root i b =
    coordinateGroup (transportCoordinates (productData k.1).coords k.2)
  simpa only [k, hki, hka, hkb] using ht

/-- Every ordered commutator is a product of strictly later roots. -/
theorem root_commutator (i j : Fin 12) (a b : Fin 8) (hij : i < j) :
    (root i a)⁻¹ * (root j b)⁻¹ * root i a * root j b =
      coordinateGroup (commutatorCoordinates i j a b) := by
  by_cases ha : a = 0
  · subst a
    simp [commutatorCoordinates, coordinateGroup_zero]
  by_cases hb : b = 0
  · subst b
    simp [commutatorCoordinates, coordinateGroup_zero]
  let k := commutatorSelector i j a b
  obtain ⟨hki,hkj,hka,hkb⟩ := commutator_selector_check i j a b hij ha hb
  have ht := congrArg (fun g => rightConj g (torus k.2.1 k.2.2)) (commutator_identity k.1)
  simp only [rightConj_mul_elements, rightConj_inverse, root_conj_torus,
    coordinateGroup_conj] at ht
  simp only [commutatorCoordinates, ha, hb, or_self, ite_false]
  change (root i a)⁻¹ * (root j b)⁻¹ * root i a * root j b =
    coordinateGroup (transportCoordinates (commutatorData k.1).coords k.2)
  simpa only [k, hki, hkj, hka, hkb] using ht

end Kourovka.Problem2153.RootSystem.RootRelations
