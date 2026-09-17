import Kourovka.Problem2153.TorusAction
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Transport

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.RootRelations
open WilsonModel.RootData.Relations

def transportCoordinates (v : Coordinates) (h : Fin 7 × Fin 7) : Coordinates :=
  fun i => parameterAction i h.1 h.2 (v i)

def inverseSelector (i : Fin 12) (a : Fin 8) : Transport 12 :=
  (inverseTransport i a).getD (0,(0,0))

def productSelector (i : Fin 12) (a b : Fin 8) : Transport 84 :=
  (productTransport i a b).getD (0,(0,0))

def commutatorSelector (i j : Fin 12) (a b : Fin 8) : Transport 90 :=
  (commutatorTransport i j a b).getD (0,(0,0))

theorem inverse_selector_check : ∀ i : Fin 12, ∀ a : Fin 8, a ≠ 0 →
    let k := inverseSelector i a
    (inverseData k.1).i = i ∧
      parameterAction i k.2.1 k.2.2 (inverseData k.1).a = a := by
  decide +kernel

theorem product_selector_check : ∀ i : Fin 12, ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 →
    let k := productSelector i a b
    (productData k.1).i = i ∧
      parameterAction i k.2.1 k.2.2 (productData k.1).a = a ∧
      parameterAction i k.2.1 k.2.2 (productData k.1).b = b := by
  decide +kernel

theorem commutator_selector_check : ∀ i j : Fin 12, ∀ a b : Fin 8,
    i < j → a ≠ 0 → b ≠ 0 →
    let k := commutatorSelector i j a b
    (commutatorData k.1).i = i ∧ (commutatorData k.1).j = j ∧
      parameterAction i k.2.1 k.2.2 (commutatorData k.1).a = a ∧
      parameterAction j k.2.1 k.2.2 (commutatorData k.1).b = b := by
  decide +kernel

def singleCoordinate (i : Fin 12) (a : Fin 8) : Coordinates := fun j => if j = i then a else 0

def inverseCoordinates (i : Fin 12) (a : Fin 8) : Coordinates :=
  if a = 0 then fun _ => 0 else
    let k := inverseSelector i a
    transportCoordinates (inverseData k.1).coords k.2

def productCoordinates (i : Fin 12) (a b : Fin 8) : Coordinates :=
  if a = 0 then singleCoordinate i b else
  if b = 0 then singleCoordinate i a else
    let k := productSelector i a b
    transportCoordinates (productData k.1).coords k.2

def commutatorCoordinates (i j : Fin 12) (a b : Fin 8) : Coordinates :=
  if a = 0 ∨ b = 0 then fun _ => 0 else
    let k := commutatorSelector i j a b
    transportCoordinates (commutatorData k.1).coords k.2

theorem inverse_representative_support : ∀ k : Fin 12, ∀ j : Fin 12,
    j < (inverseData k).i → (inverseData k).coords j = 0 := by decide +kernel

theorem product_representative_support : ∀ k : Fin 84, ∀ j : Fin 12,
    j < (productData k).i → (productData k).coords j = 0 := by decide +kernel

theorem commutator_representative_support : ∀ k : Fin 90, ∀ j : Fin 12,
    j ≤ (commutatorData k).j → (commutatorData k).coords j = 0 := by decide +kernel

/-- Torus transport preserves the support of each representative identity. -/
theorem inverse_support (i j : Fin 12) (a : Fin 8) (hji : j < i) :
    inverseCoordinates i a j = 0 := by
  by_cases ha : a = 0
  · simp [inverseCoordinates, ha]
  obtain ⟨hi,_⟩ := inverse_selector_check i a ha
  simp only [inverseCoordinates, ha, ite_false, transportCoordinates]
  rw [inverse_representative_support _ j (by simpa only [hi] using hji), parameterAction_zero]

theorem product_support (i j : Fin 12) (a b : Fin 8) (hji : j < i) :
    productCoordinates i a b j = 0 := by
  by_cases ha : a = 0
  · simp [productCoordinates, ha, singleCoordinate, ne_of_lt hji]
  by_cases hb : b = 0
  · simp [productCoordinates, hb, ha, singleCoordinate, ne_of_lt hji]
  obtain ⟨hi,_,_⟩ := product_selector_check i a b ha hb
  simp only [productCoordinates, ha, hb, ite_false, transportCoordinates]
  rw [product_representative_support _ j (by simpa only [hi] using hji), parameterAction_zero]

theorem commutator_support (i j k : Fin 12) (a b : Fin 8) (hij : i < j) (hkj : k ≤ j) :
    commutatorCoordinates i j a b k = 0 := by
  by_cases hz : a = 0 ∨ b = 0
  · simp [commutatorCoordinates, hz]
  have ha : a ≠ 0 := fun h => hz (Or.inl h)
  have hb : b ≠ 0 := fun h => hz (Or.inr h)
  obtain ⟨_,hj,_,_⟩ := commutator_selector_check i j a b hij ha hb
  simp only [commutatorCoordinates, hz, ite_false, transportCoordinates]
  rw [commutator_representative_support _ k (by simpa only [hj] using hkj), parameterAction_zero]

end Kourovka.Problem2153.RootSystem.RootRelations
