import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra

/-!
# The integral Heisenberg group and its finite quotients

The multiplication is written in three coordinates. Reduction of each coordinate
modulo a positive integer separates every nonidentity element, proving residual
finiteness using mathlib's `Group.ResiduallyFinite` definition.
-/

namespace Kourovka.P21_106

/-- The three-coordinate Heisenberg group over a commutative ring. -/
@[ext]
structure Heisenberg (R : Type*) where
  r : R
  s : R
  t : R

namespace Heisenberg

variable {R S : Type*} [CommRing R] [CommRing S]

instance : One (Heisenberg R) := ⟨⟨0, 0, 0⟩⟩
instance : Mul (Heisenberg R) :=
  ⟨fun a b => ⟨a.r + b.r, a.s + b.s, a.t + b.t + a.r * b.s⟩⟩
instance : Inv (Heisenberg R) := ⟨fun a => ⟨-a.r, -a.s, a.r * a.s - a.t⟩⟩

@[simp] theorem one_r : (1 : Heisenberg R).r = 0 := rfl
@[simp] theorem one_s : (1 : Heisenberg R).s = 0 := rfl
@[simp] theorem one_t : (1 : Heisenberg R).t = 0 := rfl
@[simp] theorem mul_r (a b : Heisenberg R) : (a * b).r = a.r + b.r := rfl
@[simp] theorem mul_s (a b : Heisenberg R) : (a * b).s = a.s + b.s := rfl
@[simp] theorem mul_t (a b : Heisenberg R) : (a * b).t = a.t + b.t + a.r * b.s := rfl
@[simp] theorem inv_r (a : Heisenberg R) : a⁻¹.r = -a.r := rfl
@[simp] theorem inv_s (a : Heisenberg R) : a⁻¹.s = -a.s := rfl
@[simp] theorem inv_t (a : Heisenberg R) : a⁻¹.t = a.r * a.s - a.t := rfl

instance : Group (Heisenberg R) where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

/-- Commutators use the inverse-first convention of the displayed formula. -/
theorem commutator_eq (a b : Heisenberg R) :
    a⁻¹ * b⁻¹ * a * b = ⟨0, 0, a.r * b.s - a.s * b.r⟩ := by
  ext <;> simp
  ring

/-- Apply a ring homomorphism to all three coordinates. -/
def map (f : R →+* S) : Heisenberg R →* Heisenberg S where
  toFun a := ⟨f a.r, f a.s, f a.t⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

@[simp] theorem map_r (f : R →+* S) (a : Heisenberg R) : (map f a).r = f a.r := rfl
@[simp] theorem map_s (f : R →+* S) (a : Heisenberg R) : (map f a).s = f a.s := rfl
@[simp] theorem map_t (f : R →+* S) (a : Heisenberg R) : (map f a).t = f a.t := rfl

instance [Finite R] : Finite (Heisenberg R) :=
  Finite.of_injective (fun a : Heisenberg R => (a.r, a.s, a.t))
    (by intro a b h; cases a; cases b; simpa using h)

end Heisenberg

/-- The integral Heisenberg group. -/
abbrev H := Heisenberg ℤ

/-- The central element with integer coordinate `n`. -/
def central (n : ℤ) : H := ⟨0, 0, n⟩

@[simp] theorem central_r (n : ℤ) : (central n).r = 0 := rfl
@[simp] theorem central_s (n : ℤ) : (central n).s = 0 := rfl
@[simp] theorem central_t (n : ℤ) : (central n).t = n := rfl
@[simp] theorem central_zero : central 0 = 1 := rfl

@[simp] theorem central_add (m n : ℤ) : central (m + n) = central m * central n := by
  ext <;> simp [central]

@[simp] theorem central_neg (n : ℤ) : central (-n) = (central n)⁻¹ := by
  ext <;> simp [central]

theorem central_injective : Function.Injective central := by
  intro m n h
  exact congrArg Heisenberg.t h

/-- The central copy of the additive group of integers, written multiplicatively. -/
def centralHom : Multiplicative ℤ →* H where
  toFun n := central n.toAdd
  map_one' := rfl
  map_mul' m n := central_add m.toAdd n.toAdd

@[simp] theorem central_zpow (m n : ℤ) : (central m) ^ n = central (n * m) := by
  have h := (map_zpow centralHom (Multiplicative.ofAdd m) n).symm
  change (central m) ^ n = central ((Multiplicative.ofAdd m ^ n).toAdd) at h
  simpa [toAdd_zpow, zsmul_eq_mul] using h

/-- A nonzero integer stays nonzero modulo one more than its absolute value. -/
theorem intCast_natAbs_succ_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (n : ZMod (n.natAbs + 1)) ≠ 0 := by
  intro h
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd n (n.natAbs + 1)).mp h
  rw [Int.natCast_dvd] at hd
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd
  omega

instance : Group.ResiduallyFinite H := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro a ha
  have h : a.r ≠ 0 ∨ a.s ≠ 0 ∨ a.t ≠ 0 := by
    by_contra! h
    apply ha
    ext <;> simp [h.1, h.2.1, h.2.2]
  rcases h with hr | hs | ht
  · let m := a.r.natAbs + 1
    exact ⟨Heisenberg (ZMod m), inferInstance, inferInstance,
      Heisenberg.map (Int.castRingHom (ZMod m)), fun h =>
      intCast_natAbs_succ_ne_zero hr (congrArg Heisenberg.r h)⟩
  · let m := a.s.natAbs + 1
    exact ⟨Heisenberg (ZMod m), inferInstance, inferInstance,
      Heisenberg.map (Int.castRingHom (ZMod m)), fun h =>
      intCast_natAbs_succ_ne_zero hs (congrArg Heisenberg.s h)⟩
  · let m := a.t.natAbs + 1
    exact ⟨Heisenberg (ZMod m), inferInstance, inferInstance,
      Heisenberg.map (Int.castRingHom (ZMod m)), fun h =>
      intCast_natAbs_succ_ne_zero ht (congrArg Heisenberg.t h)⟩

end Kourovka.P21_106
