import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Comparing irreducible representations through their actual images.

A shared nonzero image vector forces image containment by pulling an
invariant subspace back to the simple source. Factoring through an
injective intertwiner then gives a genuine representation equivalence.
No subtype representation or transferred irreducibility instance is used.
-/

set_option autoImplicit false
noncomputable section
universe u v w x y

namespace Kourovka2135.IrreducibleImageComparison

variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type x} [AddCommGroup W] [Module k W]
variable {U : Type y} [AddCommGroup U] [Module k U]
variable {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G U}

/-- Pull an invariant subspace back along the actual intertwining map. -/
def preimage (f : ρ.IntertwiningMap τ) (S : Subrepresentation τ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change f (ρ g v) ∈ S.toSubmodule
    rw [f.isIntertwining]
    exact S.apply_mem_toSubmodule g hv

@[simp] theorem mem_preimage (f : ρ.IntertwiningMap τ) (S : Subrepresentation τ) (v : V) :
    v ∈ preimage f S ↔ f v ∈ S := Iff.rfl

/-- A nonzero intersection with a simple image forces containment of that image. -/
theorem range_le_of_nonzero_mem [ρ.IsIrreducible] (f : ρ.IntertwiningMap τ)
    (S : Subrepresentation τ) (z : U) (hz : z ≠ 0)
    (hzf : z ∈ f.range) (hzS : z ∈ S) : f.range ≤ S := by
  obtain ⟨v, hv⟩ := hzf
  change f v = z at hv
  have hvS : v ∈ preimage f S := by
    change f v ∈ S
    rwa [hv]
  have hne : preimage f S ≠ ⊥ := by
    intro h
    rw [h] at hvS
    change v = 0 at hvS
    apply hz
    calc
      z = f v := hv.symm
      _ = 0 := by rw [hvS, map_zero]
  have htop : preimage f S = ⊤ := (eq_bot_or_eq_top (preimage f S)).resolve_left hne
  intro w hw
  obtain ⟨v, rfl⟩ := hw
  change v ∈ preimage f S
  rw [htop]
  trivial

/-- A target with a nonzero proper invariant subspace is never a whole simple image. -/
theorem range_ne_top_of_nonzero_proper [ρ.IsIrreducible] (f : ρ.IntertwiningMap τ)
    (S : Subrepresentation τ) (hS : S ≠ ⊤) (z : U) (hz : z ≠ 0) (hzS : z ∈ S) :
    f.range ≠ ⊤ := by
  intro hf
  have hzf : z ∈ f.range := by rw [hf]; trivial
  have hle := range_le_of_nonzero_mem f S z hz hzf hzS
  apply hS
  apply top_unique
  rwa [hf] at hle

/-- The underlying factor map through an injective intertwiner, using its actual linear range. -/
def factorLinear (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (he : Function.Injective e) (hle : f.range ≤ e.range) : V →ₗ[k] W :=
  LinearMap.codRestrictOfInjective f.toLinearMap e.toLinearMap he
    (fun v => hle ⟨v, rfl⟩)

/-- The factor map is a genuine lift of the original map. -/
theorem factorLinear_spec (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (he : Function.Injective e) (hle : f.range ≤ e.range) (v : V) :
    e (factorLinear f e he hle v) = f v := by
  exact LinearMap.codRestrictOfInjective_comp_apply
    f.toLinearMap e.toLinearMap he (fun x => hle ⟨x, rfl⟩) v

/-- Injectivity of the target embedding proves equivariance of the factor map. -/
def factorThrough (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (he : Function.Injective e) (hle : f.range ≤ e.range) : ρ.IntertwiningMap σ where
  toLinearMap := factorLinear f e he hle
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply he
    change e (factorLinear f e he hle (ρ g v)) =
      e (σ g (factorLinear f e he hle v))
    rw [factorLinear_spec, e.isIntertwining, factorLinear_spec, f.isIntertwining]

/-- The actual intertwiner factors the original image embedding. -/
theorem factorThrough_spec (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (he : Function.Injective e) (hle : f.range ≤ e.range) (v : V) :
    e (factorThrough f e he hle v) = f v := factorLinear_spec f e he hle v

/-- Factoring a nonzero map cannot produce the zero intertwiner. -/
theorem factorThrough_ne_zero (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (he : Function.Injective e) (hle : f.range ≤ e.range) (hf : f ≠ 0) :
    factorThrough f e he hle ≠ 0 := by
  intro h
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change f v = 0
  calc
    f v = e (factorThrough f e he hle v) := (factorThrough_spec f e he hle v).symm
    _ = e 0 := by rw [h]; rfl
    _ = 0 := map_zero e

/-- A nonzero vector in two simple images produces an actual equivalence of their sources. -/
def equivOfNonzeroCommon [ρ.IsIrreducible] [σ.IsIrreducible]
    (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (z : U) (hz : z ≠ 0) (hzf : z ∈ f.range) (hze : z ∈ e.range) : ρ.Equiv σ := by
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hzf
    rw [h] at hv
    change (0 : U) = z at hv
    exact hz hv.symm
  have he0 : e ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hze
    rw [h] at hv
    change (0 : U) = z at hv
    exact hz hv.symm
  have he : Function.Injective e :=
    (Representation.IsIrreducible.injective_or_eq_zero e).resolve_right he0
  have hle := range_le_of_nonzero_mem f e.range z hz hzf hze
  let l := factorThrough f e he hle
  have hl : l ≠ 0 := factorThrough_ne_zero f e he hle hf
  exact l.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero l).resolve_right hl)

/-- Proposition-valued interface for classification theorems. -/
theorem nonempty_equiv_of_nonzero_common [ρ.IsIrreducible] [σ.IsIrreducible]
    (f : ρ.IntertwiningMap τ) (e : σ.IntertwiningMap τ)
    (z : U) (hz : z ≠ 0) (hzf : z ∈ f.range) (hze : z ∈ e.range) :
    Nonempty (ρ.Equiv σ) := ⟨equivOfNonzeroCommon f e z hz hzf hze⟩

end Kourovka2135.IrreducibleImageComparison
