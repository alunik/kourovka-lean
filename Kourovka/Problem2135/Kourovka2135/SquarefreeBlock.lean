import Kourovka2135.SquarefreeOperators
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Finite squarefree blocks of the periodic resolution. Restricting the
subset basis to one fixed finite support makes both the differential and
its contracting homotopy genuine endomorphisms of that block. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SquarefreeBlock
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (k : Type*) [Semiring k] (S : Finset ι)

abbrev Index (S : Finset ι) := {J : Finset ι // J ⊆ S}
abbrev Space (S : Finset ι) (k : Type*) [Zero k] := Index S →₀ k

/-- Forget the support bound, retaining the actual subset coordinates. -/
def embed : Space S k →ₗ[k] SquarefreeOperators.Space ι k :=
  Finsupp.lmapDomain k k Subtype.val

omit [DecidableEq ι] in
theorem embed_injective : Function.Injective (embed k S) :=
  Finsupp.mapDomain_injective Subtype.val_injective

omit [DecidableEq ι] in
@[simp] theorem embed_single (J : Index S) (c : k) :
    embed k S (Finsupp.single J c) = Finsupp.single J.val c := by
  simp [embed, Finsupp.lmapDomain_apply]

def creation (i : ι) (hi : i ∈ S) : Module.End k (Space S k) :=
  Finsupp.linearCombination k fun J => if i ∈ J.val then 0 else
    Finsupp.single ⟨insert i J.val, Finset.insert_subset hi J.property⟩ 1

def annihilation (i : ι) : Module.End k (Space S k) :=
  Finsupp.linearCombination k fun J => if i ∈ J.val then
    Finsupp.single ⟨J.val.erase i, (Finset.erase_subset i J.val).trans J.property⟩ 1
    else 0

@[simp] theorem creation_single (i : ι) (hi : i ∈ S) (J : Index S) (c : k) :
    creation k S i hi (Finsupp.single J c) = if i ∈ J.val then 0 else
      Finsupp.single ⟨insert i J.val, Finset.insert_subset hi J.property⟩ c := by
  by_cases h : i ∈ J.val <;> simp [creation, h, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem annihilation_single (i : ι) (J : Index S) (c : k) :
    annihilation k S i (Finsupp.single J c) = if i ∈ J.val then
      Finsupp.single ⟨J.val.erase i, (Finset.erase_subset i J.val).trans J.property⟩ c
      else 0 := by
  by_cases h : i ∈ J.val <;> simp [annihilation, h, Finsupp.smul_single, smul_eq_mul]

theorem embed_creation (i : ι) (hi : i ∈ S) (v : Space S k) :
    embed k S (creation k S i hi v) = SquarefreeOperators.creation k i (embed k S v) := by
  suffices h : (embed k S).comp (creation k S i hi) =
      (SquarefreeOperators.creation k i).comp (embed k S) from LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro J c
  by_cases h : i ∈ J.val <;> simp [h]

theorem embed_annihilation (i : ι) (v : Space S k) :
    embed k S (annihilation k S i v) =
      SquarefreeOperators.annihilation k i (embed k S v) := by
  suffices h : (embed k S).comp (annihilation k S i) =
      (SquarefreeOperators.annihilation k i).comp (embed k S) from LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro J c
  by_cases h : i ∈ J.val <;> simp [h]

/-- The differential is the sum over precisely the block's active support. -/
def differential : Module.End k (Space S k) := ∑ i : S, creation k S i.val i.property

theorem embed_differential (v : Space S k) :
    embed k S (differential k S v) =
      SquarefreeOperators.differential k S (embed k S v) := by
  simp only [differential, LinearMap.sum_apply, map_sum, embed_creation,
    SquarefreeOperators.differential]
  exact Finset.sum_coe_sort S (fun i => SquarefreeOperators.creation k i (embed k S v))

variable [CharP k 2]

theorem differential_square_zero : differential k S * differential k S = 0 := by
  apply LinearMap.ext
  intro v
  apply embed_injective k S
  simp only [Module.End.mul_apply, LinearMap.zero_apply, map_zero, embed_differential]
  exact LinearMap.congr_fun (SquarefreeOperators.differential_mul_self k S) (embed k S v)

/-- The contraction remains inside the finite block. -/
theorem differential_annihilation_add (i : ι) (hi : i ∈ S) :
    differential k S * annihilation k S i +
      annihilation k S i * differential k S = 1 := by
  apply LinearMap.ext
  intro v
  apply embed_injective k S
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, map_add,
    embed_differential, embed_annihilation]
  exact LinearMap.congr_fun
    (SquarefreeOperators.differential_annihilation_add k S i hi) (embed k S v)

theorem differential_ker_eq_range (hS : S.Nonempty) :
    (differential k S).ker = (differential k S).range := by
  obtain ⟨i, hi⟩ := hS
  ext v
  constructor
  · intro hv
    refine ⟨annihilation k S i v, ?_⟩
    have h := LinearMap.congr_fun (differential_annihilation_add k S i hi) v
    have hv0 : differential k S v = 0 := hv
    simpa [Module.End.mul_apply, hv0] using h
  · rintro ⟨u, rfl⟩
    exact LinearMap.congr_fun (differential_square_zero k S) u

end Kourovka2135.SquarefreeBlock
