import Kourovka2135.AbelianExtensionCocycle
import Mathlib.GroupTheory.Frattini
import Mathlib.RepresentationTheory.Irreducible

/-! The actual extension factor-set map is injective for simple coefficients
when the kernel lies in the Frattini subgroup. A zero class gives a crossed
homomorphism; its zero subgroup supplies a supplement to the kernel.

The ordinary H2 class is computed from the actual normalized section factor set.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.AbelianExtensionCocycle

section General

variable {k J Q W V : Type u} [CommRing k] [Group J] [Group Q]
variable [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]

/-- The zero fiber of a crossed homomorphism is an actual subgroup. -/
def crossedHomZeroSubgroup (π : J →* Q) (ρ : Representation k Q V)
    (d : J → V) (hd1 : d 1 = 0)
    (hdmul : ∀ j l : J, d (j * l) = d j + ρ (π j) (d l)) : Subgroup J where
  carrier := {j | d j = 0}
  one_mem' := hd1
  mul_mem' := by
    intro j l hj hl
    change d j = 0 at hj
    change d l = 0 at hl
    change d (j * l) = 0
    rw [hdmul, hj, hl, map_zero, add_zero]
  inv_mem' := by
    intro j hj
    change d j = 0 at hj
    change d j⁻¹ = 0
    have hz : ρ (π j) (d j⁻¹) = 0 := by
      simpa only [mul_inv_cancel, hd1, hj, zero_add] using (hdmul j j⁻¹).symm
    have h := congrArg (ρ ((π j)⁻¹)) hz
    simpa only [ρ.inv_self_apply, map_zero] using h

variable (S : GroupExtension (Multiplicative W) J Q)
variable (ρV : Representation k Q V)

omit [Module k W] in
/-- Surjectivity on the kernel lets the zero fiber correct every coset. -/
theorem crossedHomZeroSubgroup_sup_eq_top
    (d : J → V) (hd1 : d 1 = 0)
    (hdmul : ∀ j l : J, d (j * l) = d j + ρV (S.rightHom j) (d l))
    (f : W → V) (hf : Function.Surjective f)
    (hdf : ∀ w : W, d (embed S w) = f w) :
    crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul ⊔ S.inl.range = ⊤ := by
  apply top_le_iff.mp
  intro j _
  obtain ⟨w, hw⟩ := hf (-d j)
  have hz : embed S w * j ∈ crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul := by
    change d (embed S w * j) = 0
    rw [hdmul, hdf, hw, rightHom_embed, map_one, Module.End.one_apply, neg_add_cancel]
  have hwmem : embed S w ∈ S.inl.range := ⟨Multiplicative.ofAdd w, rfl⟩
  have hm := (crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul ⊔ S.inl.range).mul_mem
    ((show S.inl.range ≤
      crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul ⊔ S.inl.range from
      le_sup_right) (S.inl.range.inv_mem hwmem))
    ((show crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul ≤
      crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul ⊔ S.inl.range from
      le_sup_left) hz)
  simpa only [inv_mul_cancel_left] using hm

omit [Module k W] in
/-- A crossed homomorphism with surjective kernel restriction cannot be
nonzero on a Frattini kernel. -/
theorem crossedHom_restriction_eq_zero_of_frattini [Finite J]
    (hΦ : S.inl.range ≤ frattini J)
    (d : J → V) (hd1 : d 1 = 0)
    (hdmul : ∀ j l : J, d (j * l) = d j + ρV (S.rightHom j) (d l))
    (f : W → V) (hf : Function.Surjective f)
    (hdf : ∀ w : W, d (embed S w) = f w) : ∀ w : W, f w = 0 := by
  have hsup := crossedHomZeroSubgroup_sup_eq_top S ρV d hd1 hdmul f hf hdf
  have htop : crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul = ⊤ := by
    apply frattini_nongenerating
    apply top_le_iff.mp
    rw [← hsup]
    exact sup_le_sup_left hΦ _
  intro w
  have hw : embed S w ∈ crossedHomZeroSubgroup S.rightHom ρV d hd1 hdmul := by
    rw [htop]
    trivial
  change d (embed S w) = 0 at hw
  rw [hdf] at hw
  exact hw

end General

section Field

variable {k J Q W V : Type u} [Field k] [Group J] [Group Q] [Finite J]
variable [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
variable (S : GroupExtension (Multiplicative W) J Q) (ρV : Representation k Q V)
variable (ρW : Representation k Q W) (hcompat : CompatibleAction S ρW)
variable [ρV.IsIrreducible]

/-- A zero ordinary H2 class forces the actual coefficient intertwiner to vanish. -/
theorem eq_zero_of_transgression_eq_zero
    (hΦ : S.inl.range ≤ frattini J) (f : ρW.IntertwiningMap ρV)
    (hf : transgression S ρW ρV hcompat f = 0) : f = 0 := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hsurj | hzero
  · obtain ⟨d, hd1, hdmul, hdf⟩ :=
      exists_crossedHom_of_transgression_eq_zero S ρW ρV hcompat f hf
    have hz := crossedHom_restriction_eq_zero_of_frattini
      S ρV hΦ d hd1 hdmul f hsurj hdf
    ext w
    exact hz w
  · exact hzero

/-- The extension's actual coefficient-class map is injective on the Hom space. -/
theorem transgression_injective
    (hΦ : S.inl.range ≤ frattini J) :
    Function.Injective (transgression S ρW ρV hcompat) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro f hf
  change f = 0
  exact eq_zero_of_transgression_eq_zero S ρV ρW hcompat hΦ f hf

end Field

end Kourovka2135.AbelianExtensionCocycle
