import Kourovka2135.AbelianExtensionCocycle
import Mathlib.GroupTheory.IsPerfect

/-! Central extensions with arbitrary abelian kernels and actual scalar
coefficient characters. No elementary-abelian structure is imposed on the
kernel. A zero ordinary H2 class extends its character to the full group,
which is impossible for a nonzero character of a perfect group.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CentralExtensionCocycle

open CategoryTheory groupCohomology AbelianExtensionCocycle
open scoped IsMulCommutative

variable {k J Q W V : Type u} [CommRing k] [Group J] [Group Q]
variable [AddCommGroup W] [AddCommGroup V] [Module k V]
variable (S : GroupExtension (Multiplicative W) J Q)
variable (hcentral : S.inl.range ≤ Subgroup.center J)

include hcentral in
/-- Actual centrality lets every kernel element pass through any section value. -/
theorem embed_conj (j : J) (w : W) :
    embed S w = j * embed S w * j⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp (hcentral ⟨Multiplicative.ofAdd w, rfl⟩) j
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

include hcentral in
/-- Actual factor sets of central extensions satisfy the additive cocycle
identity without putting a finite-field module structure on the kernel. -/
theorem factorSet_cocycle (s t v : Q) :
    factorSet S (s * t) v + factorSet S s t =
      factorSet S t v + factorSet S s (t * v) := by
  rw [add_comm (factorSet S (s * t) v) (factorSet S s t)]
  apply embed_injective S
  simp only [embed_add]
  rw [embed_conj S hcentral (normalizedSection S s) (factorSet S t v)]
  simp only [embed_factorSet]
  rw [mul_assoc s t v]
  group

include hcentral in
/-- Kernel coordinates multiply with the actual central factor set. -/
theorem coordinate_mul (j l : J) :
    coordinate S (j * l) = coordinate S j + coordinate S l +
      factorSet S (S.rightHom j) (S.rightHom l) := by
  apply embed_injective S
  simp only [embed_add]
  rw [embed_conj S hcentral (normalizedSection S (S.rightHom j)) (coordinate S l)]
  simp only [embed_coordinate, embed_factorSet, map_mul]
  group

/-- Postcompose the actual factor set with an additive character of its kernel. -/
def characterCocycle (f : W →+ V) :
    cocycles₂ (Rep.of (Representation.trivial k Q V)) :=
  ⟨fun q => f (factorSet S q.1 q.2), (mem_cocycles₂_iff _).mpr (by
    intro s t v
    have h := congrArg f (factorSet_cocycle S hcentral s t v)
    simpa only [map_add, Rep.of_ρ, Representation.trivial_apply] using h)⟩

/-- The character's actual ordinary H2 class. -/
def characterClass (f : W →+ V) :
    groupCohomology (Rep.of (Representation.trivial k Q V)) 2 :=
  H2π _ (characterCocycle (k := k) S hcentral f)

/-- Vanishing of the character class supplies an actual extension of the
character to an ordinary additive-valued group homomorphism. -/
theorem exists_hom_of_characterClass_eq_zero (f : W →+ V)
    (hf : characterClass (k := k) S hcentral f = 0) :
    ∃ d : J →* Multiplicative V,
      ∀ w : W, d (embed S w) = Multiplicative.ofAdd (f w) := by
  have hz := (H2π_eq_zero_iff
    (characterCocycle (k := k) S hcentral f)).mp hf
  obtain ⟨b, hb⟩ := hz
  have hb' (s t : Q) : b t - b (s * t) + b s = f (factorSet S s t) :=
    congrFun hb (s, t)
  have hb1 : b 1 = 0 := by
    simpa only [one_mul, sub_self, zero_add, factorSet_one_left, map_zero] using hb' 1 1
  let d : J → V := fun j => f (coordinate S j) + b (S.rightHom j)
  have hd1 : d 1 = 0 := by simp [d, hb1]
  have hdmul (j l : J) : d (j * l) = d j + d l := by
    dsimp only [d]
    rw [coordinate_mul S hcentral]
    simp only [map_add, map_mul]
    rw [← hb' (S.rightHom j) (S.rightHom l)]
    abel
  refine ⟨{ toFun := fun j => Multiplicative.ofAdd (d j)
            map_one' := hd1
            map_mul' := hdmul }, ?_⟩
  intro w
  change d (embed S w) = f w
  simp [d, hb1]

/-- A homomorphism from a perfect group to an abelian group is trivial. -/
theorem hom_eq_one_of_perfect [Group.IsPerfect J]
    (d : J →* Multiplicative V) (j : J) : d j = 1 := by
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  let : Subsingleton d.range := inferInstance
  have h : (⟨d j, ⟨j, rfl⟩⟩ : d.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

include hcentral in
/-- If actual scalar-trivial H2 vanishes, every additive character on the
central kernel of a perfect group vanishes. -/
theorem character_eq_zero_of_H2_vanishes [Group.IsPerfect J]
    [Subsingleton (groupCohomology (Rep.of (Representation.trivial k Q V)) 2)]
    (f : W →+ V) : f = 0 := by
  have hf : characterClass (k := k) S hcentral f = 0 := Subsingleton.elim _ _
  obtain ⟨d, hd⟩ := exists_hom_of_characterClass_eq_zero (k := k) S hcentral f hf
  ext w
  have h := hom_eq_one_of_perfect d (embed S w)
  rw [hd] at h
  exact h

end Kourovka2135.CentralExtensionCocycle
