import Kourovka2135.NestedNormalExtension
import Kourovka2135.AbelianExtensionRepresentation
import Kourovka2135.Vendor.CFSG.ElementaryAbelian

/-! The actual kernel in a quotient by the intersection of two normal
subgroups. Its two quotient coordinates are injective jointly, and are
surjective jointly when two subgroups supply the coordinates independently.

Elementary abelianity is inherited from the two actual coordinate kernels.
The coordinate maps intertwine the actual quotient conjugation actions;
there is no semisimplicity assumption on the joint kernel.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.DoubleQuotientKernel

open scoped IsMulCommutative

variable {G : Type} [Group G]

/-- The natural surjection from R to its actual image in G/C. -/
def fromRadical (C R : Subgroup G) [C.Normal] :
    R →* NestedNormalExtension.kernel C R where
  toFun r := ⟨QuotientGroup.mk' C (r : G), Subgroup.mem_map_of_mem _ r.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext ((QuotientGroup.mk' C).map_mul (a : G) (b : G))

@[simp] theorem fromRadical_val (C R : Subgroup G) [C.Normal] (r : R) :
    (fromRadical C R r : G ⧸ C) = QuotientGroup.mk' C (r : G) := rfl

theorem fromRadical_surjective (C R : Subgroup G) [C.Normal] :
    Function.Surjective (fromRadical C R) := by
  intro x
  obtain ⟨r, hr, hrx⟩ := x.property
  exact ⟨⟨r, hr⟩, Subtype.ext hrx⟩

/-- An actual quotient map restricted to the two actual images of R. -/
def kernelMap (E C R : Subgroup G) [E.Normal] [C.Normal] (hEC : E ≤ C) :
    NestedNormalExtension.kernel E R →* NestedNormalExtension.kernel C R where
  toFun x := ⟨NestedNormalExtension.projection E C hEC (x : G ⧸ E), by
    obtain ⟨g, hg, hgx⟩ := x.property
    refine ⟨g, hg, ?_⟩
    rw [← hgx]
    rfl⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext
    ((NestedNormalExtension.projection E C hEC).map_mul (a : G ⧸ E) (b : G ⧸ E))

@[simp] theorem kernelMap_val (E C R : Subgroup G) [E.Normal] [C.Normal]
    (hEC : E ≤ C) (x : NestedNormalExtension.kernel E R) :
    (kernelMap E C R hEC x : G ⧸ C) =
      NestedNormalExtension.projection E C hEC (x : G ⧸ E) := rfl

@[simp] theorem kernelMap_fromRadical (E C R : Subgroup G) [E.Normal] [C.Normal]
    (hEC : E ≤ C) (r : R) :
    kernelMap E C R hEC (fromRadical E R r) = fromRadical C R r := rfl

/-- The two actual quotient coordinates of R/(C ∩ D). -/
def jointMap (C D R : Subgroup G) [C.Normal] [D.Normal] :
    NestedNormalExtension.kernel (C ⊓ D) R →*
      NestedNormalExtension.kernel C R × NestedNormalExtension.kernel D R :=
  (kernelMap (C ⊓ D) C R inf_le_left).prod
    (kernelMap (C ⊓ D) D R inf_le_right)

@[simp] theorem jointMap_fromRadical (C D R : Subgroup G) [C.Normal] [D.Normal]
    (r : R) : jointMap C D R (fromRadical (C ⊓ D) R r) =
      (fromRadical C R r, fromRadical D R r) := rfl

/-- The intersection is exactly what makes the joint quotient coordinates faithful. -/
theorem jointMap_injective (C D R : Subgroup G) [C.Normal] [D.Normal] :
    Function.Injective (jointMap C D R) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨r, rfl⟩ := fromRadical_surjective (C ⊓ D) R x
  have hC := congrArg (fun y : NestedNormalExtension.kernel C R ×
      NestedNormalExtension.kernel D R => (y.1 : G ⧸ C)) hx
  have hD := congrArg (fun y : NestedNormalExtension.kernel C R ×
      NestedNormalExtension.kernel D R => (y.2 : G ⧸ D)) hx
  change QuotientGroup.mk' C (r : G) = 1 at hC
  change QuotientGroup.mk' D (r : G) = 1 at hD
  apply Subtype.ext
  change QuotientGroup.mk' (C ⊓ D) (r : G) = 1
  exact (QuotientGroup.eq_one_iff _).mpr
    ⟨(QuotientGroup.eq_one_iff _).mp hC, (QuotientGroup.eq_one_iff _).mp hD⟩

/-- Actual subgroup images independently supply the two quotient coordinates. -/
theorem jointMap_surjective (C D R : Subgroup G) [C.Normal] [D.Normal]
    (N M : Subgroup G) (hNR : N ≤ R) (hMR : M ≤ R)
    (hND : N ≤ D) (hMC : M ≤ C)
    (hN : N.map (QuotientGroup.mk' C) = NestedNormalExtension.kernel C R)
    (hM : M.map (QuotientGroup.mk' D) = NestedNormalExtension.kernel D R) :
    Function.Surjective (jointMap C D R) := by
  intro x
  have hx : (x.1 : G ⧸ C) ∈ N.map (QuotientGroup.mk' C) := by
    rw [hN]
    exact x.1.property
  have hy : (x.2 : G ⧸ D) ∈ M.map (QuotientGroup.mk' D) := by
    rw [hM]
    exact x.2.property
  obtain ⟨n, hn, hnx⟩ := hx
  obtain ⟨m, hm, hmy⟩ := hy
  have hnD : QuotientGroup.mk' D n = 1 := (QuotientGroup.eq_one_iff _).mpr (hND hn)
  have hmC : QuotientGroup.mk' C m = 1 := (QuotientGroup.eq_one_iff _).mpr (hMC hm)
  refine ⟨fromRadical (C ⊓ D) R ⟨n * m, R.mul_mem (hNR hn) (hMR hm)⟩, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change QuotientGroup.mk' C (n * m) = (x.1 : G ⧸ C)
    rw [map_mul, hmC, mul_one, hnx]
  · apply Subtype.ext
    change QuotientGroup.mk' D (n * m) = (x.2 : G ⧸ D)
    rw [map_mul, hnD, one_mul, hmy]

/-- The actual intersection kernel is elementary abelian whenever both
actual coordinate kernels are elementary abelian. -/
theorem kernel_isElementaryAbelian (p : ℕ) (C D R : Subgroup G)
    [C.Normal] [D.Normal]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel D R)] :
    IsElementaryAbelian p (NestedNormalExtension.kernel (C ⊓ D) R) := by
  have hj := jointMap_injective C D R
  refine {
    toIsMulCommutative := ⟨⟨fun a b => hj (by rw [map_mul, map_mul, mul_comm])⟩⟩
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  apply hj
  rw [map_pow, map_one]
  apply Prod.ext
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (NestedNormalExtension.kernel C R))
      (jointMap C D R a).1
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (NestedNormalExtension.kernel D R))
      (jointMap C D R a).2

variable (p : ℕ) [Fact p.Prime]

/-- The actual quotient-conjugation representation on a nested kernel. -/
abbrev representation (C R : Subgroup G) [C.Normal] [R.Normal] (hCR : C ≤ R)
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)] :
    Representation (ZMod p) (G ⧸ R) (Additive (NestedNormalExtension.kernel C R)) :=
  AbelianExtensionRepresentation.representation (NestedNormalExtension.extension C R hCR) p

/-- The actual quotient coordinate written as a prime-field linear map. -/
def kernelLinearMap (E C R : Subgroup G) [E.Normal] [C.Normal] (hEC : E ≤ C)
    [IsElementaryAbelian p (NestedNormalExtension.kernel E R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)] :
    Additive (NestedNormalExtension.kernel E R) →ₗ[ZMod p]
      Additive (NestedNormalExtension.kernel C R) :=
  (kernelMap E C R hEC).toAdditive.toZModLinearMap p

@[simp] theorem kernelLinearMap_toMul (E C R : Subgroup G) [E.Normal] [C.Normal]
    (hEC : E ≤ C)
    [IsElementaryAbelian p (NestedNormalExtension.kernel E R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)]
    (x : Additive (NestedNormalExtension.kernel E R)) :
    (kernelLinearMap p E C R hEC x).toMul = kernelMap E C R hEC x.toMul := rfl

/-- Both coefficient actions are the actual ambient conjugation action,
so the actual quotient coordinate intertwines them. -/
theorem kernelLinearMap_representation (E C R : Subgroup G)
    [E.Normal] [C.Normal] [R.Normal] (hEC : E ≤ C) (hER : E ≤ R) (hCR : C ≤ R)
    [IsElementaryAbelian p (NestedNormalExtension.kernel E R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)]
    (q : G ⧸ R) (x : Additive (NestedNormalExtension.kernel E R)) :
    kernelLinearMap p E C R hEC (representation p E R hER q x) =
      representation p C R hCR q (kernelLinearMap p E C R hEC x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R q
  have hE := AbelianExtensionRepresentation.compatibleAction
    (NestedNormalExtension.extension E R hER) p (QuotientGroup.mk' E g) x
  have hC := AbelianExtensionRepresentation.compatibleAction
    (NestedNormalExtension.extension C R hCR) p (QuotientGroup.mk' C g)
    (kernelLinearMap p E C R hEC x)
  change ((representation p E R hER (QuotientGroup.mk' R g) x).toMul : G ⧸ E) =
    QuotientGroup.mk' E g * (x.toMul : G ⧸ E) * (QuotientGroup.mk' E g)⁻¹ at hE
  change ((representation p C R hCR (QuotientGroup.mk' R g)
      (kernelLinearMap p E C R hEC x)).toMul : G ⧸ C) =
    QuotientGroup.mk' C g *
      NestedNormalExtension.projection E C hEC (x.toMul : G ⧸ E) *
      (QuotientGroup.mk' C g)⁻¹ at hC
  apply Additive.ext
  apply Subtype.ext
  change NestedNormalExtension.projection E C hEC
      ((representation p E R hER (QuotientGroup.mk' R g) x).toMul : G ⧸ E) = _
  rw [hE, hC, map_mul, map_mul, map_inv,
    NestedNormalExtension.projection_mk]

/-- The actual intertwiner between nested conjugation kernels. -/
def kernelIntertwiner (E C R : Subgroup G) [E.Normal] [C.Normal] [R.Normal]
    (hEC : E ≤ C) (hER : E ≤ R) (hCR : C ≤ R)
    [IsElementaryAbelian p (NestedNormalExtension.kernel E R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)] :
    (representation p E R hER).IntertwiningMap (representation p C R hCR) where
  toLinearMap := kernelLinearMap p E C R hEC
  isIntertwining' q := by
    apply LinearMap.ext
    intro x
    exact kernelLinearMap_representation p E C R hEC hER hCR q x

/-- The two actual coefficient coordinates, as a single actual intertwiner. -/
def jointIntertwiner (C D R : Subgroup G) [C.Normal] [D.Normal] [R.Normal]
    (hCR : C ≤ R) (hDR : D ≤ R)
    [IsElementaryAbelian p (NestedNormalExtension.kernel (C ⊓ D) R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel D R)] :
    (representation p (C ⊓ D) R (inf_le_left.trans hCR)).IntertwiningMap
      ((representation p C R hCR).prod (representation p D R hDR)) :=
  (kernelIntertwiner p (C ⊓ D) C R inf_le_left (inf_le_left.trans hCR) hCR).prod
    (kernelIntertwiner p (C ⊓ D) D R inf_le_right (inf_le_left.trans hCR) hDR)

/-- The two independent subgroup images give an actual surjective
intertwiner onto the two actual coordinate representations. -/
theorem jointIntertwiner_surjective (C D R : Subgroup G)
    [C.Normal] [D.Normal] [R.Normal] (hCR : C ≤ R) (hDR : D ≤ R)
    [IsElementaryAbelian p (NestedNormalExtension.kernel (C ⊓ D) R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel C R)]
    [IsElementaryAbelian p (NestedNormalExtension.kernel D R)]
    (N M : Subgroup G) (hNR : N ≤ R) (hMR : M ≤ R)
    (hND : N ≤ D) (hMC : M ≤ C)
    (hN : N.map (QuotientGroup.mk' C) = NestedNormalExtension.kernel C R)
    (hM : M.map (QuotientGroup.mk' D) = NestedNormalExtension.kernel D R) :
    Function.Surjective (jointIntertwiner p C D R hCR hDR) := by
  intro y
  obtain ⟨x, hx⟩ := jointMap_surjective C D R N M hNR hMR hND hMC hN hM
    (y.1.toMul, y.2.toMul)
  refine ⟨Additive.ofMul x, ?_⟩
  exact congrArg (fun z : NestedNormalExtension.kernel C R ×
    NestedNormalExtension.kernel D R => (Additive.ofMul z.1, Additive.ofMul z.2)) hx

end Kourovka2135.DoubleQuotientKernel
