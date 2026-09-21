import Kourovka2135.SuzukiEightCoverCodeGoodWords
import Kourovka2135.SuzukiEightCoverWords

/-! The paired ambient automorphism, with explicit component maps. Keeping
the component equalities named avoids unfolding concrete matrix operations
when restricting or composing the automorphism. -/

set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace Kourovka2135.SuzukiEightPairedAmbient

abbrev Ambient := SuzukiEightCoverCodeMatrices.UnitMatrix × SuzukiEightCoverMatrices.UnitMatrix

def inverseConj {G : Type*} [Group G] (d : G) : MulAut G := MulAut.conj d⁻¹

@[simp] theorem inverseConj_apply {G : Type*} [Group G] (d g : G) :
    inverseConj d g = d⁻¹ * g * d := by simp [inverseConj]

@[simp] theorem inverseConj_symm_apply {G : Type*} [Group G] (d g : G) :
    (inverseConj d).symm g = d * g * d⁻¹ := by simp [inverseConj, MulAut.conj_apply]

set_option diagnostics true in
def coverAut : MulAut SuzukiEightCoverMatrices.UnitMatrix :=
  inverseConj (G := SuzukiEightCoverMatrices.UnitMatrix) SuzukiEightCoverMatrices.d

def outerAut : MulAut Ambient where
  toFun g := (SuzukiEightCoverSemilinear.outerAut g.1, coverAut g.2)
  invFun g := (SuzukiEightCoverSemilinear.outerAut.symm g.1, coverAut.symm g.2)
  left_inv g := Prod.ext (SuzukiEightCoverSemilinear.outerAut.symm_apply_apply g.1)
    (coverAut.symm_apply_apply g.2)
  right_inv g := Prod.ext (SuzukiEightCoverSemilinear.outerAut.apply_symm_apply g.1)
    (coverAut.apply_symm_apply g.2)
  map_mul' g h := Prod.ext (map_mul SuzukiEightCoverSemilinear.outerAut g.1 h.1)
    (map_mul coverAut g.2 h.2)

@[simp] theorem outerAut_fst (g : Ambient) :
    (outerAut g).1 = SuzukiEightCoverSemilinear.outerAut g.1 := rfl

@[simp] theorem outerAut_snd (g : Ambient) : (outerAut g).2 = coverAut g.2 := rfl

@[simp] theorem outerAut_symm_fst (g : Ambient) :
    (outerAut.symm g).1 = SuzukiEightCoverSemilinear.outerAut.symm g.1 := rfl

@[simp] theorem outerAut_symm_snd (g : Ambient) :
    (outerAut.symm g).2 = coverAut.symm g.2 := rfl

end Kourovka2135.SuzukiEightPairedAmbient
