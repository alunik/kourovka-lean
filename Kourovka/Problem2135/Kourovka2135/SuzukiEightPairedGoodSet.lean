import Kourovka2135.SuzukiEightPairedAmbient
import Kourovka2135.FiniteAutomorphismRestriction
import Kourovka2135.AutomorphismGoodSet
import Kourovka2135.FinitePairWords

/-! A generating good set in the actual paired matrix subgroup.
The quotient map and the cardinal/central-kernel certificates are separate. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace Kourovka2135.SuzukiEightPairedGoodSet

abbrev Ambient := SuzukiEightCoverCodeMatrices.UnitMatrix × SuzukiEightCoverMatrices.UnitMatrix
def c : Ambient := (SuzukiEightCoverCodeMatrices.c, SuzukiEightCoverMatrices.c)
def b : Ambient := (SuzukiEightCoverCodeMatrices.b, SuzukiEightCoverMatrices.b)
def x : Ambient := (SuzukiEightCoverCodeGoodWords.x, SuzukiEightCoverMatrices.x)
def z : Ambient := (SuzukiEightCoverCodeGoodWords.z, SuzukiEightCoverMatrices.z)
def y : Ambient := (SuzukiEightCoverCodeGoodWords.y, SuzukiEightCoverMatrices.y)
def k : Ambient := (SuzukiEightCoverCodeGoodWords.k, SuzukiEightCoverMatrices.k)
def ad : Ambient := (SuzukiEightCoverCodeGoodWords.ad, SuzukiEightCoverMatrices.ad)
def bd : Ambient := (SuzukiEightCoverCodeGoodWords.bd, SuzukiEightCoverMatrices.bd)

theorem x_from_cb : c * b * b * c * b * b = x :=
  Prod.ext SuzukiEightCoverCodeGoodWords.x_from_cb SuzukiEightCoverWords.x_from_cb

theorem z_from_cb : b * b * c * b * b * c * b * c = z :=
  Prod.ext SuzukiEightCoverCodeGoodWords.z_from_cb SuzukiEightCoverWords.z_from_cb

theorem y_conjugate : z⁻¹ * x * z = y :=
  Prod.ext SuzukiEightCoverCodeGoodWords.y_conjugate SuzukiEightCoverWords.y_conjugate

theorem commutator : x⁻¹ * y⁻¹ * x * y = k :=
  Prod.ext SuzukiEightCoverCodeGoodWords.commutator SuzukiEightCoverWords.commutator

theorem c_from_xy : y * x * y * y * x * x * y⁻¹ * x⁻¹ * y⁻¹ * y⁻¹ * x * y = c :=
  Prod.ext SuzukiEightCoverCodeGoodWords.c_from_xy SuzukiEightCoverWords.c_from_xy

theorem b_from_xy : x * x * y⁻¹ * x * y * x⁻¹ * y⁻¹ * x⁻¹ * x⁻¹ = b :=
  Prod.ext SuzukiEightCoverCodeGoodWords.b_from_xy SuzukiEightCoverWords.b_from_xy

theorem ad_from_cb : b⁻¹ * c * b⁻¹ * c * b * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * c * b⁻¹ * c * b * c = ad :=
  Prod.ext SuzukiEightCoverCodeGoodWords.ad_from_cb SuzukiEightCoverWords.ad_from_cb

theorem bd_from_cb : b * b * c * b * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c * b * b * c * b⁻¹ * c * b * b * c * b * c * b⁻¹ * c = bd :=
  Prod.ext SuzukiEightCoverCodeGoodWords.bd_from_cb SuzukiEightCoverWords.bd_from_cb

theorem x_seventh : x * x * x * x * x * x * x = (1 : Ambient) :=
  Prod.ext SuzukiEightCoverCodeGoodWords.x_seventh SuzukiEightCoverWords.x_seventh

def coverGroup : Subgroup Ambient := Subgroup.closure ({c, b} : Set Ambient)
abbrev E := coverGroup

theorem c_mem : c ∈ coverGroup := Subgroup.subset_closure (Set.mem_insert _ _)
theorem b_mem : b ∈ coverGroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem x_mem : x ∈ coverGroup := by
  rw [← x_from_cb]
  exact (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem c_mem b_mem) b_mem) c_mem) b_mem) b_mem)

theorem z_mem : z ∈ coverGroup := by
  rw [← z_from_cb]
  exact (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem b_mem b_mem) c_mem) b_mem) b_mem) c_mem) b_mem) c_mem)

theorem y_mem : y ∈ coverGroup := by
  rw [← y_conjugate]
  exact (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.inv_mem z_mem) x_mem) z_mem)

theorem ad_mem : ad ∈ coverGroup := by
  rw [← ad_from_cb]
  exact (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.inv_mem b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) c_mem) b_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) c_mem)

theorem bd_mem : bd ∈ coverGroup := by
  rw [← bd_from_cb]
  exact (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem (coverGroup.mul_mem b_mem b_mem) c_mem) b_mem) c_mem) b_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) b_mem) c_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem) b_mem) b_mem) c_mem) b_mem) c_mem) (coverGroup.inv_mem b_mem)) c_mem)

def ambientD : MulAut Ambient := SuzukiEightPairedAmbient.outerAut

theorem ambientD_c : ambientD c = ad := by
  apply Prod.ext
  · exact SuzukiEightCoverCodeGoodWords.outer_c
  · change SuzukiEightCoverMatrices.d⁻¹ * SuzukiEightCoverMatrices.c *
      (SuzukiEightCoverMatrices.d⁻¹)⁻¹ = SuzukiEightCoverMatrices.ad
    simpa only [inv_inv] using SuzukiEightCoverWords.ad_conjugate

theorem ambientD_b : ambientD b = bd := by
  apply Prod.ext
  · exact SuzukiEightCoverCodeGoodWords.outer_b
  · change SuzukiEightCoverMatrices.d⁻¹ * SuzukiEightCoverMatrices.b *
      (SuzukiEightCoverMatrices.d⁻¹)⁻¹ = SuzukiEightCoverMatrices.bd
    simpa only [inv_inv] using SuzukiEightCoverWords.bd_conjugate

theorem ambientD_preserves : ∀ g ∈ coverGroup, ambientD g ∈ coverGroup := by
  apply FiniteAutomorphismRestriction.preserves_closure
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · rw [ambientD_c]; exact ad_mem
  · have he : g = b := Set.mem_singleton_iff.mp hg
    subst g
    rw [ambientD_b]; exact bd_mem

def cE : E := ⟨c, c_mem⟩
def xE : E := ⟨x, x_mem⟩
def yE : E := ⟨y, y_mem⟩
def zE : E := ⟨z, z_mem⟩
def cAut : MulAut E := SuzukiEightPairedAmbient.inverseConj (G := E) cE
def dAut : MulAut E :=
  FiniteAutomorphismRestriction.restrict coverGroup ambientD ambientD_preserves
def ambientC : MulAut Ambient := SuzukiEightPairedAmbient.inverseConj (G := Ambient) c

theorem cAut_compatible (g : E) : (cAut g).val = ambientC g.val := rfl
theorem dAut_compatible (g : E) : (dAut g).val = ambientD g.val := rfl

def outputAut : MulAut E := (((((((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut

def ambientOutput : MulAut Ambient := (((((((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD

theorem outputAut_compatible (g : E) : (outputAut g).val = ambientOutput g.val :=
  (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut) dAut (((((((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC) ambientD (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut) cAut ((((((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut) dAut (((((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC) ambientD (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm) cAut ((((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut) dAut.symm (((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC) ambientD.symm (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut) cAut ((((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut) dAut (((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC) ambientD (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut).trans dAut.symm) cAut ((((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm).trans cAut) dAut.symm (((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm).trans ambientC) ambientD.symm (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut).trans dAut.symm) cAut ((((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC).trans ambientD.symm) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut).trans cAut) dAut.symm (((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD).trans ambientC) ambientD.symm (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut).trans dAut) cAut ((((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC).trans ambientD) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((((cAut).trans dAut.symm).trans cAut).trans dAut.symm).trans cAut) dAut (((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm).trans ambientC) ambientD (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((((cAut).trans dAut.symm).trans cAut).trans dAut.symm) cAut ((((ambientC).trans ambientD.symm).trans ambientC).trans ambientD.symm) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (((cAut).trans dAut.symm).trans cAut) dAut.symm (((ambientC).trans ambientD.symm).trans ambientC) ambientD.symm (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) ((cAut).trans dAut.symm) cAut ((ambientC).trans ambientD.symm) ambientC (FiniteAutomorphismRestriction.compatible_trans (fun g : E => g.val) (cAut) dAut.symm (ambientC) ambientD.symm cAut_compatible (FiniteAutomorphismRestriction.compatible_symm (fun g : E => g.val) dAut ambientD dAut_compatible)) cAut_compatible) (FiniteAutomorphismRestriction.compatible_symm (fun g : E => g.val) dAut ambientD dAut_compatible)) cAut_compatible) dAut_compatible) cAut_compatible) (FiniteAutomorphismRestriction.compatible_symm (fun g : E => g.val) dAut ambientD dAut_compatible)) cAut_compatible) (FiniteAutomorphismRestriction.compatible_symm (fun g : E => g.val) dAut ambientD dAut_compatible)) cAut_compatible) dAut_compatible) cAut_compatible) (FiniteAutomorphismRestriction.compatible_symm (fun g : E => g.val) dAut ambientD dAut_compatible)) cAut_compatible) dAut_compatible) cAut_compatible) dAut_compatible) g

theorem ambientOutput_snd (g : Ambient) :
    (ambientOutput g).2 = SuzukiEightCoverMatrices.t⁻¹ * g.2 * SuzukiEightCoverMatrices.t := by
  change SuzukiEightCoverMatrices.d⁻¹ * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d⁻¹ * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d⁻¹ * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d⁻¹ * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d * (SuzukiEightCoverMatrices.c⁻¹ * (SuzukiEightCoverMatrices.d * (SuzukiEightCoverMatrices.c⁻¹ * (g.2) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d⁻¹) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d⁻¹) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d⁻¹) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d⁻¹) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d⁻¹) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d) * SuzukiEightCoverMatrices.c) * SuzukiEightCoverMatrices.d = _
  rw [← SuzukiEightCoverWords.t_from_cd]
  group

theorem ambientOutput_x : ambientOutput x = k := by
  apply Prod.ext
  · exact SuzukiEightCoverCodeGoodWords.outputAut_x
  · rw [ambientOutput_snd]
    exact SuzukiEightCoverWords.commutator_conjugate

def inputAut : MulAut E := SuzukiEightPairedAmbient.inverseConj (G := E) zE

theorem inputAut_x : inputAut xE = yE := by
  apply Subtype.ext
  change z⁻¹ * x * (z⁻¹)⁻¹ = y
  simpa only [inv_inv] using y_conjugate

theorem commutator_identity : paperCommutator xE (inputAut xE) = outputAut xE := by
  rw [inputAut_x]
  apply Subtype.ext
  rw [outputAut_compatible]
  change x⁻¹ * y⁻¹ * x * y = ambientOutput x
  exact commutator.trans ambientOutput_x.symm

theorem closure_pair : Subgroup.closure ({x, y} : Set Ambient) = coverGroup := by
  let H : Subgroup Ambient := Subgroup.closure ({x, y} : Set Ambient)
  have hx : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc : c ∈ H := by
    rw [← c_from_xy]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hy hx) hy) hy) hx) hx) (H.inv_mem hy)) (H.inv_mem hx)) (H.inv_mem hy)) (H.inv_mem hy)) hx) hy)
  have hb : b ∈ H := by
    rw [← b_from_xy]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hx hx) (H.inv_mem hy)) hx) hy) (H.inv_mem hx)) (H.inv_mem hy)) (H.inv_mem hx)) (H.inv_mem hx))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact x_mem
    · exact (Set.mem_singleton_iff.mp hg).symm ▸ y_mem
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact hc
    · exact (Set.mem_singleton_iff.mp hg).symm ▸ hb

theorem generates : Subgroup.closure ({xE, inputAut xE} : Set E) = ⊤ := by
  rw [inputAut_x]
  exact closure_pair_eq_top_of_subtype_closure coverGroup xE yE closure_pair

def Y : Set E := automorphismOrbit xE

theorem goodSet : IsGeneratingGoodSet Y :=
  isGeneratingGoodSet_automorphismOrbit xE inputAut outputAut commutator_identity generates

instance : Group.IsPerfect E := goodSet.isPerfect ⟨xE, mem_automorphismOrbit xE⟩

theorem orderOf_x : orderOf x = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hn : x ≠ 1 := by
    intro h
    exact SuzukiEightCoverMatrices.x_ne_one (congrArg Prod.snd h)
  apply orderOf_eq_prime _ hn
  calc
    x ^ 7 = x * x * x * x * x * x * x := by
      simp only [pow_succ, pow_zero, one_mul]
    _ = 1 := x_seventh

theorem orderOf_xE : orderOf xE = 7 := by
  rw [← orderOf_injective coverGroup.subtype coverGroup.subtype_injective xE]
  exact orderOf_x

theorem orderOf_mem_Y {g : E} (hg : g ∈ Y) : orderOf g = 7 :=
  (orderOf_mem_automorphismOrbit xE hg).trans orderOf_xE

theorem universal_value (w : OuterWord) : xE ∈ w.values E :=
  goodSet.subset_values w (mem_automorphismOrbit xE)

end Kourovka2135.SuzukiEightPairedGoodSet
