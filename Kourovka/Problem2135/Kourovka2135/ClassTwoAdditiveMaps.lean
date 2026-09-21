import Kourovka2135.ClassTwoAdditive

/-! Maps between the corrected additive structure and the original central subgroups and quotients. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135.ClassTwoAdditive
open scoped IsMulCommutative
variable {G : Type u} [Group G] (D : ClassTwoData G)

instance [Finite G] : Finite (ClassTwoAdditive D) := Finite.of_injective _ (toMul_injective D)

/-- A homomorphism to an abelian group also respects corrected addition. -/
def quotientMap {Q : Type v} [Group Q] [IsMulCommutative Q] (f : G →* Q) :
    ClassTwoAdditive D →+ Additive Q where
  toFun x := Additive.ofMul (f (toMul D x))
  map_zero' := f.map_one
  map_add' x y := by
    change f (classTwoSum D.halfExponent (toMul D x) (toMul D y)) =
      f (toMul D x) * f (toMul D y)
    have hc (a b : G) : f (paperCommutator a b) = 1 := by
      simp [paperCommutator, mul_comm]
    simp only [classTwoSum, map_mul, map_pow, hc, one_pow, mul_one]

/-- A central subgroup has its usual addition inside the corrected additive structure. -/
def centralEmbedding (H : Subgroup G) (hH : H ≤ Subgroup.center G) :
    Additive H →+ ClassTwoAdditive D where
  toFun x := ofMul D (x.toMul : G)
  map_zero' := rfl
  map_add' x y := by
    apply toMul_injective D
    change (x.toMul : G) * (y.toMul : G) =
      classTwoSum D.halfExponent (x.toMul : G) (y.toMul : G)
    symm
    apply classTwoSum_of_commute
    exact Subgroup.mem_center_iff.mp (hH y.toMul.property) x.toMul

/-- Group automorphisms act on the corrected additive group. -/
def mapAut (a : MulAut G) : AddAut (ClassTwoAdditive D) where
  toFun x := ofMul D (a (toMul D x))
  invFun x := ofMul D (a.symm (toMul D x))
  left_inv x := toMul_injective D (a.left_inv (toMul D x))
  right_inv x := toMul_injective D (a.right_inv (toMul D x))
  map_add' x y := (map D D a.toMonoidHom rfl).map_add x y

def mapPermHom : MulAut G →* Equiv.Perm (ClassTwoAdditive D) where
  toFun a := (mapAut D a).toEquiv
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

end Kourovka2135.ClassTwoAdditive
