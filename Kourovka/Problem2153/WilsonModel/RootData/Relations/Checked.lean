import Kourovka.Problem2153.WilsonModel.RootData.Relations
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Convenience
set_option autoImplicit false
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations

theorem inverse_identity (k : Fin 12) :
    (RootSystem.root (inverseData k).i (inverseData k).a)⁻¹ =
      coordinateGroup (inverseData k).coords :=
  inverse_convenient k (inverse_checked k)

theorem product_identity (k : Fin 84) :
    RootSystem.root (productData k).i (productData k).a *
      RootSystem.root (productData k).i (productData k).b =
        coordinateGroup (productData k).coords :=
  product_convenient k (product_checked k)

theorem commutator_identity (k : Fin 90) :
    (RootSystem.root (commutatorData k).i (commutatorData k).a)⁻¹ *
      (RootSystem.root (commutatorData k).j (commutatorData k).b)⁻¹ *
        RootSystem.root (commutatorData k).i (commutatorData k).a *
          RootSystem.root (commutatorData k).j (commutatorData k).b =
            coordinateGroup (commutatorData k).coords :=
  commutator_convenient k (commutator_checked k)

theorem weyl_identity (k : Fin 21) :
    rightConj (RootSystem.root (weylData k).i (weylData k).a)
      (weylGenerator (weylData k).sigma) = coordinateGroup (weylData k).coords :=
  weyl_convenient k (weyl_checked k)

end Kourovka.Problem2153.WilsonModel.RootData.Relations
