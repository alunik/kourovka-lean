import Kourovka.Problem2153.BNPair
import Kourovka.Problem2153.Simplicity.Concrete

set_option autoImplicit false
namespace Kourovka.Problem2153.RootSystem

/-- Simplicity of the explicitly generated Wilson matrix group, obtained from the
proved concrete Bruhat coverage and the verified Iwasawa ingredients. -/
instance ambient_isSimpleGroup : IsSimpleGroup G :=
  ambient_isSimpleGroup_of_coverage BNPair.coverage

#print axioms ambient_isSimpleGroup
end Kourovka.Problem2153.RootSystem
