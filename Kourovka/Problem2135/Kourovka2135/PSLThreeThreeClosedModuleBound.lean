import Kourovka2135.PSLThreeThreeFrattiniLifting
import Kourovka2135.IrreducibleCorrectionAlternative
import Kourovka2135.RepresentationCohomologyAlternative

/-! The closed-field representation calculation discharges the exact
binary module interface used by the minimal-kernel argument. The commuting
field is the actual endomorphism field, and its degree is retained. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeClosedModuleBound
open PSL33GoodSets IrreducibleEndCohomology
open RepresentationCohomologyAlternative

/-- A statement about actual irreducible representations over algebraically
closed fields, to be proved from the seven explicit simple models. -/
def ClosedModuleBound : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L Q V) [ρ.IsIrreducible]
    (g : Q), orderOf g = 13 → Alternative ρ g

/-- No prime-field endomorphism-degree assumption is needed for descent. -/
theorem binaryModuleBound_of_closed (hclosed : ClosedModuleBound) :
    PSLThreeThreeFrattiniLifting.BinaryModuleBound := by
  intro V _ _ _ ρ _ hdual g hg
  exact IrreducibleCorrectionAlternative.descend ρ g hdual
    (hclosed (ClosedField ρ) (ExtendedCarrier ρ) (extended ρ) g hg)

end Kourovka2135.PSLThreeThreeClosedModuleBound
