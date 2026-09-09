import Kourovka.Problems.P21_99.Proof.Instance
import Kourovka.Problems.P21_99.Proof.Transfer

/-! A counterexample to Peter Müller's Problem 21.99. -/

namespace Kourovka.P21_99

/-- The notebook assertion is false: in the concrete finite transitive action,
every element transporting `source` to `target` has exactly one fixed point. -/
theorem not_notebookStatement : ¬ NotebookStatement :=
  not_notebookStatement_of_action source target source_ne_target transporter_unique

end Kourovka.P21_99
