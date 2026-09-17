import Kourovka.Problem2153.Simple
import Kourovka.Problem2153.Endpoint

set_option autoImplicit false
namespace Kourovka.Problem2153

/-- The concrete transposition acts on the entire ambient conjugacy class. -/
theorem whole_class_counterexample :
    PreservesColour 2 Endpoint.classSwap ∧ PreservesColour 3 Endpoint.classSwap ∧
      ¬ PreservesAllColours Endpoint.classSwap :=
  Endpoint.classSwap_counterexample_of_coverage RootSystem.BNPair.uhwu_coverage

/-- Negative answer to the universal assertion in Kourovka Notebook Problem 21.53. -/
theorem not_statement : ¬ Statement.{0} :=
  Endpoint.not_statement_of_coverage RootSystem.BNPair.uhwu_coverage

#print axioms whole_class_counterexample
#print axioms not_statement
end Kourovka.Problem2153
