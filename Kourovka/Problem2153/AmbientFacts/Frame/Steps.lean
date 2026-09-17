import Kourovka.Problem2153.AmbientFacts.Frame.Data
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel.Frame
open Field8 F8

theorem generator_alignment : ∀ j : Fin 6, (generatorMatrix j).transpose = Sparse.eval (generatorColumns j) := by decide +kernel

theorem trace0_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word0 k)) (trace0 k.castSucc) = trace0 k.succ := by decide +kernel

theorem trace1_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word1 k)) (trace1 k.castSucc) = trace1 k.succ := by decide +kernel

theorem trace2_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word2 k)) (trace2 k.castSucc) = trace2 k.succ := by decide +kernel

theorem trace3_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word3 k)) (trace3 k.castSucc) = trace3 k.succ := by decide +kernel

theorem trace4_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word4 k)) (trace4 k.castSucc) = trace4 k.succ := by decide +kernel

theorem trace5_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word5 k)) (trace5 k.castSucc) = trace5 k.succ := by decide +kernel

theorem trace6_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word6 k)) (trace6 k.castSucc) = trace6 k.succ := by decide +kernel

theorem trace7_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word7 k)) (trace7 k.castSucc) = trace7 k.succ := by decide +kernel

theorem trace8_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word8 k)) (trace8 k.castSucc) = trace8 k.succ := by decide +kernel

theorem trace9_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word9 k)) (trace9 k.castSucc) = trace9 k.succ := by decide +kernel

theorem trace10_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word10 k)) (trace10 k.castSucc) = trace10 k.succ := by decide +kernel

theorem trace11_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word11 k)) (trace11 k.castSucc) = trace11 k.succ := by decide +kernel

theorem trace12_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word12 k)) (trace12 k.castSucc) = trace12 k.succ := by decide +kernel

theorem trace13_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word13 k)) (trace13 k.castSucc) = trace13 k.succ := by decide +kernel

theorem trace14_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word14 k)) (trace14 k.castSucc) = trace14 k.succ := by decide +kernel

theorem trace15_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word15 k)) (trace15 k.castSucc) = trace15 k.succ := by decide +kernel

theorem trace16_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word16 k)) (trace16 k.castSucc) = trace16 k.succ := by decide +kernel

theorem trace17_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word17 k)) (trace17 k.castSucc) = trace17 k.succ := by decide +kernel

theorem trace18_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word18 k)) (trace18 k.castSucc) = trace18 k.succ := by decide +kernel

theorem trace19_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word19 k)) (trace19 k.castSucc) = trace19 k.succ := by decide +kernel

theorem trace20_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word20 k)) (trace20 k.castSucc) = trace20 k.succ := by decide +kernel

theorem trace21_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word21 k)) (trace21 k.castSucc) = trace21 k.succ := by decide +kernel

theorem trace22_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word22 k)) (trace22 k.castSucc) = trace22 k.succ := by decide +kernel

theorem trace23_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word23 k)) (trace23 k.castSucc) = trace23 k.succ := by decide +kernel

theorem trace24_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word24 k)) (trace24 k.castSucc) = trace24 k.succ := by decide +kernel

theorem trace25_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word25 k)) (trace25 k.castSucc) = trace25 k.succ := by decide +kernel

theorem trace26_step : ∀ k : Fin 48, sparseRowAction (generatorColumns (word26 k)) (trace26 k.castSucc) = trace26 k.succ := by decide +kernel

theorem trace_steps (j : Fin 27) (k : Fin 48) :
    sparseRowAction (generatorColumns (words j k)) (traces j k.castSucc) = traces j k.succ := by
  fin_cases j
  · exact trace0_step k
  · exact trace1_step k
  · exact trace2_step k
  · exact trace3_step k
  · exact trace4_step k
  · exact trace5_step k
  · exact trace6_step k
  · exact trace7_step k
  · exact trace8_step k
  · exact trace9_step k
  · exact trace10_step k
  · exact trace11_step k
  · exact trace12_step k
  · exact trace13_step k
  · exact trace14_step k
  · exact trace15_step k
  · exact trace16_step k
  · exact trace17_step k
  · exact trace18_step k
  · exact trace19_step k
  · exact trace20_step k
  · exact trace21_step k
  · exact trace22_step k
  · exact trace23_step k
  · exact trace24_step k
  · exact trace25_step k
  · exact trace26_step k


#print axioms trace_steps
end Kourovka.Problem2153.WilsonModel.Frame
