import Kourovka.Problem2153.RankOne.Cells.R00
import Kourovka.Problem2153.RankOne.Cells.R01
import Kourovka.Problem2153.RankOne.Cells.R02
import Kourovka.Problem2153.RankOne.Cells.R03
import Kourovka.Problem2153.RankOne.Cells.R04
import Kourovka.Problem2153.RankOne.Cells.R05
import Kourovka.Problem2153.RankOne.Cells.R06
import Kourovka.Problem2153.RankOne.Cells.R07
import Kourovka.Problem2153.RankOne.Cells.R08
import Kourovka.Problem2153.RankOne.Cells.R09
import Kourovka.Problem2153.RankOne.Cells.R10
import Kourovka.Problem2153.RankOne.Cells.S00
import Kourovka.Problem2153.RankOne.Cells.S01

set_option autoImplicit false
namespace Kourovka.Problem2153.RootSystem.RankOne
theorem r_cell_checked (k : Fin 63) :
    wordGroup (r_lhs k) = wordGroup (r_rhs k) := by
  fin_cases k
  · exact r_cell_0
  · exact r_cell_1
  · exact r_cell_2
  · exact r_cell_3
  · exact r_cell_4
  · exact r_cell_5
  · exact r_cell_6
  · exact r_cell_7
  · exact r_cell_8
  · exact r_cell_9
  · exact r_cell_10
  · exact r_cell_11
  · exact r_cell_12
  · exact r_cell_13
  · exact r_cell_14
  · exact r_cell_15
  · exact r_cell_16
  · exact r_cell_17
  · exact r_cell_18
  · exact r_cell_19
  · exact r_cell_20
  · exact r_cell_21
  · exact r_cell_22
  · exact r_cell_23
  · exact r_cell_24
  · exact r_cell_25
  · exact r_cell_26
  · exact r_cell_27
  · exact r_cell_28
  · exact r_cell_29
  · exact r_cell_30
  · exact r_cell_31
  · exact r_cell_32
  · exact r_cell_33
  · exact r_cell_34
  · exact r_cell_35
  · exact r_cell_36
  · exact r_cell_37
  · exact r_cell_38
  · exact r_cell_39
  · exact r_cell_40
  · exact r_cell_41
  · exact r_cell_42
  · exact r_cell_43
  · exact r_cell_44
  · exact r_cell_45
  · exact r_cell_46
  · exact r_cell_47
  · exact r_cell_48
  · exact r_cell_49
  · exact r_cell_50
  · exact r_cell_51
  · exact r_cell_52
  · exact r_cell_53
  · exact r_cell_54
  · exact r_cell_55
  · exact r_cell_56
  · exact r_cell_57
  · exact r_cell_58
  · exact r_cell_59
  · exact r_cell_60
  · exact r_cell_61
  · exact r_cell_62
theorem s_cell_checked (k : Fin 7) :
    wordGroup (s_lhs k) = wordGroup (s_rhs k) := by
  fin_cases k
  · exact s_cell_0
  · exact s_cell_1
  · exact s_cell_2
  · exact s_cell_3
  · exact s_cell_4
  · exact s_cell_5
  · exact s_cell_6
end Kourovka.Problem2153.RootSystem.RankOne
