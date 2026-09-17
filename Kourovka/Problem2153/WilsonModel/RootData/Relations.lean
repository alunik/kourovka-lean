import Kourovka.Problem2153.WilsonModel.RootData.Relations.Inverse00
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Inverse01
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product00
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product01
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product02
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product03
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product04
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product05
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product06
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product07
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product08
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product09
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product10
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product11
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product12
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Product13
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator00
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator01
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator02
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator03
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator04
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator05
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator06
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator07
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator08
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator09
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator10
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator11
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator12
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator13
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Commutator14
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl00
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl01
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl02
import Kourovka.Problem2153.WilsonModel.RootData.Relations.Weyl03

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations
theorem inverse_checked (k : Fin 12) : wordGroup (inverse_lhs k) = wordGroup (inverse_rhs k) := by
  fin_cases k
  · exact inverse_0
  · exact inverse_1
  · exact inverse_2
  · exact inverse_3
  · exact inverse_4
  · exact inverse_5
  · exact inverse_6
  · exact inverse_7
  · exact inverse_8
  · exact inverse_9
  · exact inverse_10
  · exact inverse_11
theorem product_checked (k : Fin 84) : wordGroup (product_lhs k) = wordGroup (product_rhs k) := by
  fin_cases k
  · exact product_0
  · exact product_1
  · exact product_2
  · exact product_3
  · exact product_4
  · exact product_5
  · exact product_6
  · exact product_7
  · exact product_8
  · exact product_9
  · exact product_10
  · exact product_11
  · exact product_12
  · exact product_13
  · exact product_14
  · exact product_15
  · exact product_16
  · exact product_17
  · exact product_18
  · exact product_19
  · exact product_20
  · exact product_21
  · exact product_22
  · exact product_23
  · exact product_24
  · exact product_25
  · exact product_26
  · exact product_27
  · exact product_28
  · exact product_29
  · exact product_30
  · exact product_31
  · exact product_32
  · exact product_33
  · exact product_34
  · exact product_35
  · exact product_36
  · exact product_37
  · exact product_38
  · exact product_39
  · exact product_40
  · exact product_41
  · exact product_42
  · exact product_43
  · exact product_44
  · exact product_45
  · exact product_46
  · exact product_47
  · exact product_48
  · exact product_49
  · exact product_50
  · exact product_51
  · exact product_52
  · exact product_53
  · exact product_54
  · exact product_55
  · exact product_56
  · exact product_57
  · exact product_58
  · exact product_59
  · exact product_60
  · exact product_61
  · exact product_62
  · exact product_63
  · exact product_64
  · exact product_65
  · exact product_66
  · exact product_67
  · exact product_68
  · exact product_69
  · exact product_70
  · exact product_71
  · exact product_72
  · exact product_73
  · exact product_74
  · exact product_75
  · exact product_76
  · exact product_77
  · exact product_78
  · exact product_79
  · exact product_80
  · exact product_81
  · exact product_82
  · exact product_83
theorem commutator_checked (k : Fin 90) : wordGroup (commutator_lhs k) = wordGroup (commutator_rhs k) := by
  fin_cases k
  · exact commutator_0
  · exact commutator_1
  · exact commutator_2
  · exact commutator_3
  · exact commutator_4
  · exact commutator_5
  · exact commutator_6
  · exact commutator_7
  · exact commutator_8
  · exact commutator_9
  · exact commutator_10
  · exact commutator_11
  · exact commutator_12
  · exact commutator_13
  · exact commutator_14
  · exact commutator_15
  · exact commutator_16
  · exact commutator_17
  · exact commutator_18
  · exact commutator_19
  · exact commutator_20
  · exact commutator_21
  · exact commutator_22
  · exact commutator_23
  · exact commutator_24
  · exact commutator_25
  · exact commutator_26
  · exact commutator_27
  · exact commutator_28
  · exact commutator_29
  · exact commutator_30
  · exact commutator_31
  · exact commutator_32
  · exact commutator_33
  · exact commutator_34
  · exact commutator_35
  · exact commutator_36
  · exact commutator_37
  · exact commutator_38
  · exact commutator_39
  · exact commutator_40
  · exact commutator_41
  · exact commutator_42
  · exact commutator_43
  · exact commutator_44
  · exact commutator_45
  · exact commutator_46
  · exact commutator_47
  · exact commutator_48
  · exact commutator_49
  · exact commutator_50
  · exact commutator_51
  · exact commutator_52
  · exact commutator_53
  · exact commutator_54
  · exact commutator_55
  · exact commutator_56
  · exact commutator_57
  · exact commutator_58
  · exact commutator_59
  · exact commutator_60
  · exact commutator_61
  · exact commutator_62
  · exact commutator_63
  · exact commutator_64
  · exact commutator_65
  · exact commutator_66
  · exact commutator_67
  · exact commutator_68
  · exact commutator_69
  · exact commutator_70
  · exact commutator_71
  · exact commutator_72
  · exact commutator_73
  · exact commutator_74
  · exact commutator_75
  · exact commutator_76
  · exact commutator_77
  · exact commutator_78
  · exact commutator_79
  · exact commutator_80
  · exact commutator_81
  · exact commutator_82
  · exact commutator_83
  · exact commutator_84
  · exact commutator_85
  · exact commutator_86
  · exact commutator_87
  · exact commutator_88
  · exact commutator_89
theorem weyl_checked (k : Fin 21) : wordGroup (weyl_lhs k) = wordGroup (weyl_rhs k) := by
  fin_cases k
  · exact weyl_0
  · exact weyl_1
  · exact weyl_2
  · exact weyl_3
  · exact weyl_4
  · exact weyl_5
  · exact weyl_6
  · exact weyl_7
  · exact weyl_8
  · exact weyl_9
  · exact weyl_10
  · exact weyl_11
  · exact weyl_12
  · exact weyl_13
  · exact weyl_14
  · exact weyl_15
  · exact weyl_16
  · exact weyl_17
  · exact weyl_18
  · exact weyl_19
  · exact weyl_20
end Kourovka.Problem2153.WilsonModel.RootData.Relations
