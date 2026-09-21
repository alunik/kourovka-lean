import Kourovka2135.SuzukiEightCoverCodeMatrices

/-! Canonical PC normal-form values, with every product checked in the kernel. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Kourovka2135.SuzukiEightCoverCodeForms
open SuzukiEightCodeField SuzukiEightCoverCodeMatrices

def form000Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form000 : UnitMatrix := 1
theorem form000_val : form000.val = form000Matrix := by decide +kernel

def form001Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form001 : UnitMatrix := pc7
theorem form001_val : form001.val = form001Matrix := rfl

def form002Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form002 : UnitMatrix := pc6
theorem form002_val : form002.val = form002Matrix := rfl

def form003Matrix : M := !![ofCode 1, ofCode 0, ofCode 0, ofCode 0; ofCode 0, ofCode 1, ofCode 0, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form003Step : form002Matrix * pc7Matrix = form003Matrix := by decide +kernel
def form003 : UnitMatrix := form002 * pc7
theorem form003_val : form003.val = form003Matrix := by
  change form002.val * pc7Matrix = form003Matrix
  rw [form002_val]
  exact form003Step

def form004Matrix : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form004 : UnitMatrix := pc5
theorem form004_val : form004.val = form004Matrix := rfl

def form005Matrix : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form005Step : form004Matrix * pc7Matrix = form005Matrix := by decide +kernel
def form005 : UnitMatrix := form004 * pc7
theorem form005_val : form005.val = form005Matrix := by
  change form004.val * pc7Matrix = form005Matrix
  rw [form004_val]
  exact form005Step

def form006Matrix : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form006Step : form004Matrix * pc6Matrix = form006Matrix := by decide +kernel
def form006 : UnitMatrix := form004 * pc6
theorem form006_val : form006.val = form006Matrix := by
  change form004.val * pc6Matrix = form006Matrix
  rw [form004_val]
  exact form006Step

def form007Matrix : M := !![ofCode 1, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form007Step : form006Matrix * pc7Matrix = form007Matrix := by decide +kernel
def form007 : UnitMatrix := form006 * pc7
theorem form007_val : form007.val = form007Matrix := by
  change form006.val * pc7Matrix = form007Matrix
  rw [form006_val]
  exact form007Step

def form008Matrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form008 : UnitMatrix := pc4
theorem form008_val : form008.val = form008Matrix := rfl

def form009Matrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form009Step : form008Matrix * pc7Matrix = form009Matrix := by decide +kernel
def form009 : UnitMatrix := form008 * pc7
theorem form009_val : form009.val = form009Matrix := by
  change form008.val * pc7Matrix = form009Matrix
  rw [form008_val]
  exact form009Step

def form010Matrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form010Step : form008Matrix * pc6Matrix = form010Matrix := by decide +kernel
def form010 : UnitMatrix := form008 * pc6
theorem form010_val : form010.val = form010Matrix := by
  change form008.val * pc6Matrix = form010Matrix
  rw [form008_val]
  exact form010Step

def form011Matrix : M := !![ofCode 1, ofCode 0, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 0, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form011Step : form010Matrix * pc7Matrix = form011Matrix := by decide +kernel
def form011 : UnitMatrix := form010 * pc7
theorem form011_val : form011.val = form011Matrix := by
  change form010.val * pc7Matrix = form011Matrix
  rw [form010_val]
  exact form011Step

def form012Matrix : M := !![ofCode 1, ofCode 0, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form012Step : form008Matrix * pc5Matrix = form012Matrix := by decide +kernel
def form012 : UnitMatrix := form008 * pc5
theorem form012_val : form012.val = form012Matrix := by
  change form008.val * pc5Matrix = form012Matrix
  rw [form008_val]
  exact form012Step

def form013Matrix : M := !![ofCode 1, ofCode 0, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form013Step : form012Matrix * pc7Matrix = form013Matrix := by decide +kernel
def form013 : UnitMatrix := form012 * pc7
theorem form013_val : form013.val = form013Matrix := by
  change form012.val * pc7Matrix = form013Matrix
  rw [form012_val]
  exact form013Step

def form014Matrix : M := !![ofCode 1, ofCode 0, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form014Step : form012Matrix * pc6Matrix = form014Matrix := by decide +kernel
def form014 : UnitMatrix := form012 * pc6
theorem form014_val : form014.val = form014Matrix := by
  change form012.val * pc6Matrix = form014Matrix
  rw [form012_val]
  exact form014Step

def form015Matrix : M := !![ofCode 1, ofCode 0, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 0, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form015Step : form014Matrix * pc7Matrix = form015Matrix := by decide +kernel
def form015 : UnitMatrix := form014 * pc7
theorem form015_val : form015.val = form015Matrix := by
  change form014.val * pc7Matrix = form015Matrix
  rw [form014_val]
  exact form015Step

def form016Matrix : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form016 : UnitMatrix := pc3
theorem form016_val : form016.val = form016Matrix := rfl

def form017Matrix : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form017Step : form016Matrix * pc7Matrix = form017Matrix := by decide +kernel
def form017 : UnitMatrix := form016 * pc7
theorem form017_val : form017.val = form017Matrix := by
  change form016.val * pc7Matrix = form017Matrix
  rw [form016_val]
  exact form017Step

def form018Matrix : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form018Step : form016Matrix * pc6Matrix = form018Matrix := by decide +kernel
def form018 : UnitMatrix := form016 * pc6
theorem form018_val : form018.val = form018Matrix := by
  change form016.val * pc6Matrix = form018Matrix
  rw [form016_val]
  exact form018Step

def form019Matrix : M := !![ofCode 1, ofCode 0, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 0, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form019Step : form018Matrix * pc7Matrix = form019Matrix := by decide +kernel
def form019 : UnitMatrix := form018 * pc7
theorem form019_val : form019.val = form019Matrix := by
  change form018.val * pc7Matrix = form019Matrix
  rw [form018_val]
  exact form019Step

def form020Matrix : M := !![ofCode 1, ofCode 0, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 0, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form020Step : form016Matrix * pc5Matrix = form020Matrix := by decide +kernel
def form020 : UnitMatrix := form016 * pc5
theorem form020_val : form020.val = form020Matrix := by
  change form016.val * pc5Matrix = form020Matrix
  rw [form016_val]
  exact form020Step

def form021Matrix : M := !![ofCode 1, ofCode 0, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 0, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form021Step : form020Matrix * pc7Matrix = form021Matrix := by decide +kernel
def form021 : UnitMatrix := form020 * pc7
theorem form021_val : form021.val = form021Matrix := by
  change form020.val * pc7Matrix = form021Matrix
  rw [form020_val]
  exact form021Step

def form022Matrix : M := !![ofCode 1, ofCode 0, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 0, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form022Step : form020Matrix * pc6Matrix = form022Matrix := by decide +kernel
def form022 : UnitMatrix := form020 * pc6
theorem form022_val : form022.val = form022Matrix := by
  change form020.val * pc6Matrix = form022Matrix
  rw [form020_val]
  exact form022Step

def form023Matrix : M := !![ofCode 1, ofCode 0, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 0, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form023Step : form022Matrix * pc7Matrix = form023Matrix := by decide +kernel
def form023 : UnitMatrix := form022 * pc7
theorem form023_val : form023.val = form023Matrix := by
  change form022.val * pc7Matrix = form023Matrix
  rw [form022_val]
  exact form023Step

def form024Matrix : M := !![ofCode 1, ofCode 0, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form024Step : form016Matrix * pc4Matrix = form024Matrix := by decide +kernel
def form024 : UnitMatrix := form016 * pc4
theorem form024_val : form024.val = form024Matrix := by
  change form016.val * pc4Matrix = form024Matrix
  rw [form016_val]
  exact form024Step

def form025Matrix : M := !![ofCode 1, ofCode 0, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form025Step : form024Matrix * pc7Matrix = form025Matrix := by decide +kernel
def form025 : UnitMatrix := form024 * pc7
theorem form025_val : form025.val = form025Matrix := by
  change form024.val * pc7Matrix = form025Matrix
  rw [form024_val]
  exact form025Step

def form026Matrix : M := !![ofCode 1, ofCode 0, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form026Step : form024Matrix * pc6Matrix = form026Matrix := by decide +kernel
def form026 : UnitMatrix := form024 * pc6
theorem form026_val : form026.val = form026Matrix := by
  change form024.val * pc6Matrix = form026Matrix
  rw [form024_val]
  exact form026Step

def form027Matrix : M := !![ofCode 1, ofCode 0, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 0, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form027Step : form026Matrix * pc7Matrix = form027Matrix := by decide +kernel
def form027 : UnitMatrix := form026 * pc7
theorem form027_val : form027.val = form027Matrix := by
  change form026.val * pc7Matrix = form027Matrix
  rw [form026_val]
  exact form027Step

def form028Matrix : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 0, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form028Step : form024Matrix * pc5Matrix = form028Matrix := by decide +kernel
def form028 : UnitMatrix := form024 * pc5
theorem form028_val : form028.val = form028Matrix := by
  change form024.val * pc5Matrix = form028Matrix
  rw [form024_val]
  exact form028Step

def form029Matrix : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 0, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form029Step : form028Matrix * pc7Matrix = form029Matrix := by decide +kernel
def form029 : UnitMatrix := form028 * pc7
theorem form029_val : form029.val = form029Matrix := by
  change form028.val * pc7Matrix = form029Matrix
  rw [form028_val]
  exact form029Step

def form030Matrix : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 0, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form030Step : form028Matrix * pc6Matrix = form030Matrix := by decide +kernel
def form030 : UnitMatrix := form028 * pc6
theorem form030_val : form030.val = form030Matrix := by
  change form028.val * pc6Matrix = form030Matrix
  rw [form028_val]
  exact form030Step

def form031Matrix : M := !![ofCode 1, ofCode 0, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 0, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form031Step : form030Matrix * pc7Matrix = form031Matrix := by decide +kernel
def form031 : UnitMatrix := form030 * pc7
theorem form031_val : form031.val = form031Matrix := by
  change form030.val * pc7Matrix = form031Matrix
  rw [form030_val]
  exact form031Step

def form032Matrix : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form032 : UnitMatrix := pc2
theorem form032_val : form032.val = form032Matrix := rfl

def form033Matrix : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form033Step : form032Matrix * pc7Matrix = form033Matrix := by decide +kernel
def form033 : UnitMatrix := form032 * pc7
theorem form033_val : form033.val = form033Matrix := by
  change form032.val * pc7Matrix = form033Matrix
  rw [form032_val]
  exact form033Step

def form034Matrix : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form034Step : form032Matrix * pc6Matrix = form034Matrix := by decide +kernel
def form034 : UnitMatrix := form032 * pc6
theorem form034_val : form034.val = form034Matrix := by
  change form032.val * pc6Matrix = form034Matrix
  rw [form032_val]
  exact form034Step

def form035Matrix : M := !![ofCode 1, ofCode 1, ofCode 0, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form035Step : form034Matrix * pc7Matrix = form035Matrix := by decide +kernel
def form035 : UnitMatrix := form034 * pc7
theorem form035_val : form035.val = form035Matrix := by
  change form034.val * pc7Matrix = form035Matrix
  rw [form034_val]
  exact form035Step

def form036Matrix : M := !![ofCode 1, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form036Step : form032Matrix * pc5Matrix = form036Matrix := by decide +kernel
def form036 : UnitMatrix := form032 * pc5
theorem form036_val : form036.val = form036Matrix := by
  change form032.val * pc5Matrix = form036Matrix
  rw [form032_val]
  exact form036Step

def form037Matrix : M := !![ofCode 1, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form037Step : form036Matrix * pc7Matrix = form037Matrix := by decide +kernel
def form037 : UnitMatrix := form036 * pc7
theorem form037_val : form037.val = form037Matrix := by
  change form036.val * pc7Matrix = form037Matrix
  rw [form036_val]
  exact form037Step

def form038Matrix : M := !![ofCode 1, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form038Step : form036Matrix * pc6Matrix = form038Matrix := by decide +kernel
def form038 : UnitMatrix := form036 * pc6
theorem form038_val : form038.val = form038Matrix := by
  change form036.val * pc6Matrix = form038Matrix
  rw [form036_val]
  exact form038Step

def form039Matrix : M := !![ofCode 1, ofCode 1, ofCode 1, ofCode 1; ofCode 0, ofCode 1, ofCode 1, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form039Step : form038Matrix * pc7Matrix = form039Matrix := by decide +kernel
def form039 : UnitMatrix := form038 * pc7
theorem form039_val : form039.val = form039Matrix := by
  change form038.val * pc7Matrix = form039Matrix
  rw [form038_val]
  exact form039Step

def form040Matrix : M := !![ofCode 1, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form040Step : form032Matrix * pc4Matrix = form040Matrix := by decide +kernel
def form040 : UnitMatrix := form032 * pc4
theorem form040_val : form040.val = form040Matrix := by
  change form032.val * pc4Matrix = form040Matrix
  rw [form032_val]
  exact form040Step

def form041Matrix : M := !![ofCode 1, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form041Step : form040Matrix * pc7Matrix = form041Matrix := by decide +kernel
def form041 : UnitMatrix := form040 * pc7
theorem form041_val : form041.val = form041Matrix := by
  change form040.val * pc7Matrix = form041Matrix
  rw [form040_val]
  exact form041Step

def form042Matrix : M := !![ofCode 1, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form042Step : form040Matrix * pc6Matrix = form042Matrix := by decide +kernel
def form042 : UnitMatrix := form040 * pc6
theorem form042_val : form042.val = form042Matrix := by
  change form040.val * pc6Matrix = form042Matrix
  rw [form040_val]
  exact form042Step

def form043Matrix : M := !![ofCode 1, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form043Step : form042Matrix * pc7Matrix = form043Matrix := by decide +kernel
def form043 : UnitMatrix := form042 * pc7
theorem form043_val : form043.val = form043Matrix := by
  change form042.val * pc7Matrix = form043Matrix
  rw [form042_val]
  exact form043Step

def form044Matrix : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form044Step : form040Matrix * pc5Matrix = form044Matrix := by decide +kernel
def form044 : UnitMatrix := form040 * pc5
theorem form044_val : form044.val = form044Matrix := by
  change form040.val * pc5Matrix = form044Matrix
  rw [form040_val]
  exact form044Step

def form045Matrix : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form045Step : form044Matrix * pc7Matrix = form045Matrix := by decide +kernel
def form045 : UnitMatrix := form044 * pc7
theorem form045_val : form045.val = form045Matrix := by
  change form044.val * pc7Matrix = form045Matrix
  rw [form044_val]
  exact form045Step

def form046Matrix : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form046Step : form044Matrix * pc6Matrix = form046Matrix := by decide +kernel
def form046 : UnitMatrix := form044 * pc6
theorem form046_val : form046.val = form046Matrix := by
  change form044.val * pc6Matrix = form046Matrix
  rw [form044_val]
  exact form046Step

def form047Matrix : M := !![ofCode 1, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form047Step : form046Matrix * pc7Matrix = form047Matrix := by decide +kernel
def form047 : UnitMatrix := form046 * pc7
theorem form047_val : form047.val = form047Matrix := by
  change form046.val * pc7Matrix = form047Matrix
  rw [form046_val]
  exact form047Step

def form048Matrix : M := !![ofCode 1, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form048Step : form032Matrix * pc3Matrix = form048Matrix := by decide +kernel
def form048 : UnitMatrix := form032 * pc3
theorem form048_val : form048.val = form048Matrix := by
  change form032.val * pc3Matrix = form048Matrix
  rw [form032_val]
  exact form048Step

def form049Matrix : M := !![ofCode 1, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form049Step : form048Matrix * pc7Matrix = form049Matrix := by decide +kernel
def form049 : UnitMatrix := form048 * pc7
theorem form049_val : form049.val = form049Matrix := by
  change form048.val * pc7Matrix = form049Matrix
  rw [form048_val]
  exact form049Step

def form050Matrix : M := !![ofCode 1, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form050Step : form048Matrix * pc6Matrix = form050Matrix := by decide +kernel
def form050 : UnitMatrix := form048 * pc6
theorem form050_val : form050.val = form050Matrix := by
  change form048.val * pc6Matrix = form050Matrix
  rw [form048_val]
  exact form050Step

def form051Matrix : M := !![ofCode 1, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form051Step : form050Matrix * pc7Matrix = form051Matrix := by decide +kernel
def form051 : UnitMatrix := form050 * pc7
theorem form051_val : form051.val = form051Matrix := by
  change form050.val * pc7Matrix = form051Matrix
  rw [form050_val]
  exact form051Step

def form052Matrix : M := !![ofCode 1, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form052Step : form048Matrix * pc5Matrix = form052Matrix := by decide +kernel
def form052 : UnitMatrix := form048 * pc5
theorem form052_val : form052.val = form052Matrix := by
  change form048.val * pc5Matrix = form052Matrix
  rw [form048_val]
  exact form052Step

def form053Matrix : M := !![ofCode 1, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form053Step : form052Matrix * pc7Matrix = form053Matrix := by decide +kernel
def form053 : UnitMatrix := form052 * pc7
theorem form053_val : form053.val = form053Matrix := by
  change form052.val * pc7Matrix = form053Matrix
  rw [form052_val]
  exact form053Step

def form054Matrix : M := !![ofCode 1, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form054Step : form052Matrix * pc6Matrix = form054Matrix := by decide +kernel
def form054 : UnitMatrix := form052 * pc6
theorem form054_val : form054.val = form054Matrix := by
  change form052.val * pc6Matrix = form054Matrix
  rw [form052_val]
  exact form054Step

def form055Matrix : M := !![ofCode 1, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form055Step : form054Matrix * pc7Matrix = form055Matrix := by decide +kernel
def form055 : UnitMatrix := form054 * pc7
theorem form055_val : form055.val = form055Matrix := by
  change form054.val * pc7Matrix = form055Matrix
  rw [form054_val]
  exact form055Step

def form056Matrix : M := !![ofCode 1, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form056Step : form048Matrix * pc4Matrix = form056Matrix := by decide +kernel
def form056 : UnitMatrix := form048 * pc4
theorem form056_val : form056.val = form056Matrix := by
  change form048.val * pc4Matrix = form056Matrix
  rw [form048_val]
  exact form056Step

def form057Matrix : M := !![ofCode 1, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form057Step : form056Matrix * pc7Matrix = form057Matrix := by decide +kernel
def form057 : UnitMatrix := form056 * pc7
theorem form057_val : form057.val = form057Matrix := by
  change form056.val * pc7Matrix = form057Matrix
  rw [form056_val]
  exact form057Step

def form058Matrix : M := !![ofCode 1, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form058Step : form056Matrix * pc6Matrix = form058Matrix := by decide +kernel
def form058 : UnitMatrix := form056 * pc6
theorem form058_val : form058.val = form058Matrix := by
  change form056.val * pc6Matrix = form058Matrix
  rw [form056_val]
  exact form058Step

def form059Matrix : M := !![ofCode 1, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form059Step : form058Matrix * pc7Matrix = form059Matrix := by decide +kernel
def form059 : UnitMatrix := form058 * pc7
theorem form059_val : form059.val = form059Matrix := by
  change form058.val * pc7Matrix = form059Matrix
  rw [form058_val]
  exact form059Step

def form060Matrix : M := !![ofCode 1, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form060Step : form056Matrix * pc5Matrix = form060Matrix := by decide +kernel
def form060 : UnitMatrix := form056 * pc5
theorem form060_val : form060.val = form060Matrix := by
  change form056.val * pc5Matrix = form060Matrix
  rw [form056_val]
  exact form060Step

def form061Matrix : M := !![ofCode 1, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form061Step : form060Matrix * pc7Matrix = form061Matrix := by decide +kernel
def form061 : UnitMatrix := form060 * pc7
theorem form061_val : form061.val = form061Matrix := by
  change form060.val * pc7Matrix = form061Matrix
  rw [form060_val]
  exact form061Step

def form062Matrix : M := !![ofCode 1, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form062Step : form060Matrix * pc6Matrix = form062Matrix := by decide +kernel
def form062 : UnitMatrix := form060 * pc6
theorem form062_val : form062.val = form062Matrix := by
  change form060.val * pc6Matrix = form062Matrix
  rw [form060_val]
  exact form062Step

def form063Matrix : M := !![ofCode 1, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 1; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form063Step : form062Matrix * pc7Matrix = form063Matrix := by decide +kernel
def form063 : UnitMatrix := form062 * pc7
theorem form063_val : form063.val = form063Matrix := by
  change form062.val * pc7Matrix = form063Matrix
  rw [form062_val]
  exact form063Step

def form064Matrix : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form064 : UnitMatrix := pc1
theorem form064_val : form064.val = form064Matrix := rfl

def form065Matrix : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form065Step : form064Matrix * pc7Matrix = form065Matrix := by decide +kernel
def form065 : UnitMatrix := form064 * pc7
theorem form065_val : form065.val = form065Matrix := by
  change form064.val * pc7Matrix = form065Matrix
  rw [form064_val]
  exact form065Step

def form066Matrix : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form066Step : form064Matrix * pc6Matrix = form066Matrix := by decide +kernel
def form066 : UnitMatrix := form064 * pc6
theorem form066_val : form066.val = form066Matrix := by
  change form064.val * pc6Matrix = form066Matrix
  rw [form064_val]
  exact form066Step

def form067Matrix : M := !![ofCode 1, ofCode 2, ofCode 0, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form067Step : form066Matrix * pc7Matrix = form067Matrix := by decide +kernel
def form067 : UnitMatrix := form066 * pc7
theorem form067_val : form067.val = form067Matrix := by
  change form066.val * pc7Matrix = form067Matrix
  rw [form066_val]
  exact form067Step

def form068Matrix : M := !![ofCode 1, ofCode 2, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form068Step : form064Matrix * pc5Matrix = form068Matrix := by decide +kernel
def form068 : UnitMatrix := form064 * pc5
theorem form068_val : form068.val = form068Matrix := by
  change form064.val * pc5Matrix = form068Matrix
  rw [form064_val]
  exact form068Step

def form069Matrix : M := !![ofCode 1, ofCode 2, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form069Step : form068Matrix * pc7Matrix = form069Matrix := by decide +kernel
def form069 : UnitMatrix := form068 * pc7
theorem form069_val : form069.val = form069Matrix := by
  change form068.val * pc7Matrix = form069Matrix
  rw [form068_val]
  exact form069Step

def form070Matrix : M := !![ofCode 1, ofCode 2, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form070Step : form068Matrix * pc6Matrix = form070Matrix := by decide +kernel
def form070 : UnitMatrix := form068 * pc6
theorem form070_val : form070.val = form070Matrix := by
  change form068.val * pc6Matrix = form070Matrix
  rw [form068_val]
  exact form070Step

def form071Matrix : M := !![ofCode 1, ofCode 2, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form071Step : form070Matrix * pc7Matrix = form071Matrix := by decide +kernel
def form071 : UnitMatrix := form070 * pc7
theorem form071_val : form071.val = form071Matrix := by
  change form070.val * pc7Matrix = form071Matrix
  rw [form070_val]
  exact form071Step

def form072Matrix : M := !![ofCode 1, ofCode 2, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form072Step : form064Matrix * pc4Matrix = form072Matrix := by decide +kernel
def form072 : UnitMatrix := form064 * pc4
theorem form072_val : form072.val = form072Matrix := by
  change form064.val * pc4Matrix = form072Matrix
  rw [form064_val]
  exact form072Step

def form073Matrix : M := !![ofCode 1, ofCode 2, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form073Step : form072Matrix * pc7Matrix = form073Matrix := by decide +kernel
def form073 : UnitMatrix := form072 * pc7
theorem form073_val : form073.val = form073Matrix := by
  change form072.val * pc7Matrix = form073Matrix
  rw [form072_val]
  exact form073Step

def form074Matrix : M := !![ofCode 1, ofCode 2, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form074Step : form072Matrix * pc6Matrix = form074Matrix := by decide +kernel
def form074 : UnitMatrix := form072 * pc6
theorem form074_val : form074.val = form074Matrix := by
  change form072.val * pc6Matrix = form074Matrix
  rw [form072_val]
  exact form074Step

def form075Matrix : M := !![ofCode 1, ofCode 2, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form075Step : form074Matrix * pc7Matrix = form075Matrix := by decide +kernel
def form075 : UnitMatrix := form074 * pc7
theorem form075_val : form075.val = form075Matrix := by
  change form074.val * pc7Matrix = form075Matrix
  rw [form074_val]
  exact form075Step

def form076Matrix : M := !![ofCode 1, ofCode 2, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form076Step : form072Matrix * pc5Matrix = form076Matrix := by decide +kernel
def form076 : UnitMatrix := form072 * pc5
theorem form076_val : form076.val = form076Matrix := by
  change form072.val * pc5Matrix = form076Matrix
  rw [form072_val]
  exact form076Step

def form077Matrix : M := !![ofCode 1, ofCode 2, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form077Step : form076Matrix * pc7Matrix = form077Matrix := by decide +kernel
def form077 : UnitMatrix := form076 * pc7
theorem form077_val : form077.val = form077Matrix := by
  change form076.val * pc7Matrix = form077Matrix
  rw [form076_val]
  exact form077Step

def form078Matrix : M := !![ofCode 1, ofCode 2, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form078Step : form076Matrix * pc6Matrix = form078Matrix := by decide +kernel
def form078 : UnitMatrix := form076 * pc6
theorem form078_val : form078.val = form078Matrix := by
  change form076.val * pc6Matrix = form078Matrix
  rw [form076_val]
  exact form078Step

def form079Matrix : M := !![ofCode 1, ofCode 2, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form079Step : form078Matrix * pc7Matrix = form079Matrix := by decide +kernel
def form079 : UnitMatrix := form078 * pc7
theorem form079_val : form079.val = form079Matrix := by
  change form078.val * pc7Matrix = form079Matrix
  rw [form078_val]
  exact form079Step

def form080Matrix : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form080Step : form064Matrix * pc3Matrix = form080Matrix := by decide +kernel
def form080 : UnitMatrix := form064 * pc3
theorem form080_val : form080.val = form080Matrix := by
  change form064.val * pc3Matrix = form080Matrix
  rw [form064_val]
  exact form080Step

def form081Matrix : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form081Step : form080Matrix * pc7Matrix = form081Matrix := by decide +kernel
def form081 : UnitMatrix := form080 * pc7
theorem form081_val : form081.val = form081Matrix := by
  change form080.val * pc7Matrix = form081Matrix
  rw [form080_val]
  exact form081Step

def form082Matrix : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form082Step : form080Matrix * pc6Matrix = form082Matrix := by decide +kernel
def form082 : UnitMatrix := form080 * pc6
theorem form082_val : form082.val = form082Matrix := by
  change form080.val * pc6Matrix = form082Matrix
  rw [form080_val]
  exact form082Step

def form083Matrix : M := !![ofCode 1, ofCode 2, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 6, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form083Step : form082Matrix * pc7Matrix = form083Matrix := by decide +kernel
def form083 : UnitMatrix := form082 * pc7
theorem form083_val : form083.val = form083Matrix := by
  change form082.val * pc7Matrix = form083Matrix
  rw [form082_val]
  exact form083Step

def form084Matrix : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form084Step : form080Matrix * pc5Matrix = form084Matrix := by decide +kernel
def form084 : UnitMatrix := form080 * pc5
theorem form084_val : form084.val = form084Matrix := by
  change form080.val * pc5Matrix = form084Matrix
  rw [form080_val]
  exact form084Step

def form085Matrix : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form085Step : form084Matrix * pc7Matrix = form085Matrix := by decide +kernel
def form085 : UnitMatrix := form084 * pc7
theorem form085_val : form085.val = form085Matrix := by
  change form084.val * pc7Matrix = form085Matrix
  rw [form084_val]
  exact form085Step

def form086Matrix : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form086Step : form084Matrix * pc6Matrix = form086Matrix := by decide +kernel
def form086 : UnitMatrix := form084 * pc6
theorem form086_val : form086.val = form086Matrix := by
  change form084.val * pc6Matrix = form086Matrix
  rw [form084_val]
  exact form086Step

def form087Matrix : M := !![ofCode 1, ofCode 2, ofCode 5, ofCode 7; ofCode 0, ofCode 1, ofCode 6, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form087Step : form086Matrix * pc7Matrix = form087Matrix := by decide +kernel
def form087 : UnitMatrix := form086 * pc7
theorem form087_val : form087.val = form087Matrix := by
  change form086.val * pc7Matrix = form087Matrix
  rw [form086_val]
  exact form087Step

def form088Matrix : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form088Step : form080Matrix * pc4Matrix = form088Matrix := by decide +kernel
def form088 : UnitMatrix := form080 * pc4
theorem form088_val : form088.val = form088Matrix := by
  change form080.val * pc4Matrix = form088Matrix
  rw [form080_val]
  exact form088Step

def form089Matrix : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form089Step : form088Matrix * pc7Matrix = form089Matrix := by decide +kernel
def form089 : UnitMatrix := form088 * pc7
theorem form089_val : form089.val = form089Matrix := by
  change form088.val * pc7Matrix = form089Matrix
  rw [form088_val]
  exact form089Step

def form090Matrix : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form090Step : form088Matrix * pc6Matrix = form090Matrix := by decide +kernel
def form090 : UnitMatrix := form088 * pc6
theorem form090_val : form090.val = form090Matrix := by
  change form088.val * pc6Matrix = form090Matrix
  rw [form088_val]
  exact form090Step

def form091Matrix : M := !![ofCode 1, ofCode 2, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 6, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form091Step : form090Matrix * pc7Matrix = form091Matrix := by decide +kernel
def form091 : UnitMatrix := form090 * pc7
theorem form091_val : form091.val = form091Matrix := by
  change form090.val * pc7Matrix = form091Matrix
  rw [form090_val]
  exact form091Step

def form092Matrix : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form092Step : form088Matrix * pc5Matrix = form092Matrix := by decide +kernel
def form092 : UnitMatrix := form088 * pc5
theorem form092_val : form092.val = form092Matrix := by
  change form088.val * pc5Matrix = form092Matrix
  rw [form088_val]
  exact form092Step

def form093Matrix : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form093Step : form092Matrix * pc7Matrix = form093Matrix := by decide +kernel
def form093 : UnitMatrix := form092 * pc7
theorem form093_val : form093.val = form093Matrix := by
  change form092.val * pc7Matrix = form093Matrix
  rw [form092_val]
  exact form093Step

def form094Matrix : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form094Step : form092Matrix * pc6Matrix = form094Matrix := by decide +kernel
def form094 : UnitMatrix := form092 * pc6
theorem form094_val : form094.val = form094Matrix := by
  change form092.val * pc6Matrix = form094Matrix
  rw [form092_val]
  exact form094Step

def form095Matrix : M := !![ofCode 1, ofCode 2, ofCode 7, ofCode 5; ofCode 0, ofCode 1, ofCode 6, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 2; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form095Step : form094Matrix * pc7Matrix = form095Matrix := by decide +kernel
def form095 : UnitMatrix := form094 * pc7
theorem form095_val : form095.val = form095Matrix := by
  change form094.val * pc7Matrix = form095Matrix
  rw [form094_val]
  exact form095Step

def form096Matrix : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form096Step : form064Matrix * pc2Matrix = form096Matrix := by decide +kernel
def form096 : UnitMatrix := form064 * pc2
theorem form096_val : form096.val = form096Matrix := by
  change form064.val * pc2Matrix = form096Matrix
  rw [form064_val]
  exact form096Step

def form097Matrix : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form097Step : form096Matrix * pc7Matrix = form097Matrix := by decide +kernel
def form097 : UnitMatrix := form096 * pc7
theorem form097_val : form097.val = form097Matrix := by
  change form096.val * pc7Matrix = form097Matrix
  rw [form096_val]
  exact form097Step

def form098Matrix : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form098Step : form096Matrix * pc6Matrix = form098Matrix := by decide +kernel
def form098 : UnitMatrix := form096 * pc6
theorem form098_val : form098.val = form098Matrix := by
  change form096.val * pc6Matrix = form098Matrix
  rw [form096_val]
  exact form098Step

def form099Matrix : M := !![ofCode 1, ofCode 3, ofCode 2, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form099Step : form098Matrix * pc7Matrix = form099Matrix := by decide +kernel
def form099 : UnitMatrix := form098 * pc7
theorem form099_val : form099.val = form099Matrix := by
  change form098.val * pc7Matrix = form099Matrix
  rw [form098_val]
  exact form099Step

def form100Matrix : M := !![ofCode 1, ofCode 3, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form100Step : form096Matrix * pc5Matrix = form100Matrix := by decide +kernel
def form100 : UnitMatrix := form096 * pc5
theorem form100_val : form100.val = form100Matrix := by
  change form096.val * pc5Matrix = form100Matrix
  rw [form096_val]
  exact form100Step

def form101Matrix : M := !![ofCode 1, ofCode 3, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form101Step : form100Matrix * pc7Matrix = form101Matrix := by decide +kernel
def form101 : UnitMatrix := form100 * pc7
theorem form101_val : form101.val = form101Matrix := by
  change form100.val * pc7Matrix = form101Matrix
  rw [form100_val]
  exact form101Step

def form102Matrix : M := !![ofCode 1, ofCode 3, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form102Step : form100Matrix * pc6Matrix = form102Matrix := by decide +kernel
def form102 : UnitMatrix := form100 * pc6
theorem form102_val : form102.val = form102Matrix := by
  change form100.val * pc6Matrix = form102Matrix
  rw [form100_val]
  exact form102Step

def form103Matrix : M := !![ofCode 1, ofCode 3, ofCode 3, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form103Step : form102Matrix * pc7Matrix = form103Matrix := by decide +kernel
def form103 : UnitMatrix := form102 * pc7
theorem form103_val : form103.val = form103Matrix := by
  change form102.val * pc7Matrix = form103Matrix
  rw [form102_val]
  exact form103Step

def form104Matrix : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form104Step : form096Matrix * pc4Matrix = form104Matrix := by decide +kernel
def form104 : UnitMatrix := form096 * pc4
theorem form104_val : form104.val = form104Matrix := by
  change form096.val * pc4Matrix = form104Matrix
  rw [form096_val]
  exact form104Step

def form105Matrix : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form105Step : form104Matrix * pc7Matrix = form105Matrix := by decide +kernel
def form105 : UnitMatrix := form104 * pc7
theorem form105_val : form105.val = form105Matrix := by
  change form104.val * pc7Matrix = form105Matrix
  rw [form104_val]
  exact form105Step

def form106Matrix : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form106Step : form104Matrix * pc6Matrix = form106Matrix := by decide +kernel
def form106 : UnitMatrix := form104 * pc6
theorem form106_val : form106.val = form106Matrix := by
  change form104.val * pc6Matrix = form106Matrix
  rw [form104_val]
  exact form106Step

def form107Matrix : M := !![ofCode 1, ofCode 3, ofCode 0, ofCode 6; ofCode 0, ofCode 1, ofCode 7, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form107Step : form106Matrix * pc7Matrix = form107Matrix := by decide +kernel
def form107 : UnitMatrix := form106 * pc7
theorem form107_val : form107.val = form107Matrix := by
  change form106.val * pc7Matrix = form107Matrix
  rw [form106_val]
  exact form107Step

def form108Matrix : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form108Step : form104Matrix * pc5Matrix = form108Matrix := by decide +kernel
def form108 : UnitMatrix := form104 * pc5
theorem form108_val : form108.val = form108Matrix := by
  change form104.val * pc5Matrix = form108Matrix
  rw [form104_val]
  exact form108Step

def form109Matrix : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form109Step : form108Matrix * pc7Matrix = form109Matrix := by decide +kernel
def form109 : UnitMatrix := form108 * pc7
theorem form109_val : form109.val = form109Matrix := by
  change form108.val * pc7Matrix = form109Matrix
  rw [form108_val]
  exact form109Step

def form110Matrix : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form110Step : form108Matrix * pc6Matrix = form110Matrix := by decide +kernel
def form110 : UnitMatrix := form108 * pc6
theorem form110_val : form110.val = form110Matrix := by
  change form108.val * pc6Matrix = form110Matrix
  rw [form108_val]
  exact form110Step

def form111Matrix : M := !![ofCode 1, ofCode 3, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 7, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form111Step : form110Matrix * pc7Matrix = form111Matrix := by decide +kernel
def form111 : UnitMatrix := form110 * pc7
theorem form111_val : form111.val = form111Matrix := by
  change form110.val * pc7Matrix = form111Matrix
  rw [form110_val]
  exact form111Step

def form112Matrix : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form112Step : form096Matrix * pc3Matrix = form112Matrix := by decide +kernel
def form112 : UnitMatrix := form096 * pc3
theorem form112_val : form112.val = form112Matrix := by
  change form096.val * pc3Matrix = form112Matrix
  rw [form096_val]
  exact form112Step

def form113Matrix : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form113Step : form112Matrix * pc7Matrix = form113Matrix := by decide +kernel
def form113 : UnitMatrix := form112 * pc7
theorem form113_val : form113.val = form113Matrix := by
  change form112.val * pc7Matrix = form113Matrix
  rw [form112_val]
  exact form113Step

def form114Matrix : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form114Step : form112Matrix * pc6Matrix = form114Matrix := by decide +kernel
def form114 : UnitMatrix := form112 * pc6
theorem form114_val : form114.val = form114Matrix := by
  change form112.val * pc6Matrix = form114Matrix
  rw [form112_val]
  exact form114Step

def form115Matrix : M := !![ofCode 1, ofCode 3, ofCode 6, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form115Step : form114Matrix * pc7Matrix = form115Matrix := by decide +kernel
def form115 : UnitMatrix := form114 * pc7
theorem form115_val : form115.val = form115Matrix := by
  change form114.val * pc7Matrix = form115Matrix
  rw [form114_val]
  exact form115Step

def form116Matrix : M := !![ofCode 1, ofCode 3, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form116Step : form112Matrix * pc5Matrix = form116Matrix := by decide +kernel
def form116 : UnitMatrix := form112 * pc5
theorem form116_val : form116.val = form116Matrix := by
  change form112.val * pc5Matrix = form116Matrix
  rw [form112_val]
  exact form116Step

def form117Matrix : M := !![ofCode 1, ofCode 3, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form117Step : form116Matrix * pc7Matrix = form117Matrix := by decide +kernel
def form117 : UnitMatrix := form116 * pc7
theorem form117_val : form117.val = form117Matrix := by
  change form116.val * pc7Matrix = form117Matrix
  rw [form116_val]
  exact form117Step

def form118Matrix : M := !![ofCode 1, ofCode 3, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form118Step : form116Matrix * pc6Matrix = form118Matrix := by decide +kernel
def form118 : UnitMatrix := form116 * pc6
theorem form118_val : form118.val = form118Matrix := by
  change form116.val * pc6Matrix = form118Matrix
  rw [form116_val]
  exact form118Step

def form119Matrix : M := !![ofCode 1, ofCode 3, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form119Step : form118Matrix * pc7Matrix = form119Matrix := by decide +kernel
def form119 : UnitMatrix := form118 * pc7
theorem form119_val : form119.val = form119Matrix := by
  change form118.val * pc7Matrix = form119Matrix
  rw [form118_val]
  exact form119Step

def form120Matrix : M := !![ofCode 1, ofCode 3, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form120Step : form112Matrix * pc4Matrix = form120Matrix := by decide +kernel
def form120 : UnitMatrix := form112 * pc4
theorem form120_val : form120.val = form120Matrix := by
  change form112.val * pc4Matrix = form120Matrix
  rw [form112_val]
  exact form120Step

def form121Matrix : M := !![ofCode 1, ofCode 3, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form121Step : form120Matrix * pc7Matrix = form121Matrix := by decide +kernel
def form121 : UnitMatrix := form120 * pc7
theorem form121_val : form121.val = form121Matrix := by
  change form120.val * pc7Matrix = form121Matrix
  rw [form120_val]
  exact form121Step

def form122Matrix : M := !![ofCode 1, ofCode 3, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form122Step : form120Matrix * pc6Matrix = form122Matrix := by decide +kernel
def form122 : UnitMatrix := form120 * pc6
theorem form122_val : form122.val = form122Matrix := by
  change form120.val * pc6Matrix = form122Matrix
  rw [form120_val]
  exact form122Step

def form123Matrix : M := !![ofCode 1, ofCode 3, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 7, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form123Step : form122Matrix * pc7Matrix = form123Matrix := by decide +kernel
def form123 : UnitMatrix := form122 * pc7
theorem form123_val : form123.val = form123Matrix := by
  change form122.val * pc7Matrix = form123Matrix
  rw [form122_val]
  exact form123Step

def form124Matrix : M := !![ofCode 1, ofCode 3, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form124Step : form120Matrix * pc5Matrix = form124Matrix := by decide +kernel
def form124 : UnitMatrix := form120 * pc5
theorem form124_val : form124.val = form124Matrix := by
  change form120.val * pc5Matrix = form124Matrix
  rw [form120_val]
  exact form124Step

def form125Matrix : M := !![ofCode 1, ofCode 3, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form125Step : form124Matrix * pc7Matrix = form125Matrix := by decide +kernel
def form125 : UnitMatrix := form124 * pc7
theorem form125_val : form125.val = form125Matrix := by
  change form124.val * pc7Matrix = form125Matrix
  rw [form124_val]
  exact form125Step

def form126Matrix : M := !![ofCode 1, ofCode 3, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form126Step : form124Matrix * pc6Matrix = form126Matrix := by decide +kernel
def form126 : UnitMatrix := form124 * pc6
theorem form126_val : form126.val = form126Matrix := by
  change form124.val * pc6Matrix = form126Matrix
  rw [form124_val]
  exact form126Step

def form127Matrix : M := !![ofCode 1, ofCode 3, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 7, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 3; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form127Step : form126Matrix * pc7Matrix = form127Matrix := by decide +kernel
def form127 : UnitMatrix := form126 * pc7
theorem form127_val : form127.val = form127Matrix := by
  change form126.val * pc7Matrix = form127Matrix
  rw [form126_val]
  exact form127Step

def form128Matrix : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
def form128 : UnitMatrix := pc0
theorem form128_val : form128.val = form128Matrix := rfl

def form129Matrix : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form129Step : form128Matrix * pc7Matrix = form129Matrix := by decide +kernel
def form129 : UnitMatrix := form128 * pc7
theorem form129_val : form129.val = form129Matrix := by
  change form128.val * pc7Matrix = form129Matrix
  rw [form128_val]
  exact form129Step

def form130Matrix : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form130Step : form128Matrix * pc6Matrix = form130Matrix := by decide +kernel
def form130 : UnitMatrix := form128 * pc6
theorem form130_val : form130.val = form130Matrix := by
  change form128.val * pc6Matrix = form130Matrix
  rw [form128_val]
  exact form130Step

def form131Matrix : M := !![ofCode 1, ofCode 4, ofCode 0, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form131Step : form130Matrix * pc7Matrix = form131Matrix := by decide +kernel
def form131 : UnitMatrix := form130 * pc7
theorem form131_val : form131.val = form131Matrix := by
  change form130.val * pc7Matrix = form131Matrix
  rw [form130_val]
  exact form131Step

def form132Matrix : M := !![ofCode 1, ofCode 4, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form132Step : form128Matrix * pc5Matrix = form132Matrix := by decide +kernel
def form132 : UnitMatrix := form128 * pc5
theorem form132_val : form132.val = form132Matrix := by
  change form128.val * pc5Matrix = form132Matrix
  rw [form128_val]
  exact form132Step

def form133Matrix : M := !![ofCode 1, ofCode 4, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form133Step : form132Matrix * pc7Matrix = form133Matrix := by decide +kernel
def form133 : UnitMatrix := form132 * pc7
theorem form133_val : form133.val = form133Matrix := by
  change form132.val * pc7Matrix = form133Matrix
  rw [form132_val]
  exact form133Step

def form134Matrix : M := !![ofCode 1, ofCode 4, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form134Step : form132Matrix * pc6Matrix = form134Matrix := by decide +kernel
def form134 : UnitMatrix := form132 * pc6
theorem form134_val : form134.val = form134Matrix := by
  change form132.val * pc6Matrix = form134Matrix
  rw [form132_val]
  exact form134Step

def form135Matrix : M := !![ofCode 1, ofCode 4, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form135Step : form134Matrix * pc7Matrix = form135Matrix := by decide +kernel
def form135 : UnitMatrix := form134 * pc7
theorem form135_val : form135.val = form135Matrix := by
  change form134.val * pc7Matrix = form135Matrix
  rw [form134_val]
  exact form135Step

def form136Matrix : M := !![ofCode 1, ofCode 4, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form136Step : form128Matrix * pc4Matrix = form136Matrix := by decide +kernel
def form136 : UnitMatrix := form128 * pc4
theorem form136_val : form136.val = form136Matrix := by
  change form128.val * pc4Matrix = form136Matrix
  rw [form128_val]
  exact form136Step

def form137Matrix : M := !![ofCode 1, ofCode 4, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form137Step : form136Matrix * pc7Matrix = form137Matrix := by decide +kernel
def form137 : UnitMatrix := form136 * pc7
theorem form137_val : form137.val = form137Matrix := by
  change form136.val * pc7Matrix = form137Matrix
  rw [form136_val]
  exact form137Step

def form138Matrix : M := !![ofCode 1, ofCode 4, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form138Step : form136Matrix * pc6Matrix = form138Matrix := by decide +kernel
def form138 : UnitMatrix := form136 * pc6
theorem form138_val : form138.val = form138Matrix := by
  change form136.val * pc6Matrix = form138Matrix
  rw [form136_val]
  exact form138Step

def form139Matrix : M := !![ofCode 1, ofCode 4, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 2, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form139Step : form138Matrix * pc7Matrix = form139Matrix := by decide +kernel
def form139 : UnitMatrix := form138 * pc7
theorem form139_val : form139.val = form139Matrix := by
  change form138.val * pc7Matrix = form139Matrix
  rw [form138_val]
  exact form139Step

def form140Matrix : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form140Step : form136Matrix * pc5Matrix = form140Matrix := by decide +kernel
def form140 : UnitMatrix := form136 * pc5
theorem form140_val : form140.val = form140Matrix := by
  change form136.val * pc5Matrix = form140Matrix
  rw [form136_val]
  exact form140Step

def form141Matrix : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form141Step : form140Matrix * pc7Matrix = form141Matrix := by decide +kernel
def form141 : UnitMatrix := form140 * pc7
theorem form141_val : form141.val = form141Matrix := by
  change form140.val * pc7Matrix = form141Matrix
  rw [form140_val]
  exact form141Step

def form142Matrix : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form142Step : form140Matrix * pc6Matrix = form142Matrix := by decide +kernel
def form142 : UnitMatrix := form140 * pc6
theorem form142_val : form142.val = form142Matrix := by
  change form140.val * pc6Matrix = form142Matrix
  rw [form140_val]
  exact form142Step

def form143Matrix : M := !![ofCode 1, ofCode 4, ofCode 3, ofCode 7; ofCode 0, ofCode 1, ofCode 2, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form143Step : form142Matrix * pc7Matrix = form143Matrix := by decide +kernel
def form143 : UnitMatrix := form142 * pc7
theorem form143_val : form143.val = form143Matrix := by
  change form142.val * pc7Matrix = form143Matrix
  rw [form142_val]
  exact form143Step

def form144Matrix : M := !![ofCode 1, ofCode 4, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form144Step : form128Matrix * pc3Matrix = form144Matrix := by decide +kernel
def form144 : UnitMatrix := form128 * pc3
theorem form144_val : form144.val = form144Matrix := by
  change form128.val * pc3Matrix = form144Matrix
  rw [form128_val]
  exact form144Step

def form145Matrix : M := !![ofCode 1, ofCode 4, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form145Step : form144Matrix * pc7Matrix = form145Matrix := by decide +kernel
def form145 : UnitMatrix := form144 * pc7
theorem form145_val : form145.val = form145Matrix := by
  change form144.val * pc7Matrix = form145Matrix
  rw [form144_val]
  exact form145Step

def form146Matrix : M := !![ofCode 1, ofCode 4, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form146Step : form144Matrix * pc6Matrix = form146Matrix := by decide +kernel
def form146 : UnitMatrix := form144 * pc6
theorem form146_val : form146.val = form146Matrix := by
  change form144.val * pc6Matrix = form146Matrix
  rw [form144_val]
  exact form146Step

def form147Matrix : M := !![ofCode 1, ofCode 4, ofCode 4, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form147Step : form146Matrix * pc7Matrix = form147Matrix := by decide +kernel
def form147 : UnitMatrix := form146 * pc7
theorem form147_val : form147.val = form147Matrix := by
  change form146.val * pc7Matrix = form147Matrix
  rw [form146_val]
  exact form147Step

def form148Matrix : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form148Step : form144Matrix * pc5Matrix = form148Matrix := by decide +kernel
def form148 : UnitMatrix := form144 * pc5
theorem form148_val : form148.val = form148Matrix := by
  change form144.val * pc5Matrix = form148Matrix
  rw [form144_val]
  exact form148Step

def form149Matrix : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form149Step : form148Matrix * pc7Matrix = form149Matrix := by decide +kernel
def form149 : UnitMatrix := form148 * pc7
theorem form149_val : form149.val = form149Matrix := by
  change form148.val * pc7Matrix = form149Matrix
  rw [form148_val]
  exact form149Step

def form150Matrix : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form150Step : form148Matrix * pc6Matrix = form150Matrix := by decide +kernel
def form150 : UnitMatrix := form148 * pc6
theorem form150_val : form150.val = form150Matrix := by
  change form148.val * pc6Matrix = form150Matrix
  rw [form148_val]
  exact form150Step

def form151Matrix : M := !![ofCode 1, ofCode 4, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form151Step : form150Matrix * pc7Matrix = form151Matrix := by decide +kernel
def form151 : UnitMatrix := form150 * pc7
theorem form151_val : form151.val = form151Matrix := by
  change form150.val * pc7Matrix = form151Matrix
  rw [form150_val]
  exact form151Step

def form152Matrix : M := !![ofCode 1, ofCode 4, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form152Step : form144Matrix * pc4Matrix = form152Matrix := by decide +kernel
def form152 : UnitMatrix := form144 * pc4
theorem form152_val : form152.val = form152Matrix := by
  change form144.val * pc4Matrix = form152Matrix
  rw [form144_val]
  exact form152Step

def form153Matrix : M := !![ofCode 1, ofCode 4, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form153Step : form152Matrix * pc7Matrix = form153Matrix := by decide +kernel
def form153 : UnitMatrix := form152 * pc7
theorem form153_val : form153.val = form153Matrix := by
  change form152.val * pc7Matrix = form153Matrix
  rw [form152_val]
  exact form153Step

def form154Matrix : M := !![ofCode 1, ofCode 4, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form154Step : form152Matrix * pc6Matrix = form154Matrix := by decide +kernel
def form154 : UnitMatrix := form152 * pc6
theorem form154_val : form154.val = form154Matrix := by
  change form152.val * pc6Matrix = form154Matrix
  rw [form152_val]
  exact form154Step

def form155Matrix : M := !![ofCode 1, ofCode 4, ofCode 6, ofCode 6; ofCode 0, ofCode 1, ofCode 2, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form155Step : form154Matrix * pc7Matrix = form155Matrix := by decide +kernel
def form155 : UnitMatrix := form154 * pc7
theorem form155_val : form155.val = form155Matrix := by
  change form154.val * pc7Matrix = form155Matrix
  rw [form154_val]
  exact form155Step

def form156Matrix : M := !![ofCode 1, ofCode 4, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form156Step : form152Matrix * pc5Matrix = form156Matrix := by decide +kernel
def form156 : UnitMatrix := form152 * pc5
theorem form156_val : form156.val = form156Matrix := by
  change form152.val * pc5Matrix = form156Matrix
  rw [form152_val]
  exact form156Step

def form157Matrix : M := !![ofCode 1, ofCode 4, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form157Step : form156Matrix * pc7Matrix = form157Matrix := by decide +kernel
def form157 : UnitMatrix := form156 * pc7
theorem form157_val : form157.val = form157Matrix := by
  change form156.val * pc7Matrix = form157Matrix
  rw [form156_val]
  exact form157Step

def form158Matrix : M := !![ofCode 1, ofCode 4, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form158Step : form156Matrix * pc6Matrix = form158Matrix := by decide +kernel
def form158 : UnitMatrix := form156 * pc6
theorem form158_val : form158.val = form158Matrix := by
  change form156.val * pc6Matrix = form158Matrix
  rw [form156_val]
  exact form158Step

def form159Matrix : M := !![ofCode 1, ofCode 4, ofCode 7, ofCode 3; ofCode 0, ofCode 1, ofCode 2, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 4; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form159Step : form158Matrix * pc7Matrix = form159Matrix := by decide +kernel
def form159 : UnitMatrix := form158 * pc7
theorem form159_val : form159.val = form159Matrix := by
  change form158.val * pc7Matrix = form159Matrix
  rw [form158_val]
  exact form159Step

def form160Matrix : M := !![ofCode 1, ofCode 5, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form160Step : form128Matrix * pc2Matrix = form160Matrix := by decide +kernel
def form160 : UnitMatrix := form128 * pc2
theorem form160_val : form160.val = form160Matrix := by
  change form128.val * pc2Matrix = form160Matrix
  rw [form128_val]
  exact form160Step

def form161Matrix : M := !![ofCode 1, ofCode 5, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form161Step : form160Matrix * pc7Matrix = form161Matrix := by decide +kernel
def form161 : UnitMatrix := form160 * pc7
theorem form161_val : form161.val = form161Matrix := by
  change form160.val * pc7Matrix = form161Matrix
  rw [form160_val]
  exact form161Step

def form162Matrix : M := !![ofCode 1, ofCode 5, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form162Step : form160Matrix * pc6Matrix = form162Matrix := by decide +kernel
def form162 : UnitMatrix := form160 * pc6
theorem form162_val : form162.val = form162Matrix := by
  change form160.val * pc6Matrix = form162Matrix
  rw [form160_val]
  exact form162Step

def form163Matrix : M := !![ofCode 1, ofCode 5, ofCode 4, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form163Step : form162Matrix * pc7Matrix = form163Matrix := by decide +kernel
def form163 : UnitMatrix := form162 * pc7
theorem form163_val : form163.val = form163Matrix := by
  change form162.val * pc7Matrix = form163Matrix
  rw [form162_val]
  exact form163Step

def form164Matrix : M := !![ofCode 1, ofCode 5, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form164Step : form160Matrix * pc5Matrix = form164Matrix := by decide +kernel
def form164 : UnitMatrix := form160 * pc5
theorem form164_val : form164.val = form164Matrix := by
  change form160.val * pc5Matrix = form164Matrix
  rw [form160_val]
  exact form164Step

def form165Matrix : M := !![ofCode 1, ofCode 5, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form165Step : form164Matrix * pc7Matrix = form165Matrix := by decide +kernel
def form165 : UnitMatrix := form164 * pc7
theorem form165_val : form165.val = form165Matrix := by
  change form164.val * pc7Matrix = form165Matrix
  rw [form164_val]
  exact form165Step

def form166Matrix : M := !![ofCode 1, ofCode 5, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form166Step : form164Matrix * pc6Matrix = form166Matrix := by decide +kernel
def form166 : UnitMatrix := form164 * pc6
theorem form166_val : form166.val = form166Matrix := by
  change form164.val * pc6Matrix = form166Matrix
  rw [form164_val]
  exact form166Step

def form167Matrix : M := !![ofCode 1, ofCode 5, ofCode 5, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form167Step : form166Matrix * pc7Matrix = form167Matrix := by decide +kernel
def form167 : UnitMatrix := form166 * pc7
theorem form167_val : form167.val = form167Matrix := by
  change form166.val * pc7Matrix = form167Matrix
  rw [form166_val]
  exact form167Step

def form168Matrix : M := !![ofCode 1, ofCode 5, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form168Step : form160Matrix * pc4Matrix = form168Matrix := by decide +kernel
def form168 : UnitMatrix := form160 * pc4
theorem form168_val : form168.val = form168Matrix := by
  change form160.val * pc4Matrix = form168Matrix
  rw [form160_val]
  exact form168Step

def form169Matrix : M := !![ofCode 1, ofCode 5, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form169Step : form168Matrix * pc7Matrix = form169Matrix := by decide +kernel
def form169 : UnitMatrix := form168 * pc7
theorem form169_val : form169.val = form169Matrix := by
  change form168.val * pc7Matrix = form169Matrix
  rw [form168_val]
  exact form169Step

def form170Matrix : M := !![ofCode 1, ofCode 5, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form170Step : form168Matrix * pc6Matrix = form170Matrix := by decide +kernel
def form170 : UnitMatrix := form168 * pc6
theorem form170_val : form170.val = form170Matrix := by
  change form168.val * pc6Matrix = form170Matrix
  rw [form168_val]
  exact form170Step

def form171Matrix : M := !![ofCode 1, ofCode 5, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form171Step : form170Matrix * pc7Matrix = form171Matrix := by decide +kernel
def form171 : UnitMatrix := form170 * pc7
theorem form171_val : form171.val = form171Matrix := by
  change form170.val * pc7Matrix = form171Matrix
  rw [form170_val]
  exact form171Step

def form172Matrix : M := !![ofCode 1, ofCode 5, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form172Step : form168Matrix * pc5Matrix = form172Matrix := by decide +kernel
def form172 : UnitMatrix := form168 * pc5
theorem form172_val : form172.val = form172Matrix := by
  change form168.val * pc5Matrix = form172Matrix
  rw [form168_val]
  exact form172Step

def form173Matrix : M := !![ofCode 1, ofCode 5, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form173Step : form172Matrix * pc7Matrix = form173Matrix := by decide +kernel
def form173 : UnitMatrix := form172 * pc7
theorem form173_val : form173.val = form173Matrix := by
  change form172.val * pc7Matrix = form173Matrix
  rw [form172_val]
  exact form173Step

def form174Matrix : M := !![ofCode 1, ofCode 5, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form174Step : form172Matrix * pc6Matrix = form174Matrix := by decide +kernel
def form174 : UnitMatrix := form172 * pc6
theorem form174_val : form174.val = form174Matrix := by
  change form172.val * pc6Matrix = form174Matrix
  rw [form172_val]
  exact form174Step

def form175Matrix : M := !![ofCode 1, ofCode 5, ofCode 7, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form175Step : form174Matrix * pc7Matrix = form175Matrix := by decide +kernel
def form175 : UnitMatrix := form174 * pc7
theorem form175_val : form175.val = form175Matrix := by
  change form174.val * pc7Matrix = form175Matrix
  rw [form174_val]
  exact form175Step

def form176Matrix : M := !![ofCode 1, ofCode 5, ofCode 0, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form176Step : form160Matrix * pc3Matrix = form176Matrix := by decide +kernel
def form176 : UnitMatrix := form160 * pc3
theorem form176_val : form176.val = form176Matrix := by
  change form160.val * pc3Matrix = form176Matrix
  rw [form160_val]
  exact form176Step

def form177Matrix : M := !![ofCode 1, ofCode 5, ofCode 0, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form177Step : form176Matrix * pc7Matrix = form177Matrix := by decide +kernel
def form177 : UnitMatrix := form176 * pc7
theorem form177_val : form177.val = form177Matrix := by
  change form176.val * pc7Matrix = form177Matrix
  rw [form176_val]
  exact form177Step

def form178Matrix : M := !![ofCode 1, ofCode 5, ofCode 0, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form178Step : form176Matrix * pc6Matrix = form178Matrix := by decide +kernel
def form178 : UnitMatrix := form176 * pc6
theorem form178_val : form178.val = form178Matrix := by
  change form176.val * pc6Matrix = form178Matrix
  rw [form176_val]
  exact form178Step

def form179Matrix : M := !![ofCode 1, ofCode 5, ofCode 0, ofCode 2; ofCode 0, ofCode 1, ofCode 3, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form179Step : form178Matrix * pc7Matrix = form179Matrix := by decide +kernel
def form179 : UnitMatrix := form178 * pc7
theorem form179_val : form179.val = form179Matrix := by
  change form178.val * pc7Matrix = form179Matrix
  rw [form178_val]
  exact form179Step

def form180Matrix : M := !![ofCode 1, ofCode 5, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form180Step : form176Matrix * pc5Matrix = form180Matrix := by decide +kernel
def form180 : UnitMatrix := form176 * pc5
theorem form180_val : form180.val = form180Matrix := by
  change form176.val * pc5Matrix = form180Matrix
  rw [form176_val]
  exact form180Step

def form181Matrix : M := !![ofCode 1, ofCode 5, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form181Step : form180Matrix * pc7Matrix = form181Matrix := by decide +kernel
def form181 : UnitMatrix := form180 * pc7
theorem form181_val : form181.val = form181Matrix := by
  change form180.val * pc7Matrix = form181Matrix
  rw [form180_val]
  exact form181Step

def form182Matrix : M := !![ofCode 1, ofCode 5, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form182Step : form180Matrix * pc6Matrix = form182Matrix := by decide +kernel
def form182 : UnitMatrix := form180 * pc6
theorem form182_val : form182.val = form182Matrix := by
  change form180.val * pc6Matrix = form182Matrix
  rw [form180_val]
  exact form182Step

def form183Matrix : M := !![ofCode 1, ofCode 5, ofCode 1, ofCode 6; ofCode 0, ofCode 1, ofCode 3, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form183Step : form182Matrix * pc7Matrix = form183Matrix := by decide +kernel
def form183 : UnitMatrix := form182 * pc7
theorem form183_val : form183.val = form183Matrix := by
  change form182.val * pc7Matrix = form183Matrix
  rw [form182_val]
  exact form183Step

def form184Matrix : M := !![ofCode 1, ofCode 5, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form184Step : form176Matrix * pc4Matrix = form184Matrix := by decide +kernel
def form184 : UnitMatrix := form176 * pc4
theorem form184_val : form184.val = form184Matrix := by
  change form176.val * pc4Matrix = form184Matrix
  rw [form176_val]
  exact form184Step

def form185Matrix : M := !![ofCode 1, ofCode 5, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form185Step : form184Matrix * pc7Matrix = form185Matrix := by decide +kernel
def form185 : UnitMatrix := form184 * pc7
theorem form185_val : form185.val = form185Matrix := by
  change form184.val * pc7Matrix = form185Matrix
  rw [form184_val]
  exact form185Step

def form186Matrix : M := !![ofCode 1, ofCode 5, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form186Step : form184Matrix * pc6Matrix = form186Matrix := by decide +kernel
def form186 : UnitMatrix := form184 * pc6
theorem form186_val : form186.val = form186Matrix := by
  change form184.val * pc6Matrix = form186Matrix
  rw [form184_val]
  exact form186Step

def form187Matrix : M := !![ofCode 1, ofCode 5, ofCode 2, ofCode 5; ofCode 0, ofCode 1, ofCode 3, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form187Step : form186Matrix * pc7Matrix = form187Matrix := by decide +kernel
def form187 : UnitMatrix := form186 * pc7
theorem form187_val : form187.val = form187Matrix := by
  change form186.val * pc7Matrix = form187Matrix
  rw [form186_val]
  exact form187Step

def form188Matrix : M := !![ofCode 1, ofCode 5, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form188Step : form184Matrix * pc5Matrix = form188Matrix := by decide +kernel
def form188 : UnitMatrix := form184 * pc5
theorem form188_val : form188.val = form188Matrix := by
  change form184.val * pc5Matrix = form188Matrix
  rw [form184_val]
  exact form188Step

def form189Matrix : M := !![ofCode 1, ofCode 5, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form189Step : form188Matrix * pc7Matrix = form189Matrix := by decide +kernel
def form189 : UnitMatrix := form188 * pc7
theorem form189_val : form189.val = form189Matrix := by
  change form188.val * pc7Matrix = form189Matrix
  rw [form188_val]
  exact form189Step

def form190Matrix : M := !![ofCode 1, ofCode 5, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form190Step : form188Matrix * pc6Matrix = form190Matrix := by decide +kernel
def form190 : UnitMatrix := form188 * pc6
theorem form190_val : form190.val = form190Matrix := by
  change form188.val * pc6Matrix = form190Matrix
  rw [form188_val]
  exact form190Step

def form191Matrix : M := !![ofCode 1, ofCode 5, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 3, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 5; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form191Step : form190Matrix * pc7Matrix = form191Matrix := by decide +kernel
def form191 : UnitMatrix := form190 * pc7
theorem form191_val : form191.val = form191Matrix := by
  change form190.val * pc7Matrix = form191Matrix
  rw [form190_val]
  exact form191Step

def form192Matrix : M := !![ofCode 1, ofCode 6, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form192Step : form128Matrix * pc1Matrix = form192Matrix := by decide +kernel
def form192 : UnitMatrix := form128 * pc1
theorem form192_val : form192.val = form192Matrix := by
  change form128.val * pc1Matrix = form192Matrix
  rw [form128_val]
  exact form192Step

def form193Matrix : M := !![ofCode 1, ofCode 6, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form193Step : form192Matrix * pc7Matrix = form193Matrix := by decide +kernel
def form193 : UnitMatrix := form192 * pc7
theorem form193_val : form193.val = form193Matrix := by
  change form192.val * pc7Matrix = form193Matrix
  rw [form192_val]
  exact form193Step

def form194Matrix : M := !![ofCode 1, ofCode 6, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form194Step : form192Matrix * pc6Matrix = form194Matrix := by decide +kernel
def form194 : UnitMatrix := form192 * pc6
theorem form194_val : form194.val = form194Matrix := by
  change form192.val * pc6Matrix = form194Matrix
  rw [form192_val]
  exact form194Step

def form195Matrix : M := !![ofCode 1, ofCode 6, ofCode 5, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form195Step : form194Matrix * pc7Matrix = form195Matrix := by decide +kernel
def form195 : UnitMatrix := form194 * pc7
theorem form195_val : form195.val = form195Matrix := by
  change form194.val * pc7Matrix = form195Matrix
  rw [form194_val]
  exact form195Step

def form196Matrix : M := !![ofCode 1, ofCode 6, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form196Step : form192Matrix * pc5Matrix = form196Matrix := by decide +kernel
def form196 : UnitMatrix := form192 * pc5
theorem form196_val : form196.val = form196Matrix := by
  change form192.val * pc5Matrix = form196Matrix
  rw [form192_val]
  exact form196Step

def form197Matrix : M := !![ofCode 1, ofCode 6, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form197Step : form196Matrix * pc7Matrix = form197Matrix := by decide +kernel
def form197 : UnitMatrix := form196 * pc7
theorem form197_val : form197.val = form197Matrix := by
  change form196.val * pc7Matrix = form197Matrix
  rw [form196_val]
  exact form197Step

def form198Matrix : M := !![ofCode 1, ofCode 6, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form198Step : form196Matrix * pc6Matrix = form198Matrix := by decide +kernel
def form198 : UnitMatrix := form196 * pc6
theorem form198_val : form198.val = form198Matrix := by
  change form196.val * pc6Matrix = form198Matrix
  rw [form196_val]
  exact form198Step

def form199Matrix : M := !![ofCode 1, ofCode 6, ofCode 4, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form199Step : form198Matrix * pc7Matrix = form199Matrix := by decide +kernel
def form199 : UnitMatrix := form198 * pc7
theorem form199_val : form199.val = form199Matrix := by
  change form198.val * pc7Matrix = form199Matrix
  rw [form198_val]
  exact form199Step

def form200Matrix : M := !![ofCode 1, ofCode 6, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form200Step : form192Matrix * pc4Matrix = form200Matrix := by decide +kernel
def form200 : UnitMatrix := form192 * pc4
theorem form200_val : form200.val = form200Matrix := by
  change form192.val * pc4Matrix = form200Matrix
  rw [form192_val]
  exact form200Step

def form201Matrix : M := !![ofCode 1, ofCode 6, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form201Step : form200Matrix * pc7Matrix = form201Matrix := by decide +kernel
def form201 : UnitMatrix := form200 * pc7
theorem form201_val : form201.val = form201Matrix := by
  change form200.val * pc7Matrix = form201Matrix
  rw [form200_val]
  exact form201Step

def form202Matrix : M := !![ofCode 1, ofCode 6, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form202Step : form200Matrix * pc6Matrix = form202Matrix := by decide +kernel
def form202 : UnitMatrix := form200 * pc6
theorem form202_val : form202.val = form202Matrix := by
  change form200.val * pc6Matrix = form202Matrix
  rw [form200_val]
  exact form202Step

def form203Matrix : M := !![ofCode 1, ofCode 6, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form203Step : form202Matrix * pc7Matrix = form203Matrix := by decide +kernel
def form203 : UnitMatrix := form202 * pc7
theorem form203_val : form203.val = form203Matrix := by
  change form202.val * pc7Matrix = form203Matrix
  rw [form202_val]
  exact form203Step

def form204Matrix : M := !![ofCode 1, ofCode 6, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form204Step : form200Matrix * pc5Matrix = form204Matrix := by decide +kernel
def form204 : UnitMatrix := form200 * pc5
theorem form204_val : form204.val = form204Matrix := by
  change form200.val * pc5Matrix = form204Matrix
  rw [form200_val]
  exact form204Step

def form205Matrix : M := !![ofCode 1, ofCode 6, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form205Step : form204Matrix * pc7Matrix = form205Matrix := by decide +kernel
def form205 : UnitMatrix := form204 * pc7
theorem form205_val : form205.val = form205Matrix := by
  change form204.val * pc7Matrix = form205Matrix
  rw [form204_val]
  exact form205Step

def form206Matrix : M := !![ofCode 1, ofCode 6, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form206Step : form204Matrix * pc6Matrix = form206Matrix := by decide +kernel
def form206 : UnitMatrix := form204 * pc6
theorem form206_val : form206.val = form206Matrix := by
  change form204.val * pc6Matrix = form206Matrix
  rw [form204_val]
  exact form206Step

def form207Matrix : M := !![ofCode 1, ofCode 6, ofCode 6, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form207Step : form206Matrix * pc7Matrix = form207Matrix := by decide +kernel
def form207 : UnitMatrix := form206 * pc7
theorem form207_val : form207.val = form207Matrix := by
  change form206.val * pc7Matrix = form207Matrix
  rw [form206_val]
  exact form207Step

def form208Matrix : M := !![ofCode 1, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form208Step : form192Matrix * pc3Matrix = form208Matrix := by decide +kernel
def form208 : UnitMatrix := form192 * pc3
theorem form208_val : form208.val = form208Matrix := by
  change form192.val * pc3Matrix = form208Matrix
  rw [form192_val]
  exact form208Step

def form209Matrix : M := !![ofCode 1, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form209Step : form208Matrix * pc7Matrix = form209Matrix := by decide +kernel
def form209 : UnitMatrix := form208 * pc7
theorem form209_val : form209.val = form209Matrix := by
  change form208.val * pc7Matrix = form209Matrix
  rw [form208_val]
  exact form209Step

def form210Matrix : M := !![ofCode 1, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form210Step : form208Matrix * pc6Matrix = form210Matrix := by decide +kernel
def form210 : UnitMatrix := form208 * pc6
theorem form210_val : form210.val = form210Matrix := by
  change form208.val * pc6Matrix = form210Matrix
  rw [form208_val]
  exact form210Step

def form211Matrix : M := !![ofCode 1, ofCode 6, ofCode 1, ofCode 4; ofCode 0, ofCode 1, ofCode 4, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form211Step : form210Matrix * pc7Matrix = form211Matrix := by decide +kernel
def form211 : UnitMatrix := form210 * pc7
theorem form211_val : form211.val = form211Matrix := by
  change form210.val * pc7Matrix = form211Matrix
  rw [form210_val]
  exact form211Step

def form212Matrix : M := !![ofCode 1, ofCode 6, ofCode 0, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form212Step : form208Matrix * pc5Matrix = form212Matrix := by decide +kernel
def form212 : UnitMatrix := form208 * pc5
theorem form212_val : form212.val = form212Matrix := by
  change form208.val * pc5Matrix = form212Matrix
  rw [form208_val]
  exact form212Step

def form213Matrix : M := !![ofCode 1, ofCode 6, ofCode 0, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form213Step : form212Matrix * pc7Matrix = form213Matrix := by decide +kernel
def form213 : UnitMatrix := form212 * pc7
theorem form213_val : form213.val = form213Matrix := by
  change form212.val * pc7Matrix = form213Matrix
  rw [form212_val]
  exact form213Step

def form214Matrix : M := !![ofCode 1, ofCode 6, ofCode 0, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form214Step : form212Matrix * pc6Matrix = form214Matrix := by decide +kernel
def form214 : UnitMatrix := form212 * pc6
theorem form214_val : form214.val = form214Matrix := by
  change form212.val * pc6Matrix = form214Matrix
  rw [form212_val]
  exact form214Step

def form215Matrix : M := !![ofCode 1, ofCode 6, ofCode 0, ofCode 3; ofCode 0, ofCode 1, ofCode 4, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form215Step : form214Matrix * pc7Matrix = form215Matrix := by decide +kernel
def form215 : UnitMatrix := form214 * pc7
theorem form215_val : form215.val = form215Matrix := by
  change form214.val * pc7Matrix = form215Matrix
  rw [form214_val]
  exact form215Step

def form216Matrix : M := !![ofCode 1, ofCode 6, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form216Step : form208Matrix * pc4Matrix = form216Matrix := by decide +kernel
def form216 : UnitMatrix := form208 * pc4
theorem form216_val : form216.val = form216Matrix := by
  change form208.val * pc4Matrix = form216Matrix
  rw [form208_val]
  exact form216Step

def form217Matrix : M := !![ofCode 1, ofCode 6, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form217Step : form216Matrix * pc7Matrix = form217Matrix := by decide +kernel
def form217 : UnitMatrix := form216 * pc7
theorem form217_val : form217.val = form217Matrix := by
  change form216.val * pc7Matrix = form217Matrix
  rw [form216_val]
  exact form217Step

def form218Matrix : M := !![ofCode 1, ofCode 6, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form218Step : form216Matrix * pc6Matrix = form218Matrix := by decide +kernel
def form218 : UnitMatrix := form216 * pc6
theorem form218_val : form218.val = form218Matrix := by
  change form216.val * pc6Matrix = form218Matrix
  rw [form216_val]
  exact form218Step

def form219Matrix : M := !![ofCode 1, ofCode 6, ofCode 3, ofCode 5; ofCode 0, ofCode 1, ofCode 4, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form219Step : form218Matrix * pc7Matrix = form219Matrix := by decide +kernel
def form219 : UnitMatrix := form218 * pc7
theorem form219_val : form219.val = form219Matrix := by
  change form218.val * pc7Matrix = form219Matrix
  rw [form218_val]
  exact form219Step

def form220Matrix : M := !![ofCode 1, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form220Step : form216Matrix * pc5Matrix = form220Matrix := by decide +kernel
def form220 : UnitMatrix := form216 * pc5
theorem form220_val : form220.val = form220Matrix := by
  change form216.val * pc5Matrix = form220Matrix
  rw [form216_val]
  exact form220Step

def form221Matrix : M := !![ofCode 1, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form221Step : form220Matrix * pc7Matrix = form221Matrix := by decide +kernel
def form221 : UnitMatrix := form220 * pc7
theorem form221_val : form221.val = form221Matrix := by
  change form220.val * pc7Matrix = form221Matrix
  rw [form220_val]
  exact form221Step

def form222Matrix : M := !![ofCode 1, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form222Step : form220Matrix * pc6Matrix = form222Matrix := by decide +kernel
def form222 : UnitMatrix := form220 * pc6
theorem form222_val : form222.val = form222Matrix := by
  change form220.val * pc6Matrix = form222Matrix
  rw [form220_val]
  exact form222Step

def form223Matrix : M := !![ofCode 1, ofCode 6, ofCode 2, ofCode 2; ofCode 0, ofCode 1, ofCode 4, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 6; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form223Step : form222Matrix * pc7Matrix = form223Matrix := by decide +kernel
def form223 : UnitMatrix := form222 * pc7
theorem form223_val : form223.val = form223Matrix := by
  change form222.val * pc7Matrix = form223Matrix
  rw [form222_val]
  exact form223Step

def form224Matrix : M := !![ofCode 1, ofCode 7, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form224Step : form192Matrix * pc2Matrix = form224Matrix := by decide +kernel
def form224 : UnitMatrix := form192 * pc2
theorem form224_val : form224.val = form224Matrix := by
  change form192.val * pc2Matrix = form224Matrix
  rw [form192_val]
  exact form224Step

def form225Matrix : M := !![ofCode 1, ofCode 7, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form225Step : form224Matrix * pc7Matrix = form225Matrix := by decide +kernel
def form225 : UnitMatrix := form224 * pc7
theorem form225_val : form225.val = form225Matrix := by
  change form224.val * pc7Matrix = form225Matrix
  rw [form224_val]
  exact form225Step

def form226Matrix : M := !![ofCode 1, ofCode 7, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form226Step : form224Matrix * pc6Matrix = form226Matrix := by decide +kernel
def form226 : UnitMatrix := form224 * pc6
theorem form226_val : form226.val = form226Matrix := by
  change form224.val * pc6Matrix = form226Matrix
  rw [form224_val]
  exact form226Step

def form227Matrix : M := !![ofCode 1, ofCode 7, ofCode 3, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 5; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form227Step : form226Matrix * pc7Matrix = form227Matrix := by decide +kernel
def form227 : UnitMatrix := form226 * pc7
theorem form227_val : form227.val = form227Matrix := by
  change form226.val * pc7Matrix = form227Matrix
  rw [form226_val]
  exact form227Step

def form228Matrix : M := !![ofCode 1, ofCode 7, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form228Step : form224Matrix * pc5Matrix = form228Matrix := by decide +kernel
def form228 : UnitMatrix := form224 * pc5
theorem form228_val : form228.val = form228Matrix := by
  change form224.val * pc5Matrix = form228Matrix
  rw [form224_val]
  exact form228Step

def form229Matrix : M := !![ofCode 1, ofCode 7, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form229Step : form228Matrix * pc7Matrix = form229Matrix := by decide +kernel
def form229 : UnitMatrix := form228 * pc7
theorem form229_val : form229.val = form229Matrix := by
  change form228.val * pc7Matrix = form229Matrix
  rw [form228_val]
  exact form229Step

def form230Matrix : M := !![ofCode 1, ofCode 7, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form230Step : form228Matrix * pc6Matrix = form230Matrix := by decide +kernel
def form230 : UnitMatrix := form228 * pc6
theorem form230_val : form230.val = form230Matrix := by
  change form228.val * pc6Matrix = form230Matrix
  rw [form228_val]
  exact form230Step

def form231Matrix : M := !![ofCode 1, ofCode 7, ofCode 2, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 4; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form231Step : form230Matrix * pc7Matrix = form231Matrix := by decide +kernel
def form231 : UnitMatrix := form230 * pc7
theorem form231_val : form231.val = form231Matrix := by
  change form230.val * pc7Matrix = form231Matrix
  rw [form230_val]
  exact form231Step

def form232Matrix : M := !![ofCode 1, ofCode 7, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form232Step : form224Matrix * pc4Matrix = form232Matrix := by decide +kernel
def form232 : UnitMatrix := form224 * pc4
theorem form232_val : form232.val = form232Matrix := by
  change form224.val * pc4Matrix = form232Matrix
  rw [form224_val]
  exact form232Step

def form233Matrix : M := !![ofCode 1, ofCode 7, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form233Step : form232Matrix * pc7Matrix = form233Matrix := by decide +kernel
def form233 : UnitMatrix := form232 * pc7
theorem form233_val : form233.val = form233Matrix := by
  change form232.val * pc7Matrix = form233Matrix
  rw [form232_val]
  exact form233Step

def form234Matrix : M := !![ofCode 1, ofCode 7, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form234Step : form232Matrix * pc6Matrix = form234Matrix := by decide +kernel
def form234 : UnitMatrix := form232 * pc6
theorem form234_val : form234.val = form234Matrix := by
  change form232.val * pc6Matrix = form234Matrix
  rw [form232_val]
  exact form234Step

def form235Matrix : M := !![ofCode 1, ofCode 7, ofCode 1, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 7; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form235Step : form234Matrix * pc7Matrix = form235Matrix := by decide +kernel
def form235 : UnitMatrix := form234 * pc7
theorem form235_val : form235.val = form235Matrix := by
  change form234.val * pc7Matrix = form235Matrix
  rw [form234_val]
  exact form235Step

def form236Matrix : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form236Step : form232Matrix * pc5Matrix = form236Matrix := by decide +kernel
def form236 : UnitMatrix := form232 * pc5
theorem form236_val : form236.val = form236Matrix := by
  change form232.val * pc5Matrix = form236Matrix
  rw [form232_val]
  exact form236Step

def form237Matrix : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form237Step : form236Matrix * pc7Matrix = form237Matrix := by decide +kernel
def form237 : UnitMatrix := form236 * pc7
theorem form237_val : form237.val = form237Matrix := by
  change form236.val * pc7Matrix = form237Matrix
  rw [form236_val]
  exact form237Step

def form238Matrix : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form238Step : form236Matrix * pc6Matrix = form238Matrix := by decide +kernel
def form238 : UnitMatrix := form236 * pc6
theorem form238_val : form238.val = form238Matrix := by
  change form236.val * pc6Matrix = form238Matrix
  rw [form236_val]
  exact form238Step

def form239Matrix : M := !![ofCode 1, ofCode 7, ofCode 0, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 6; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form239Step : form238Matrix * pc7Matrix = form239Matrix := by decide +kernel
def form239 : UnitMatrix := form238 * pc7
theorem form239_val : form239.val = form239Matrix := by
  change form238.val * pc7Matrix = form239Matrix
  rw [form238_val]
  exact form239Step

def form240Matrix : M := !![ofCode 1, ofCode 7, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form240Step : form224Matrix * pc3Matrix = form240Matrix := by decide +kernel
def form240 : UnitMatrix := form224 * pc3
theorem form240_val : form240.val = form240Matrix := by
  change form224.val * pc3Matrix = form240Matrix
  rw [form224_val]
  exact form240Step

def form241Matrix : M := !![ofCode 1, ofCode 7, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form241Step : form240Matrix * pc7Matrix = form241Matrix := by decide +kernel
def form241 : UnitMatrix := form240 * pc7
theorem form241_val : form241.val = form241Matrix := by
  change form240.val * pc7Matrix = form241Matrix
  rw [form240_val]
  exact form241Step

def form242Matrix : M := !![ofCode 1, ofCode 7, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form242Step : form240Matrix * pc6Matrix = form242Matrix := by decide +kernel
def form242 : UnitMatrix := form240 * pc6
theorem form242_val : form242.val = form242Matrix := by
  change form240.val * pc6Matrix = form242Matrix
  rw [form240_val]
  exact form242Step

def form243Matrix : M := !![ofCode 1, ofCode 7, ofCode 7, ofCode 2; ofCode 0, ofCode 1, ofCode 5, ofCode 1; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form243Step : form242Matrix * pc7Matrix = form243Matrix := by decide +kernel
def form243 : UnitMatrix := form242 * pc7
theorem form243_val : form243.val = form243Matrix := by
  change form242.val * pc7Matrix = form243Matrix
  rw [form242_val]
  exact form243Step

def form244Matrix : M := !![ofCode 1, ofCode 7, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form244Step : form240Matrix * pc5Matrix = form244Matrix := by decide +kernel
def form244 : UnitMatrix := form240 * pc5
theorem form244_val : form244.val = form244Matrix := by
  change form240.val * pc5Matrix = form244Matrix
  rw [form240_val]
  exact form244Step

def form245Matrix : M := !![ofCode 1, ofCode 7, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form245Step : form244Matrix * pc7Matrix = form245Matrix := by decide +kernel
def form245 : UnitMatrix := form244 * pc7
theorem form245_val : form245.val = form245Matrix := by
  change form244.val * pc7Matrix = form245Matrix
  rw [form244_val]
  exact form245Step

def form246Matrix : M := !![ofCode 1, ofCode 7, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form246Step : form244Matrix * pc6Matrix = form246Matrix := by decide +kernel
def form246 : UnitMatrix := form244 * pc6
theorem form246_val : form246.val = form246Matrix := by
  change form244.val * pc6Matrix = form246Matrix
  rw [form244_val]
  exact form246Step

def form247Matrix : M := !![ofCode 1, ofCode 7, ofCode 6, ofCode 4; ofCode 0, ofCode 1, ofCode 5, ofCode 0; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form247Step : form246Matrix * pc7Matrix = form247Matrix := by decide +kernel
def form247 : UnitMatrix := form246 * pc7
theorem form247_val : form247.val = form247Matrix := by
  change form246.val * pc7Matrix = form247Matrix
  rw [form246_val]
  exact form247Step

def form248Matrix : M := !![ofCode 1, ofCode 7, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form248Step : form240Matrix * pc4Matrix = form248Matrix := by decide +kernel
def form248 : UnitMatrix := form240 * pc4
theorem form248_val : form248.val = form248Matrix := by
  change form240.val * pc4Matrix = form248Matrix
  rw [form240_val]
  exact form248Step

def form249Matrix : M := !![ofCode 1, ofCode 7, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form249Step : form248Matrix * pc7Matrix = form249Matrix := by decide +kernel
def form249 : UnitMatrix := form248 * pc7
theorem form249_val : form249.val = form249Matrix := by
  change form248.val * pc7Matrix = form249Matrix
  rw [form248_val]
  exact form249Step

def form250Matrix : M := !![ofCode 1, ofCode 7, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form250Step : form248Matrix * pc6Matrix = form250Matrix := by decide +kernel
def form250 : UnitMatrix := form248 * pc6
theorem form250_val : form250.val = form250Matrix := by
  change form248.val * pc6Matrix = form250Matrix
  rw [form248_val]
  exact form250Step

def form251Matrix : M := !![ofCode 1, ofCode 7, ofCode 5, ofCode 1; ofCode 0, ofCode 1, ofCode 5, ofCode 3; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form251Step : form250Matrix * pc7Matrix = form251Matrix := by decide +kernel
def form251 : UnitMatrix := form250 * pc7
theorem form251_val : form251.val = form251Matrix := by
  change form250.val * pc7Matrix = form251Matrix
  rw [form250_val]
  exact form251Step

def form252Matrix : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form252Step : form248Matrix * pc5Matrix = form252Matrix := by decide +kernel
def form252 : UnitMatrix := form248 * pc5
theorem form252_val : form252.val = form252Matrix := by
  change form248.val * pc5Matrix = form252Matrix
  rw [form248_val]
  exact form252Step

def form253Matrix : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form253Step : form252Matrix * pc7Matrix = form253Matrix := by decide +kernel
def form253 : UnitMatrix := form252 * pc7
theorem form253_val : form253.val = form253Matrix := by
  change form252.val * pc7Matrix = form253Matrix
  rw [form252_val]
  exact form253Step

def form254Matrix : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form254Step : form252Matrix * pc6Matrix = form254Matrix := by decide +kernel
def form254 : UnitMatrix := form252 * pc6
theorem form254_val : form254.val = form254Matrix := by
  change form252.val * pc6Matrix = form254Matrix
  rw [form252_val]
  exact form254Step

def form255Matrix : M := !![ofCode 1, ofCode 7, ofCode 4, ofCode 7; ofCode 0, ofCode 1, ofCode 5, ofCode 2; ofCode 0, ofCode 0, ofCode 1, ofCode 7; ofCode 0, ofCode 0, ofCode 0, ofCode 1]
private theorem form255Step : form254Matrix * pc7Matrix = form255Matrix := by decide +kernel
def form255 : UnitMatrix := form254 * pc7
theorem form255_val : form255.val = form255Matrix := by
  change form254.val * pc7Matrix = form255Matrix
  rw [form254_val]
  exact form255Step

def form : Fin 256 → UnitMatrix := ![form000, form001, form002, form003, form004, form005, form006, form007, form008, form009, form010, form011, form012, form013, form014, form015, form016, form017, form018, form019, form020, form021, form022, form023, form024, form025, form026, form027, form028, form029, form030, form031, form032, form033, form034, form035, form036, form037, form038, form039, form040, form041, form042, form043, form044, form045, form046, form047, form048, form049, form050, form051, form052, form053, form054, form055, form056, form057, form058, form059, form060, form061, form062, form063, form064, form065, form066, form067, form068, form069, form070, form071, form072, form073, form074, form075, form076, form077, form078, form079, form080, form081, form082, form083, form084, form085, form086, form087, form088, form089, form090, form091, form092, form093, form094, form095, form096, form097, form098, form099, form100, form101, form102, form103, form104, form105, form106, form107, form108, form109, form110, form111, form112, form113, form114, form115, form116, form117, form118, form119, form120, form121, form122, form123, form124, form125, form126, form127, form128, form129, form130, form131, form132, form133, form134, form135, form136, form137, form138, form139, form140, form141, form142, form143, form144, form145, form146, form147, form148, form149, form150, form151, form152, form153, form154, form155, form156, form157, form158, form159, form160, form161, form162, form163, form164, form165, form166, form167, form168, form169, form170, form171, form172, form173, form174, form175, form176, form177, form178, form179, form180, form181, form182, form183, form184, form185, form186, form187, form188, form189, form190, form191, form192, form193, form194, form195, form196, form197, form198, form199, form200, form201, form202, form203, form204, form205, form206, form207, form208, form209, form210, form211, form212, form213, form214, form215, form216, form217, form218, form219, form220, form221, form222, form223, form224, form225, form226, form227, form228, form229, form230, form231, form232, form233, form234, form235, form236, form237, form238, form239, form240, form241, form242, form243, form244, form245, form246, form247, form248, form249, form250, form251, form252, form253, form254, form255]

def raw : Fin 256 → M := ![form000Matrix, form001Matrix, form002Matrix, form003Matrix, form004Matrix, form005Matrix, form006Matrix, form007Matrix, form008Matrix, form009Matrix, form010Matrix, form011Matrix, form012Matrix, form013Matrix, form014Matrix, form015Matrix, form016Matrix, form017Matrix, form018Matrix, form019Matrix, form020Matrix, form021Matrix, form022Matrix, form023Matrix, form024Matrix, form025Matrix, form026Matrix, form027Matrix, form028Matrix, form029Matrix, form030Matrix, form031Matrix, form032Matrix, form033Matrix, form034Matrix, form035Matrix, form036Matrix, form037Matrix, form038Matrix, form039Matrix, form040Matrix, form041Matrix, form042Matrix, form043Matrix, form044Matrix, form045Matrix, form046Matrix, form047Matrix, form048Matrix, form049Matrix, form050Matrix, form051Matrix, form052Matrix, form053Matrix, form054Matrix, form055Matrix, form056Matrix, form057Matrix, form058Matrix, form059Matrix, form060Matrix, form061Matrix, form062Matrix, form063Matrix, form064Matrix, form065Matrix, form066Matrix, form067Matrix, form068Matrix, form069Matrix, form070Matrix, form071Matrix, form072Matrix, form073Matrix, form074Matrix, form075Matrix, form076Matrix, form077Matrix, form078Matrix, form079Matrix, form080Matrix, form081Matrix, form082Matrix, form083Matrix, form084Matrix, form085Matrix, form086Matrix, form087Matrix, form088Matrix, form089Matrix, form090Matrix, form091Matrix, form092Matrix, form093Matrix, form094Matrix, form095Matrix, form096Matrix, form097Matrix, form098Matrix, form099Matrix, form100Matrix, form101Matrix, form102Matrix, form103Matrix, form104Matrix, form105Matrix, form106Matrix, form107Matrix, form108Matrix, form109Matrix, form110Matrix, form111Matrix, form112Matrix, form113Matrix, form114Matrix, form115Matrix, form116Matrix, form117Matrix, form118Matrix, form119Matrix, form120Matrix, form121Matrix, form122Matrix, form123Matrix, form124Matrix, form125Matrix, form126Matrix, form127Matrix, form128Matrix, form129Matrix, form130Matrix, form131Matrix, form132Matrix, form133Matrix, form134Matrix, form135Matrix, form136Matrix, form137Matrix, form138Matrix, form139Matrix, form140Matrix, form141Matrix, form142Matrix, form143Matrix, form144Matrix, form145Matrix, form146Matrix, form147Matrix, form148Matrix, form149Matrix, form150Matrix, form151Matrix, form152Matrix, form153Matrix, form154Matrix, form155Matrix, form156Matrix, form157Matrix, form158Matrix, form159Matrix, form160Matrix, form161Matrix, form162Matrix, form163Matrix, form164Matrix, form165Matrix, form166Matrix, form167Matrix, form168Matrix, form169Matrix, form170Matrix, form171Matrix, form172Matrix, form173Matrix, form174Matrix, form175Matrix, form176Matrix, form177Matrix, form178Matrix, form179Matrix, form180Matrix, form181Matrix, form182Matrix, form183Matrix, form184Matrix, form185Matrix, form186Matrix, form187Matrix, form188Matrix, form189Matrix, form190Matrix, form191Matrix, form192Matrix, form193Matrix, form194Matrix, form195Matrix, form196Matrix, form197Matrix, form198Matrix, form199Matrix, form200Matrix, form201Matrix, form202Matrix, form203Matrix, form204Matrix, form205Matrix, form206Matrix, form207Matrix, form208Matrix, form209Matrix, form210Matrix, form211Matrix, form212Matrix, form213Matrix, form214Matrix, form215Matrix, form216Matrix, form217Matrix, form218Matrix, form219Matrix, form220Matrix, form221Matrix, form222Matrix, form223Matrix, form224Matrix, form225Matrix, form226Matrix, form227Matrix, form228Matrix, form229Matrix, form230Matrix, form231Matrix, form232Matrix, form233Matrix, form234Matrix, form235Matrix, form236Matrix, form237Matrix, form238Matrix, form239Matrix, form240Matrix, form241Matrix, form242Matrix, form243Matrix, form244Matrix, form245Matrix, form246Matrix, form247Matrix, form248Matrix, form249Matrix, form250Matrix, form251Matrix, form252Matrix, form253Matrix, form254Matrix, form255Matrix]

theorem form_val (i : Fin 256) : (form i).val = raw i := by
  fin_cases i
  · exact form000_val
  · exact form001_val
  · exact form002_val
  · exact form003_val
  · exact form004_val
  · exact form005_val
  · exact form006_val
  · exact form007_val
  · exact form008_val
  · exact form009_val
  · exact form010_val
  · exact form011_val
  · exact form012_val
  · exact form013_val
  · exact form014_val
  · exact form015_val
  · exact form016_val
  · exact form017_val
  · exact form018_val
  · exact form019_val
  · exact form020_val
  · exact form021_val
  · exact form022_val
  · exact form023_val
  · exact form024_val
  · exact form025_val
  · exact form026_val
  · exact form027_val
  · exact form028_val
  · exact form029_val
  · exact form030_val
  · exact form031_val
  · exact form032_val
  · exact form033_val
  · exact form034_val
  · exact form035_val
  · exact form036_val
  · exact form037_val
  · exact form038_val
  · exact form039_val
  · exact form040_val
  · exact form041_val
  · exact form042_val
  · exact form043_val
  · exact form044_val
  · exact form045_val
  · exact form046_val
  · exact form047_val
  · exact form048_val
  · exact form049_val
  · exact form050_val
  · exact form051_val
  · exact form052_val
  · exact form053_val
  · exact form054_val
  · exact form055_val
  · exact form056_val
  · exact form057_val
  · exact form058_val
  · exact form059_val
  · exact form060_val
  · exact form061_val
  · exact form062_val
  · exact form063_val
  · exact form064_val
  · exact form065_val
  · exact form066_val
  · exact form067_val
  · exact form068_val
  · exact form069_val
  · exact form070_val
  · exact form071_val
  · exact form072_val
  · exact form073_val
  · exact form074_val
  · exact form075_val
  · exact form076_val
  · exact form077_val
  · exact form078_val
  · exact form079_val
  · exact form080_val
  · exact form081_val
  · exact form082_val
  · exact form083_val
  · exact form084_val
  · exact form085_val
  · exact form086_val
  · exact form087_val
  · exact form088_val
  · exact form089_val
  · exact form090_val
  · exact form091_val
  · exact form092_val
  · exact form093_val
  · exact form094_val
  · exact form095_val
  · exact form096_val
  · exact form097_val
  · exact form098_val
  · exact form099_val
  · exact form100_val
  · exact form101_val
  · exact form102_val
  · exact form103_val
  · exact form104_val
  · exact form105_val
  · exact form106_val
  · exact form107_val
  · exact form108_val
  · exact form109_val
  · exact form110_val
  · exact form111_val
  · exact form112_val
  · exact form113_val
  · exact form114_val
  · exact form115_val
  · exact form116_val
  · exact form117_val
  · exact form118_val
  · exact form119_val
  · exact form120_val
  · exact form121_val
  · exact form122_val
  · exact form123_val
  · exact form124_val
  · exact form125_val
  · exact form126_val
  · exact form127_val
  · exact form128_val
  · exact form129_val
  · exact form130_val
  · exact form131_val
  · exact form132_val
  · exact form133_val
  · exact form134_val
  · exact form135_val
  · exact form136_val
  · exact form137_val
  · exact form138_val
  · exact form139_val
  · exact form140_val
  · exact form141_val
  · exact form142_val
  · exact form143_val
  · exact form144_val
  · exact form145_val
  · exact form146_val
  · exact form147_val
  · exact form148_val
  · exact form149_val
  · exact form150_val
  · exact form151_val
  · exact form152_val
  · exact form153_val
  · exact form154_val
  · exact form155_val
  · exact form156_val
  · exact form157_val
  · exact form158_val
  · exact form159_val
  · exact form160_val
  · exact form161_val
  · exact form162_val
  · exact form163_val
  · exact form164_val
  · exact form165_val
  · exact form166_val
  · exact form167_val
  · exact form168_val
  · exact form169_val
  · exact form170_val
  · exact form171_val
  · exact form172_val
  · exact form173_val
  · exact form174_val
  · exact form175_val
  · exact form176_val
  · exact form177_val
  · exact form178_val
  · exact form179_val
  · exact form180_val
  · exact form181_val
  · exact form182_val
  · exact form183_val
  · exact form184_val
  · exact form185_val
  · exact form186_val
  · exact form187_val
  · exact form188_val
  · exact form189_val
  · exact form190_val
  · exact form191_val
  · exact form192_val
  · exact form193_val
  · exact form194_val
  · exact form195_val
  · exact form196_val
  · exact form197_val
  · exact form198_val
  · exact form199_val
  · exact form200_val
  · exact form201_val
  · exact form202_val
  · exact form203_val
  · exact form204_val
  · exact form205_val
  · exact form206_val
  · exact form207_val
  · exact form208_val
  · exact form209_val
  · exact form210_val
  · exact form211_val
  · exact form212_val
  · exact form213_val
  · exact form214_val
  · exact form215_val
  · exact form216_val
  · exact form217_val
  · exact form218_val
  · exact form219_val
  · exact form220_val
  · exact form221_val
  · exact form222_val
  · exact form223_val
  · exact form224_val
  · exact form225_val
  · exact form226_val
  · exact form227_val
  · exact form228_val
  · exact form229_val
  · exact form230_val
  · exact form231_val
  · exact form232_val
  · exact form233_val
  · exact form234_val
  · exact form235_val
  · exact form236_val
  · exact form237_val
  · exact form238_val
  · exact form239_val
  · exact form240_val
  · exact form241_val
  · exact form242_val
  · exact form243_val
  · exact form244_val
  · exact form245_val
  · exact form246_val
  · exact form247_val
  · exact form248_val
  · exact form249_val
  · exact form250_val
  · exact form251_val
  · exact form252_val
  · exact form253_val
  · exact form254_val
  · exact form255_val

end Kourovka2135.SuzukiEightCoverCodeForms
