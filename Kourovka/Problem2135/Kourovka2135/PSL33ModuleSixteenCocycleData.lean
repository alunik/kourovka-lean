import Kourovka2135.PSL33ModuleSixteen
import Kourovka2135.CocycleWordConcatenation

/-! Short, literal append/doubling certificates for three actual relations and
cocycle-derivative matrices. Every multiplication is checked by ordinary
kernel reduction; no finite-presentation assertion is used. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
open Kourovka2135.BinaryFieldSixteen
namespace Kourovka2135.PSL33ModuleSixteenCohomology
open PSL33ModuleSixteen SL33ProjectiveData PSL33SingerSixteenData
open CocycleGeneratorEvaluation CocycleWordConcatenation

def gens : Fin 2 → Q := ![PSL33GoodSets.q a, PSL33GoodSets.q b]
def lifts : Fin 2 → S := ![a, b]
def ops : Fin 2 → Module.End k V := ![leftA.mulVecLin, leftB.mulVecLin]

theorem generators_generate : Subgroup.closure (Set.range gens) = ⊤ := by
  have he : Set.range gens = {PSL33GoodSets.q a, PSL33GoodSets.q b} := by
    exact Matrix.range_cons_cons_empty _ _ _
  rw [he]
  exact generating_projective

theorem generator_operators (i : Fin 2) : representation (gens i) = ops i := by
  fin_cases i
  · change representation (PSL33GoodSets.q a) = leftA.mulVecLin
    have h := congrArg Matrix.toLin' toMatrix_a
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_apply'] at h
    exact h
  · change representation (PSL33GoodSets.q b) = leftB.mulVecLin
    have h := congrArg Matrix.toLin' toMatrix_b
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_apply'] at h
    exact h

theorem wordValue_map (word : List (Fin 2)) :
    wordValue gens word = PSL33GoodSets.q (wordValue lifts word) := by
  induction word with
  | nil => exact (map_one _).symm
  | cons i word ih =>
      change gens i * wordValue gens word = PSL33GoodSets.q (lifts i * wordValue lifts word)
      rw [map_mul, ih]
      congr 1
      fin_cases i <;> rfl

def packedMatrix {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) k :=
  fun i j => ofBits ((rows i).shiftRight (4 * j.val))

def word0 : List (Fin 2) := [0]
def group0 : S := a
def matrix0 : Matrix (Fin 16) (Fin 16) k := leftA
def derivative0Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]) i j else (packedMatrix ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i j
def derivative0 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative0Rows i t.1 t.2

theorem value0 : wordValue lifts word0 = group0 := by
  simp [word0, group0, wordValue, lifts]
theorem operator0 : operatorMatrix representation gens word0 = matrix0 := by
  simpa [operatorMatrix, word0, wordValue, gens, matrix0] using toMatrix_a
theorem jacobian0 : derivativeMatrix representation gens word0 = derivative0 := by
  ext i t
  rw [derivativeMatrix_entry]
  simp only [word0, wordDerivative, LinearMap.comp_zero, zero_add, LinearMap.proj_apply]
  change (Pi.single t.1 (Pi.single t.2 (1 : k)) : Fin 2 → Fin 16 → k) (0 : Fin 2) i = derivative0 i t
  rcases t with ⟨t, q⟩
  fin_cases i <;> fin_cases t <;> fin_cases q <;> decide +kernel

def word1 : List (Fin 2) := [1]
def group1 : S := b
def matrix1 : Matrix (Fin 16) (Fin 16) k := leftB
def derivative1Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i j else (packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]) i j
def derivative1 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative1Rows i t.1 t.2

theorem value1 : wordValue lifts word1 = group1 := by
  simp [word1, group1, wordValue, lifts]
theorem operator1 : operatorMatrix representation gens word1 = matrix1 := by
  simpa [operatorMatrix, word1, wordValue, gens, matrix1] using toMatrix_b
theorem jacobian1 : derivativeMatrix representation gens word1 = derivative1 := by
  ext i t
  rw [derivativeMatrix_entry]
  simp only [word1, wordDerivative, LinearMap.comp_zero, zero_add, LinearMap.proj_apply]
  change (Pi.single t.1 (Pi.single t.2 (1 : k)) : Fin 2 → Fin 16 → k) (1 : Fin 2) i = derivative1 i t
  rcases t with ⟨t, q⟩
  fin_cases i <;> fin_cases t <;> fin_cases q <;> decide +kernel

def word2 : List (Fin 2) := word0 ++ word0
def group2 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide +kernel⟩
def matrix2 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]
def derivative2Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![15134629122266890257, 9227595261017063441, 16936350448191803648, 12469342567793692928, 6198641937123180544, 10594155173436784640, 17008408046541471744, 4685995481266913280, 4038604069667864576, 6127147362025472000, 13836746905142427648, 3106093960188133376, 13402712491054596096, 17157324797584080896, 4323455642275676160, 14195346025471803392]) i j else (packedMatrix ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i j
def derivative2 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative2Rows i t.1 t.2

theorem value2 : wordValue lifts word2 = group2 := by
  rw [word2, wordValue_append, value0]
  decide +kernel
theorem operator2 : operatorMatrix representation gens word2 = matrix2 := by
  rw [word2, operatorMatrix_append, operator0]
  decide +kernel
theorem jacobian2 : derivativeMatrix representation gens word2 = derivative2 := by
  rw [word2, derivativeMatrix_append, operator0, jacobian0]
  decide +kernel

def word3 : List (Fin 2) := word1 ++ word1
def group3 : S := ⟨!![1, 1, 0;
    1, 2, 1;
    2, 1, 0], by decide +kernel⟩
def matrix3 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![49539595901075712, 16, 49539595901075729, 4503599644147712, 45035996273709056, 67555093922185216, 49539595901140992, 1048576, 121597189939003392, 1197957500880551936, 67553994678992896, 18014402804449280, 45036064993181696, 4503599627370496, 67571586596601856, 281474976710656]
def derivative3Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i j else (packedMatrix ![272, 0, 49539595901075713, 45035996273774592, 49539595917918208, 269484032, 4503599644151808, 67555094190620672, 18031994990493696, 45317539969892352, 67555093923233792, 139629180634529792, 1153202979583557632, 0, 121597194233970688, 1197957569600028672]) i j
def derivative3 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative3Rows i t.1 t.2

theorem value3 : wordValue lifts word3 = group3 := by
  rw [word3, wordValue_append, value1]
  decide +kernel
theorem operator3 : operatorMatrix representation gens word3 = matrix3 := by
  rw [word3, operatorMatrix_append, operator1]
  decide +kernel
theorem jacobian3 : derivativeMatrix representation gens word3 = derivative3 := by
  rw [word3, derivativeMatrix_append, operator1, jacobian1]
  decide +kernel

def word4 : List (Fin 2) := word3 ++ word1
def group4 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide +kernel⟩
def matrix4 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]
def derivative4Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i j else (packedMatrix ![49539595901075472, 16, 16, 49539595917922304, 4503599644217344, 67555094191669248, 45035996290551808, 67555094191669248, 139629184929497088, 1153203048303034368, 1099781111808, 121614786420015104, 1198239044576739328, 4503599627370496, 90089589028421632, 1198239044576739328]) i j
def derivative4 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative4Rows i t.1 t.2

theorem value4 : wordValue lifts word4 = group4 := by
  rw [word4, wordValue_append, value3, value1]
  decide +kernel
theorem operator4 : operatorMatrix representation gens word4 = matrix4 := by
  rw [word4, operatorMatrix_append, operator3, operator1]
  decide +kernel
theorem jacobian4 : derivativeMatrix representation gens word4 = derivative4 := by
  rw [word4, derivativeMatrix_append, operator3, jacobian1, jacobian3]
  decide +kernel

def word5 : List (Fin 2) := word0 ++ word1
def group5 : S := ⟨!![1, 0, 1;
    1, 0, 2;
    0, 2, 0], by decide +kernel⟩
def matrix5 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![10380798043033174032, 17293823118859567377, 11574252051660603392, 13880094794586259457, 6967068993177780224, 6917529659018051584, 11529233651867844608, 9291207785414918144, 13853072694310866944, 9268409497712328704, 6980580247059038208, 12749690729769467904, 1152922303470764032, 12758698766542831616, 49539857894080512, 45036911101739008]
def derivative5Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]) i j else (packedMatrix ![15134629122266890256, 9227595261017063425, 16936350448191803392, 12469342567793688832, 6198641937123115008, 10594155173435736064, 17008408046524694528, 4685995480998477824, 4038604065372897280, 6127147293305995264, 13836748004654055424, 3106076368002088960, 13402993966031306752, 17152821197956710400, 4395513236313604096, 15348267530078650368]) i j
def derivative5 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative5Rows i t.1 t.2

theorem value5 : wordValue lifts word5 = group5 := by
  rw [word5, wordValue_append, value0, value1]
  decide +kernel
theorem operator5 : operatorMatrix representation gens word5 = matrix5 := by
  rw [word5, operatorMatrix_append, operator0, operator1]
  decide +kernel
theorem jacobian5 : derivativeMatrix representation gens word5 = derivative5 := by
  rw [word5, derivativeMatrix_append, operator0, jacobian1, jacobian0]
  decide +kernel

def word6 : List (Fin 2) := word5 ++ word0
def group6 : S := ⟨!![2, 0, 2;
    1, 1, 1;
    1, 0, 0], by decide +kernel⟩
def matrix6 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![12180850511397847041, 12827941690270617617, 14053107707688321024, 1729852850789482512, 14051712493651230720, 9297965111467573248, 4979587011087237120, 10234695136592265216, 11025173628068102400, 6053862645449097216, 4324827836008431616, 8722904031426510848, 1947254887121158144, 10954476132967120896, 3819541767707951104, 6055552596968472576]
def derivative6Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![10380798043033174033, 17293823118859567361, 11574252051660603648, 13880094794586263553, 6967068993177845760, 6917529659019100160, 11529233651884621824, 9291207785683353600, 13853072698605834240, 9268409428992851968, 6980581346570665984, 12749708321955512320, 1153203778447474688, 12754195166915461120, 121597451932008448, 1197958415708585984]) i j else (packedMatrix ![15134629122266890256, 9227595261017063425, 16936350448191803392, 12469342567793688832, 6198641937123115008, 10594155173435736064, 17008408046524694528, 4685995480998477824, 4038604065372897280, 6127147293305995264, 13836748004654055424, 3106076368002088960, 13402993966031306752, 17152821197956710400, 4395513236313604096, 15348267530078650368]) i j
def derivative6 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative6Rows i t.1 t.2

theorem value6 : wordValue lifts word6 = group6 := by
  rw [word6, wordValue_append, value5, value0]
  decide +kernel
theorem operator6 : operatorMatrix representation gens word6 = matrix6 := by
  rw [word6, operatorMatrix_append, operator5, operator0]
  decide +kernel
theorem jacobian6 : derivativeMatrix representation gens word6 = derivative6 := by
  rw [word6, derivativeMatrix_append, operator5, jacobian0, jacobian5]
  decide +kernel

def word7 : List (Fin 2) := word6 ++ word1
def group7 : S := ⟨!![1, 2, 1;
    1, 1, 1;
    2, 0, 1], by decide +kernel⟩
def matrix7 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![12785734361625403665, 6953567385275138305, 7660639197135417344, 1887019342093144080, 1954850048338583552, 10376321583305207808, 12700166638729740288, 10349276951630319616, 1459170234959167489, 4215375109558390784, 5647527384576950272, 16068846189183807488, 6944562836007854080, 7003113466573676544, 1977083762597482496, 11123905734038802432]
def derivative7Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![10380798043033174033, 17293823118859567361, 11574252051660603648, 13880094794586263553, 6967068993177845760, 6917529659019100160, 11529233651884621824, 9291207785683353600, 13853072698605834240, 9268409428992851968, 6980581346570665984, 12749708321955512320, 1153203778447474688, 12754195166915461120, 121597451932008448, 1197958415708585984]) i j else (packedMatrix ![8863666811351138321, 3605412978834346000, 2885868382158131200, 13046273913976324368, 10738752017767858176, 1301261023117901824, 12182532768919519232, 14916187017963372544, 11605010980597203200, 75334139846328320, 18159324040848801792, 5915191138737717248, 11603253963180212224, 8506470668328501248, 576950036001193984, 9298144328675229696]) i j
def derivative7 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative7Rows i t.1 t.2

theorem value7 : wordValue lifts word7 = group7 := by
  rw [word7, wordValue_append, value6, value1]
  decide +kernel
theorem operator7 : operatorMatrix representation gens word7 = matrix7 := by
  rw [word7, operatorMatrix_append, operator6, operator1]
  decide +kernel
theorem jacobian7 : derivativeMatrix representation gens word7 = derivative7 := by
  rw [word7, derivativeMatrix_append, operator6, jacobian1, jacobian6]
  decide +kernel

def word8 : List (Fin 2) := word7 ++ word1
def group8 : S := ⟨!![0, 1, 0;
    1, 1, 1;
    1, 1, 0], by decide +kernel⟩
def matrix8 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![66024235252977920, 52671417627447568, 48468030298722304, 4925926994153488, 1169862897347985408, 83334804314193920, 46250616261709824, 34023902262919168, 70245687194292497, 10485193069887488, 5559465810071552, 29151213008912384, 18489802546085888, 7178032291643392, 32457702709723136, 23996404545683456]
def derivative8Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![10380798043033174033, 17293823118859567361, 11574252051660603648, 13880094794586263553, 6967068993177845760, 6917529659019100160, 11529233651884621824, 9291207785683353600, 13853072698605834240, 9268409428992851968, 6980581346570665984, 12749708321955512320, 1153203778447474688, 12754195166915461120, 121597451932008448, 1197958415708585984]) i j else (packedMatrix ![14587756957259604224, 5947294345681965329, 4781878065991098368, 12627432654636175616, 10243072122770448384, 9371739588619481088, 1824242918643318784, 4656992074746302464, 13064181215522816257, 4290700453311696896, 12854097131660705792, 10166587507654832128, 13936108790528122880, 1674495293294436352, 1401110094968573952, 1975294993888202752]) i j
def derivative8 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative8Rows i t.1 t.2

theorem value8 : wordValue lifts word8 = group8 := by
  rw [word8, wordValue_append, value7, value1]
  decide +kernel
theorem operator8 : operatorMatrix representation gens word8 = matrix8 := by
  rw [word8, operatorMatrix_append, operator7, operator1]
  decide +kernel
theorem jacobian8 : derivativeMatrix representation gens word8 = derivative8 := by
  rw [word8, derivativeMatrix_append, operator7, jacobian1, jacobian7]
  decide +kernel

def word9 : List (Fin 2) := word8 ++ word8
def group9 : S := ⟨!![1, 1, 1;
    2, 0, 1;
    1, 2, 1], by decide +kernel⟩
def matrix9 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![3260678293459505409, 644825433629655296, 13693617777140804282, 15733713291623377834, 7319739797798894523, 4172180437978644480, 14890325339994984464, 1471762356429127679, 9494591938695939140, 6188192662615993002, 883550642580946686, 12859308487660994559, 12358898274865643520, 17184998134361886993, 15204944543089867707, 6749400989610388138]
def derivative9Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![6839168037020696848, 4303812051430609153, 16868012442101920001, 125399000938291457, 1407992096491024384, 16368923893718777856, 772450048841355265, 15530918887363309568, 14965621468005220369, 16321399745538269184, 3599437766848475137, 1629333046792286208, 17603082565621252096, 16147523333087170560, 3949183275809746944, 1580843914170310656]) i j else (packedMatrix ![1487934657560150273, 10299801090153591040, 8705169277131791114, 15326331812231256859, 5098023759636208395, 7351192839986405376, 3424800716578791680, 2546166935726059279, 16034097474848662548, 11704818389903944202, 4088492209040699150, 1799389454116167439, 17716028618900717568, 7294417703205314817, 15859417408993819403, 11910666356488866314]) i j
def derivative9 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative9Rows i t.1 t.2

theorem value9 : wordValue lifts word9 = group9 := by
  rw [word9, wordValue_append, value8]
  decide +kernel
theorem operator9 : operatorMatrix representation gens word9 = matrix9 := by
  rw [word9, operatorMatrix_append, operator8]
  decide +kernel
theorem jacobian9 : derivativeMatrix representation gens word9 = derivative9 := by
  rw [word9, derivativeMatrix_append, operator8, jacobian8]
  decide +kernel

def word10 : List (Fin 2) := word9 ++ word9
def group10 : S := ⟨!![1, 0, 0;
    0, 1, 0;
    0, 0, 1], by decide +kernel⟩
def matrix10 : Matrix (Fin 16) (Fin 16) k :=
  packedMatrix ![1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]
def derivative10Rows : Fin 16 → Fin 2 → Fin 16 → k :=
  fun i t j => if t = 0 then (packedMatrix ![1810570920192442384, 8522853396215103488, 8772890248211529915, 18369519162659373227, 3050576164410818747, 11373886619922595840, 16946018639568044048, 15830600678650216703, 7063778915162980437, 10064067324242559146, 16059556119650304239, 17900503631479046399, 763781064357576704, 9335903938804383761, 3730831814834782395, 3991337552192405674]) i j else (packedMatrix ![10340697529669882113, 6229991582054096896, 8146212864286884016, 14672803249891508657, 6749508641623376048, 7818485771682242560, 9098573537915543809, 17822232423691182320, 15251017780303470672, 9889092793480716448, 5418687274120159729, 3241875008129175792, 15248813219403481088, 6238049895127228432, 10852422335155466416, 5827048079470825632]) i j
def derivative10 : Matrix (Fin 16) (Fin 2 × Fin 16) k :=
  fun i t => derivative10Rows i t.1 t.2

theorem value10 : wordValue lifts word10 = group10 := by
  rw [word10, wordValue_append, value9]
  decide +kernel
theorem operator10 : operatorMatrix representation gens word10 = matrix10 := by
  rw [word10, operatorMatrix_append, operator9]
  decide +kernel
theorem jacobian10 : derivativeMatrix representation gens word10 = derivative10 := by
  rw [word10, derivativeMatrix_append, operator9, jacobian9]
  decide +kernel

def words : Fin 3 → List (Fin 2) := ![word2, word4, word10]
def certifiedDerivatives : Fin 3 → Matrix (Fin 16) (Fin 2 × Fin 16) k := ![derivative2, derivative4, derivative10]

theorem actual_relations (i : Fin 3) : wordValue gens (words i) = 1 := by
  rw [wordValue_map]
  fin_cases i
  · change PSL33GoodSets.q (wordValue lifts word2) = 1
    rw [value2, show group2 = 1 from by decide +kernel, map_one]
  · change PSL33GoodSets.q (wordValue lifts word4) = 1
    rw [value4, show group4 = 1 from by decide +kernel, map_one]
  · change PSL33GoodSets.q (wordValue lifts word10) = 1
    rw [value10, show group10 = 1 from by decide +kernel, map_one]

theorem certified_derivative (i : Fin 3) :
    derivativeMatrix representation gens (words i) = certifiedDerivatives i := by
  fin_cases i
  · exact jacobian2
  · exact jacobian4
  · exact jacobian10

end Kourovka2135.PSL33ModuleSixteenCohomology
