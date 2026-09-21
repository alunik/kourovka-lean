import Kourovka2135.SL33ProjectiveData
import Kourovka2135.PSLThreeThreeSemidihedralData
import Kourovka2135.SubactionCertificate
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases

/-! A genuine 144-point action of PSL3(3). The indexed objects are explicit
39-element translates inside the actual SL3 matrix group. Generator edges
and distinct minimum matrix codes certify an invariant indexed subset of
its left translation action. No finite-presentation recognition is used. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace Kourovka2135.PSL33SingerCosetData
open SL33ProjectiveData
open scoped Pointwise

def memberMatrix : Fin 39 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![0, 0, 2; 0, 1, 0; 1, 1, 2],
    !![0, 0, 2; 1, 1, 1; 2, 1, 2],
    !![0, 0, 2; 2, 1, 1; 0, 1, 1],
    !![0, 1, 0; 0, 2, 1; 1, 2, 2],
    !![0, 1, 0; 1, 0, 2; 2, 1, 0],
    !![0, 1, 0; 2, 2, 0; 0, 1, 1],
    !![0, 2, 1; 0, 0, 2; 1, 1, 0],
    !![0, 2, 1; 1, 0, 1; 2, 0, 0],
    !![0, 2, 1; 2, 2, 1; 0, 1, 1],
    !![0, 2, 2; 2, 1, 1; 2, 0, 2],
    !![0, 2, 2; 2, 2, 0; 2, 2, 2],
    !![0, 2, 2; 2, 2, 1; 2, 0, 1],
    !![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 2, 2; 2, 1, 0],
    !![1, 0, 0; 1, 0, 1; 2, 2, 2],
    !![1, 0, 1; 1, 0, 2; 0, 2, 0],
    !![1, 0, 1; 1, 2, 1; 1, 1, 0],
    !![1, 0, 1; 2, 1, 1; 0, 0, 1],
    !![1, 0, 2; 1, 0, 0; 1, 2, 2],
    !![1, 0, 2; 1, 1, 1; 0, 0, 1],
    !![1, 0, 2; 2, 2, 1; 0, 1, 2],
    !![1, 1, 1; 1, 0, 1; 0, 1, 2],
    !![1, 1, 1; 1, 2, 0; 1, 1, 2],
    !![1, 1, 1; 2, 2, 0; 0, 2, 0],
    !![1, 2, 0; 0, 0, 2; 0, 1, 2],
    !![1, 2, 0; 0, 2, 2; 2, 1, 2],
    !![1, 2, 0; 1, 0, 2; 2, 0, 2],
    !![1, 2, 1; 0, 2, 1; 0, 2, 0],
    !![1, 2, 1; 0, 2, 2; 2, 0, 0],
    !![1, 2, 1; 1, 1, 1; 2, 0, 1],
    !![2, 1, 1; 0, 2, 1; 2, 1, 2],
    !![2, 1, 1; 1, 0, 0; 1, 1, 0],
    !![2, 1, 1; 1, 2, 0; 2, 2, 2],
    !![2, 2, 0; 0, 0, 2; 2, 1, 0],
    !![2, 2, 0; 1, 0, 0; 2, 0, 1],
    !![2, 2, 0; 1, 2, 1; 1, 1, 2],
    !![2, 2, 1; 0, 1, 0; 2, 0, 0],
    !![2, 2, 1; 1, 2, 0; 1, 2, 2],
    !![2, 2, 1; 1, 2, 1; 2, 0, 2]]

private theorem memberMatrix_det (i : Fin 39) : (memberMatrix i).det = 1 := by
  revert i
  decide +kernel

def representativeMatrix : Fin 144 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![0, 2, 0; 2, 0, 0; 2, 1, 2],
    !![2, 2, 2; 1, 0, 1; 1, 1, 2],
    !![2, 0, 2; 1, 1, 1; 1, 0, 0],
    !![2, 0, 1; 0, 0, 1; 2, 1, 1],
    !![0, 0, 2; 1, 0, 2; 2, 2, 2],
    !![0, 1, 0; 2, 2, 1; 2, 1, 2],
    !![2, 2, 0; 1, 1, 2; 0, 2, 1],
    !![1, 1, 2; 0, 2, 0; 0, 0, 2],
    !![2, 2, 1; 1, 1, 0; 2, 0, 1],
    !![1, 0, 1; 1, 2, 2; 1, 0, 0],
    !![2, 2, 0; 2, 2, 2; 0, 2, 2],
    !![0, 1, 0; 2, 1, 1; 0, 1, 1],
    !![2, 1, 1; 2, 0, 2; 2, 2, 1],
    !![1, 1, 1; 1, 1, 0; 0, 1, 0],
    !![1, 0, 2; 1, 2, 1; 2, 1, 1],
    !![1, 2, 2; 0, 2, 0; 2, 2, 0],
    !![0, 0, 1; 0, 1, 2; 2, 2, 2],
    !![2, 0, 2; 2, 1, 2; 1, 2, 0],
    !![2, 1, 2; 2, 0, 1; 1, 1, 1],
    !![1, 0, 1; 0, 2, 1; 2, 1, 0],
    !![0, 2, 1; 0, 0, 2; 1, 2, 2],
    !![1, 2, 1; 1, 0, 1; 2, 2, 0],
    !![2, 0, 2; 0, 1, 0; 0, 1, 2],
    !![0, 1, 2; 2, 0, 2; 0, 1, 0],
    !![1, 1, 2; 0, 2, 2; 2, 0, 1],
    !![1, 0, 1; 2, 2, 0; 1, 2, 1],
    !![1, 0, 2; 0, 2, 2; 0, 2, 1],
    !![0, 2, 0; 1, 0, 1; 1, 0, 2],
    !![1, 1, 0; 1, 2, 2; 0, 2, 2],
    !![0, 0, 1; 0, 1, 1; 2, 1, 2],
    !![0, 1, 1; 2, 2, 1; 0, 1, 2],
    !![1, 1, 0; 2, 0, 2; 0, 0, 1],
    !![0, 2, 0; 1, 1, 1; 0, 1, 1],
    !![2, 2, 2; 2, 1, 0; 0, 1, 0],
    !![1, 1, 2; 2, 1, 1; 2, 0, 0],
    !![2, 1, 1; 2, 2, 0; 0, 2, 0],
    !![2, 1, 1; 1, 2, 0; 2, 2, 0],
    !![2, 2, 1; 2, 2, 2; 2, 0, 0],
    !![2, 2, 2; 0, 1, 0; 1, 1, 0],
    !![1, 2, 0; 1, 1, 1; 0, 1, 1],
    !![1, 2, 2; 2, 2, 1; 2, 0, 2],
    !![1, 2, 1; 0, 2, 1; 1, 1, 1],
    !![1, 1, 2; 1, 0, 2; 2, 1, 0],
    !![2, 1, 0; 1, 2, 2; 0, 2, 2],
    !![1, 1, 1; 1, 1, 2; 1, 0, 1],
    !![0, 1, 2; 2, 1, 2; 1, 2, 2],
    !![2, 2, 1; 0, 0, 1; 1, 2, 0],
    !![2, 2, 1; 2, 0, 2; 1, 2, 2],
    !![1, 1, 0; 0, 1, 2; 1, 2, 0],
    !![2, 0, 1; 2, 2, 1; 1, 1, 0],
    !![1, 0, 1; 0, 1, 1; 0, 1, 2],
    !![1, 1, 2; 1, 0, 1; 1, 1, 1],
    !![0, 2, 0; 1, 2, 1; 2, 1, 0],
    !![0, 0, 2; 1, 1, 2; 0, 2, 0],
    !![2, 0, 2; 0, 2, 2; 1, 2, 1],
    !![2, 0, 1; 0, 2, 0; 0, 2, 1],
    !![0, 2, 1; 2, 2, 0; 1, 1, 2],
    !![0, 1, 0; 1, 0, 0; 1, 0, 2],
    !![2, 0, 2; 2, 2, 1; 2, 1, 1],
    !![0, 0, 2; 1, 1, 0; 2, 1, 2],
    !![2, 1, 2; 0, 1, 0; 2, 2, 1],
    !![2, 2, 0; 1, 0, 0; 0, 0, 1],
    !![0, 2, 1; 0, 1, 1; 1, 0, 2],
    !![0, 1, 1; 1, 0, 1; 0, 0, 2],
    !![0, 1, 0; 1, 0, 2; 1, 0, 1],
    !![1, 2, 1; 2, 0, 0; 0, 0, 2],
    !![2, 0, 0; 0, 2, 0; 0, 2, 1],
    !![0, 1, 2; 2, 2, 0; 1, 0, 2],
    !![2, 2, 0; 0, 0, 1; 2, 0, 2],
    !![0, 1, 2; 2, 0, 0; 2, 0, 1],
    !![2, 0, 0; 1, 1, 0; 2, 1, 2],
    !![0, 2, 2; 0, 1, 2; 2, 2, 1],
    !![1, 1, 1; 2, 1, 0; 1, 1, 0],
    !![0, 2, 1; 0, 2, 0; 1, 0, 0],
    !![1, 2, 1; 2, 2, 2; 2, 0, 0],
    !![1, 0, 0; 2, 1, 2; 1, 1, 0],
    !![2, 1, 1; 2, 1, 0; 2, 0, 2],
    !![1, 2, 1; 1, 1, 2; 0, 1, 1],
    !![1, 1, 0; 0, 2, 1; 1, 1, 2],
    !![1, 2, 0; 2, 2, 2; 0, 2, 2],
    !![0, 1, 2; 2, 1, 1; 2, 0, 0],
    !![1, 0, 0; 0, 2, 1; 0, 2, 0],
    !![2, 2, 2; 1, 2, 0; 1, 0, 1],
    !![0, 1, 2; 2, 2, 1; 0, 2, 2],
    !![2, 0, 2; 1, 2, 0; 2, 0, 0],
    !![0, 1, 0; 0, 1, 2; 2, 0, 2],
    !![1, 1, 2; 2, 1, 2; 1, 2, 0],
    !![1, 1, 1; 2, 1, 2; 2, 0, 1],
    !![1, 1, 2; 0, 1, 2; 1, 2, 2],
    !![0, 1, 0; 1, 2, 0; 0, 2, 2],
    !![1, 2, 0; 1, 2, 2; 1, 0, 0],
    !![2, 2, 1; 2, 1, 2; 0, 1, 0],
    !![2, 2, 0; 2, 0, 1; 1, 2, 0],
    !![0, 0, 2; 1, 1, 1; 1, 0, 0],
    !![1, 2, 2; 0, 2, 1; 0, 0, 2],
    !![2, 2, 1; 1, 2, 1; 1, 1, 1],
    !![2, 2, 0; 2, 1, 0; 0, 1, 1],
    !![2, 1, 0; 1, 1, 1; 1, 0, 0],
    !![1, 1, 2; 0, 2, 1; 2, 2, 0],
    !![0, 1, 0; 0, 0, 2; 2, 1, 0],
    !![2, 1, 0; 1, 0, 1; 0, 2, 1],
    !![0, 0, 1; 2, 0, 1; 0, 2, 0],
    !![1, 2, 1; 2, 2, 1; 0, 1, 0],
    !![1, 2, 0; 0, 2, 1; 1, 1, 0],
    !![2, 1, 0; 0, 2, 0; 1, 2, 1],
    !![0, 1, 2; 0, 0, 1; 1, 1, 2],
    !![0, 1, 0; 1, 1, 0; 2, 2, 2],
    !![1, 0, 2; 1, 1, 0; 2, 2, 1],
    !![2, 1, 0; 2, 1, 2; 0, 2, 0],
    !![2, 1, 2; 1, 1, 2; 1, 2, 2],
    !![1, 2, 0; 1, 1, 0; 0, 1, 2],
    !![1, 2, 1; 1, 0, 2; 2, 2, 1],
    !![2, 2, 0; 0, 2, 0; 2, 1, 1],
    !![0, 0, 1; 0, 2, 0; 1, 1, 2],
    !![1, 1, 1; 1, 0, 2; 1, 2, 2],
    !![1, 0, 2; 0, 0, 2; 2, 1, 0],
    !![2, 2, 2; 2, 0, 2; 2, 0, 1],
    !![0, 1, 2; 2, 1, 0; 1, 2, 1],
    !![0, 2, 0; 1, 0, 0; 1, 0, 1],
    !![0, 0, 2; 0, 2, 1; 2, 1, 0],
    !![1, 2, 2; 0, 1, 0; 0, 0, 1],
    !![1, 2, 1; 1, 2, 0; 0, 1, 2],
    !![1, 1, 0; 1, 0, 0; 2, 0, 2],
    !![2, 1, 0; 0, 0, 2; 2, 0, 1],
    !![2, 0, 1; 2, 1, 2; 1, 2, 0],
    !![1, 1, 1; 2, 2, 0; 1, 0, 2],
    !![0, 1, 1; 1, 0, 0; 2, 2, 1],
    !![1, 1, 2; 2, 0, 0; 0, 0, 1],
    !![2, 1, 1; 1, 2, 1; 2, 0, 1],
    !![0, 2, 0; 2, 1, 1; 2, 2, 0],
    !![2, 1, 2; 2, 1, 0; 0, 1, 1],
    !![2, 2, 1; 2, 0, 0; 1, 0, 2],
    !![0, 0, 1; 1, 2, 0; 2, 2, 1],
    !![2, 2, 2; 0, 1, 2; 0, 0, 2],
    !![1, 1, 0; 2, 2, 2; 0, 1, 0],
    !![0, 2, 1; 1, 2, 0; 0, 2, 2],
    !![2, 0, 0; 0, 2, 2; 2, 0, 1],
    !![1, 0, 0; 1, 1, 2; 2, 1, 0],
    !![2, 1, 1; 0, 1, 0; 0, 0, 2],
    !![1, 1, 0; 1, 1, 2; 0, 1, 1],
    !![2, 0, 0; 2, 1, 0; 2, 0, 2],
    !![2, 2, 1; 2, 2, 0; 0, 2, 1],
    !![1, 2, 0; 1, 0, 0; 1, 1, 1]]

private theorem representativeMatrix_det (i : Fin 144) : (representativeMatrix i).det = 1 := by
  revert i
  decide +kernel

def member (i : Fin 39) : S := ⟨memberMatrix i, memberMatrix_det i⟩
def representative (i : Fin 144) : S := ⟨representativeMatrix i, representativeMatrix_det i⟩
def baseSet : Finset S := Finset.univ.image member
def index (i : Fin 144) : Finset S := baseSet.image (fun h => representative i * h)

private def packedMemberLeft : ℕ := 82562418619384768916929941810070330857620601868354045483466590195160761478225575171691034625400980046857148953436926850582671663201946500721073649108167073023077560121244547669283503012798509928669376989243166588239290113819297522832146579935012863739772457455172429733748082976933117605642155576037659557002563782348014113583573376146001532341654853850195499038063012356496151920923637602173913996546284336919907772963693779362124269039360378405036932950734803717895404303719037501029900413034201649007883234695520437924278936460268411068670497830173903328493018606355790565156110702719575568995639535107511461898502992870364039439871820976758371621652135508673552635912011711700757234635419159980960638554374101279983533143277905858063613223039386679900555522281192660194550152008017408331260356106771691740668852723636589566995206964149007858940218061736991379608841736593726444759534164644388921555817234532839623254937126347076927495209474729863481805177602318811074507763477831235844538386557769354269047058643188734848549900847794596773114971139436016917343539753281402310838607339749988610839745345553097092990937072487374358622050018406729003845089896533595805262624512260682335435590557722443055575037758585131765219674450065676132475712098023252848370153292739358144072317806545773080188936126138309051834989910081468096243538019837387617398294049418511480895535191727069560949790949957439192153960877179597245592050167575602385024123693453860172506248309861939465268316941742574252301373912987679990333550071464466214322748498881044342460568802500768657155098932781094725786136130179953948563798136256303179143939980611392356166738454065870372300029533568053948777595532647745775535538441843778315021595624275048901852038964687338763087022386009302620585855851677953637369654528717276863675077471253064284405280202911554127400872766109619360843709234406601149615606418039966896317177770550020405992248853947579877561666270058786251511293304985989346768411560493626829698995336136835544157229337330914265316374718639844471207432421987806842551571098907687102120772182314991973794131156750788054516961630075089633482233261722823371122016063394188000108785021106210442452122329799070753241030708387326140789479931774555009535454380474368776112412831112278484172077821682119685372173834405054134856693756041440836825940384497450625514633895510198642412805655879069153606970732858482653203833801616221733433861068384739955174068172774078460887929662256471672496188335102092784452148500833440515571628365546650321515898959083394255875119428126688117953446388296055034446205000765018102103790236215789621962388456542676167946789482827078979109650756081150317979493783880566068035874756980777583243452449124225647014803860682609508740375287652

private def memberLeft (i j : Fin 39) : Fin 39 :=
  ⟨((Nat.shiftRight packedMemberLeft (6 * (39 * i.val + j.val))) % 64) % 39,
    Nat.mod_lt _ (by decide +kernel)⟩

private theorem memberLeft_surjective_0 : Function.Surjective (memberLeft 0) := by decide +kernel
private theorem member_mul_0 : ∀ j : Fin 39, member 0 * member j = member (memberLeft 0 j) := by decide +kernel
private theorem memberLeft_surjective_1 : Function.Surjective (memberLeft 1) := by decide +kernel
private theorem member_mul_1 : ∀ j : Fin 39, member 1 * member j = member (memberLeft 1 j) := by decide +kernel
private theorem memberLeft_surjective_2 : Function.Surjective (memberLeft 2) := by decide +kernel
private theorem member_mul_2 : ∀ j : Fin 39, member 2 * member j = member (memberLeft 2 j) := by decide +kernel
private theorem memberLeft_surjective_3 : Function.Surjective (memberLeft 3) := by decide +kernel
private theorem member_mul_3 : ∀ j : Fin 39, member 3 * member j = member (memberLeft 3 j) := by decide +kernel
private theorem memberLeft_surjective_4 : Function.Surjective (memberLeft 4) := by decide +kernel
private theorem member_mul_4 : ∀ j : Fin 39, member 4 * member j = member (memberLeft 4 j) := by decide +kernel
private theorem memberLeft_surjective_5 : Function.Surjective (memberLeft 5) := by decide +kernel
private theorem member_mul_5 : ∀ j : Fin 39, member 5 * member j = member (memberLeft 5 j) := by decide +kernel
private theorem memberLeft_surjective_6 : Function.Surjective (memberLeft 6) := by decide +kernel
private theorem member_mul_6 : ∀ j : Fin 39, member 6 * member j = member (memberLeft 6 j) := by decide +kernel
private theorem memberLeft_surjective_7 : Function.Surjective (memberLeft 7) := by decide +kernel
private theorem member_mul_7 : ∀ j : Fin 39, member 7 * member j = member (memberLeft 7 j) := by decide +kernel
private theorem memberLeft_surjective_8 : Function.Surjective (memberLeft 8) := by decide +kernel
private theorem member_mul_8 : ∀ j : Fin 39, member 8 * member j = member (memberLeft 8 j) := by decide +kernel
private theorem memberLeft_surjective_9 : Function.Surjective (memberLeft 9) := by decide +kernel
private theorem member_mul_9 : ∀ j : Fin 39, member 9 * member j = member (memberLeft 9 j) := by decide +kernel
private theorem memberLeft_surjective_10 : Function.Surjective (memberLeft 10) := by decide +kernel
private theorem member_mul_10 : ∀ j : Fin 39, member 10 * member j = member (memberLeft 10 j) := by decide +kernel
private theorem memberLeft_surjective_11 : Function.Surjective (memberLeft 11) := by decide +kernel
private theorem member_mul_11 : ∀ j : Fin 39, member 11 * member j = member (memberLeft 11 j) := by decide +kernel
private theorem memberLeft_surjective_12 : Function.Surjective (memberLeft 12) := by decide +kernel
private theorem member_mul_12 : ∀ j : Fin 39, member 12 * member j = member (memberLeft 12 j) := by decide +kernel
private theorem memberLeft_surjective_13 : Function.Surjective (memberLeft 13) := by decide +kernel
private theorem member_mul_13 : ∀ j : Fin 39, member 13 * member j = member (memberLeft 13 j) := by decide +kernel
private theorem memberLeft_surjective_14 : Function.Surjective (memberLeft 14) := by decide +kernel
private theorem member_mul_14 : ∀ j : Fin 39, member 14 * member j = member (memberLeft 14 j) := by decide +kernel
private theorem memberLeft_surjective_15 : Function.Surjective (memberLeft 15) := by decide +kernel
private theorem member_mul_15 : ∀ j : Fin 39, member 15 * member j = member (memberLeft 15 j) := by decide +kernel
private theorem memberLeft_surjective_16 : Function.Surjective (memberLeft 16) := by decide +kernel
private theorem member_mul_16 : ∀ j : Fin 39, member 16 * member j = member (memberLeft 16 j) := by decide +kernel
private theorem memberLeft_surjective_17 : Function.Surjective (memberLeft 17) := by decide +kernel
private theorem member_mul_17 : ∀ j : Fin 39, member 17 * member j = member (memberLeft 17 j) := by decide +kernel
private theorem memberLeft_surjective_18 : Function.Surjective (memberLeft 18) := by decide +kernel
private theorem member_mul_18 : ∀ j : Fin 39, member 18 * member j = member (memberLeft 18 j) := by decide +kernel
private theorem memberLeft_surjective_19 : Function.Surjective (memberLeft 19) := by decide +kernel
private theorem member_mul_19 : ∀ j : Fin 39, member 19 * member j = member (memberLeft 19 j) := by decide +kernel
private theorem memberLeft_surjective_20 : Function.Surjective (memberLeft 20) := by decide +kernel
private theorem member_mul_20 : ∀ j : Fin 39, member 20 * member j = member (memberLeft 20 j) := by decide +kernel
private theorem memberLeft_surjective_21 : Function.Surjective (memberLeft 21) := by decide +kernel
private theorem member_mul_21 : ∀ j : Fin 39, member 21 * member j = member (memberLeft 21 j) := by decide +kernel
private theorem memberLeft_surjective_22 : Function.Surjective (memberLeft 22) := by decide +kernel
private theorem member_mul_22 : ∀ j : Fin 39, member 22 * member j = member (memberLeft 22 j) := by decide +kernel
private theorem memberLeft_surjective_23 : Function.Surjective (memberLeft 23) := by decide +kernel
private theorem member_mul_23 : ∀ j : Fin 39, member 23 * member j = member (memberLeft 23 j) := by decide +kernel
private theorem memberLeft_surjective_24 : Function.Surjective (memberLeft 24) := by decide +kernel
private theorem member_mul_24 : ∀ j : Fin 39, member 24 * member j = member (memberLeft 24 j) := by decide +kernel
private theorem memberLeft_surjective_25 : Function.Surjective (memberLeft 25) := by decide +kernel
private theorem member_mul_25 : ∀ j : Fin 39, member 25 * member j = member (memberLeft 25 j) := by decide +kernel
private theorem memberLeft_surjective_26 : Function.Surjective (memberLeft 26) := by decide +kernel
private theorem member_mul_26 : ∀ j : Fin 39, member 26 * member j = member (memberLeft 26 j) := by decide +kernel
private theorem memberLeft_surjective_27 : Function.Surjective (memberLeft 27) := by decide +kernel
private theorem member_mul_27 : ∀ j : Fin 39, member 27 * member j = member (memberLeft 27 j) := by decide +kernel
private theorem memberLeft_surjective_28 : Function.Surjective (memberLeft 28) := by decide +kernel
private theorem member_mul_28 : ∀ j : Fin 39, member 28 * member j = member (memberLeft 28 j) := by decide +kernel
private theorem memberLeft_surjective_29 : Function.Surjective (memberLeft 29) := by decide +kernel
private theorem member_mul_29 : ∀ j : Fin 39, member 29 * member j = member (memberLeft 29 j) := by decide +kernel
private theorem memberLeft_surjective_30 : Function.Surjective (memberLeft 30) := by decide +kernel
private theorem member_mul_30 : ∀ j : Fin 39, member 30 * member j = member (memberLeft 30 j) := by decide +kernel
private theorem memberLeft_surjective_31 : Function.Surjective (memberLeft 31) := by decide +kernel
private theorem member_mul_31 : ∀ j : Fin 39, member 31 * member j = member (memberLeft 31 j) := by decide +kernel
private theorem memberLeft_surjective_32 : Function.Surjective (memberLeft 32) := by decide +kernel
private theorem member_mul_32 : ∀ j : Fin 39, member 32 * member j = member (memberLeft 32 j) := by decide +kernel
private theorem memberLeft_surjective_33 : Function.Surjective (memberLeft 33) := by decide +kernel
private theorem member_mul_33 : ∀ j : Fin 39, member 33 * member j = member (memberLeft 33 j) := by decide +kernel
private theorem memberLeft_surjective_34 : Function.Surjective (memberLeft 34) := by decide +kernel
private theorem member_mul_34 : ∀ j : Fin 39, member 34 * member j = member (memberLeft 34 j) := by decide +kernel
private theorem memberLeft_surjective_35 : Function.Surjective (memberLeft 35) := by decide +kernel
private theorem member_mul_35 : ∀ j : Fin 39, member 35 * member j = member (memberLeft 35 j) := by decide +kernel
private theorem memberLeft_surjective_36 : Function.Surjective (memberLeft 36) := by decide +kernel
private theorem member_mul_36 : ∀ j : Fin 39, member 36 * member j = member (memberLeft 36 j) := by decide +kernel
private theorem memberLeft_surjective_37 : Function.Surjective (memberLeft 37) := by decide +kernel
private theorem member_mul_37 : ∀ j : Fin 39, member 37 * member j = member (memberLeft 37 j) := by decide +kernel
private theorem memberLeft_surjective_38 : Function.Surjective (memberLeft 38) := by decide +kernel
private theorem member_mul_38 : ∀ j : Fin 39, member 38 * member j = member (memberLeft 38 j) := by decide +kernel
private theorem memberLeft_surjective (i : Fin 39) : Function.Surjective (memberLeft i) := by
  fin_cases i
  · exact memberLeft_surjective_0
  · exact memberLeft_surjective_1
  · exact memberLeft_surjective_2
  · exact memberLeft_surjective_3
  · exact memberLeft_surjective_4
  · exact memberLeft_surjective_5
  · exact memberLeft_surjective_6
  · exact memberLeft_surjective_7
  · exact memberLeft_surjective_8
  · exact memberLeft_surjective_9
  · exact memberLeft_surjective_10
  · exact memberLeft_surjective_11
  · exact memberLeft_surjective_12
  · exact memberLeft_surjective_13
  · exact memberLeft_surjective_14
  · exact memberLeft_surjective_15
  · exact memberLeft_surjective_16
  · exact memberLeft_surjective_17
  · exact memberLeft_surjective_18
  · exact memberLeft_surjective_19
  · exact memberLeft_surjective_20
  · exact memberLeft_surjective_21
  · exact memberLeft_surjective_22
  · exact memberLeft_surjective_23
  · exact memberLeft_surjective_24
  · exact memberLeft_surjective_25
  · exact memberLeft_surjective_26
  · exact memberLeft_surjective_27
  · exact memberLeft_surjective_28
  · exact memberLeft_surjective_29
  · exact memberLeft_surjective_30
  · exact memberLeft_surjective_31
  · exact memberLeft_surjective_32
  · exact memberLeft_surjective_33
  · exact memberLeft_surjective_34
  · exact memberLeft_surjective_35
  · exact memberLeft_surjective_36
  · exact memberLeft_surjective_37
  · exact memberLeft_surjective_38

private theorem member_mul (i j : Fin 39) : member i * member j = member (memberLeft i j) := by
  fin_cases i
  · exact member_mul_0 j
  · exact member_mul_1 j
  · exact member_mul_2 j
  · exact member_mul_3 j
  · exact member_mul_4 j
  · exact member_mul_5 j
  · exact member_mul_6 j
  · exact member_mul_7 j
  · exact member_mul_8 j
  · exact member_mul_9 j
  · exact member_mul_10 j
  · exact member_mul_11 j
  · exact member_mul_12 j
  · exact member_mul_13 j
  · exact member_mul_14 j
  · exact member_mul_15 j
  · exact member_mul_16 j
  · exact member_mul_17 j
  · exact member_mul_18 j
  · exact member_mul_19 j
  · exact member_mul_20 j
  · exact member_mul_21 j
  · exact member_mul_22 j
  · exact member_mul_23 j
  · exact member_mul_24 j
  · exact member_mul_25 j
  · exact member_mul_26 j
  · exact member_mul_27 j
  · exact member_mul_28 j
  · exact member_mul_29 j
  · exact member_mul_30 j
  · exact member_mul_31 j
  · exact member_mul_32 j
  · exact member_mul_33 j
  · exact member_mul_34 j
  · exact member_mul_35 j
  · exact member_mul_36 j
  · exact member_mul_37 j
  · exact member_mul_38 j

theorem member_image (i : Fin 39) : baseSet.image (fun h => member i * h) = baseSet := by
  have hfun : (fun h => member i * h) ∘ member = member ∘ memberLeft i := by
    funext j
    exact member_mul i j
  rw [baseSet, Finset.image_image, hfun, ← Finset.image_image,
    Finset.image_univ_of_surjective (memberLeft_surjective i)]

def matrixCode (g : S) : ℕ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (g.val i j).val * 3 ^ (8 - (3 * i.val + j.val))
def signature (s : Finset S) : WithTop ℕ := s.inf (fun g => (matrixCode g : WithTop ℕ))
def minimumCode : Fin 144 → ℕ :=
  ![1553, 883, 833, 933, 862, 1707, 1667, 1575, 900, 1965, 1644, 1608, 1697, 1604, 1645, 1717, 1223, 890, 901, 859, 1666, 1551, 1671, 957, 906, 930, 1696, 1726, 975, 1239, 860, 828, 1241, 986, 907, 959, 1692, 1555, 1967, 962, 1673, 993, 1552, 935, 886, 1579, 885, 1966, 1580, 1240, 830, 1949, 954, 995, 1583, 994, 889, 1700, 1669, 985, 1607, 960, 1556, 1576, 955, 1548, 1577, 902, 956, 1640, 855, 884, 1947, 1646, 1609, 1643, 1956, 1641, 1610, 976, 1606, 932, 1718, 832, 835, 977, 1639, 904, 1605, 887, 1699, 1603, 1642, 1582, 1549, 834, 1550, 1578, 929, 927, 1670, 961, 1232, 1672, 1694, 1231, 908, 1638, 1957, 856, 882, 1958, 1698, 1602, 905, 1665, 1695, 903, 1230, 928, 1668, 984, 1727, 829, 836, 1222, 1554, 931, 857, 1693, 958, 1221, 1581, 934, 861, 888, 1709, 831, 1948, 1725, 858, 863, 1708, 1716]

private def rawSignature (i : Fin 144) : WithTop ℕ :=
  Finset.univ.inf (fun j : Fin 39 => (matrixCode (representative i * member j) : WithTop ℕ))

private theorem signature_index_formula (i : Fin 144) : signature (index i) = rawSignature i := by
  simp only [signature, index, baseSet, Finset.inf_image, Function.comp_def, rawSignature]

private theorem signature_index_0 : signature (index 0) = (minimumCode 0 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_1 : signature (index 1) = (minimumCode 1 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_2 : signature (index 2) = (minimumCode 2 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_3 : signature (index 3) = (minimumCode 3 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_4 : signature (index 4) = (minimumCode 4 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_5 : signature (index 5) = (minimumCode 5 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_6 : signature (index 6) = (minimumCode 6 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_7 : signature (index 7) = (minimumCode 7 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_8 : signature (index 8) = (minimumCode 8 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_9 : signature (index 9) = (minimumCode 9 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_10 : signature (index 10) = (minimumCode 10 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_11 : signature (index 11) = (minimumCode 11 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_12 : signature (index 12) = (minimumCode 12 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_13 : signature (index 13) = (minimumCode 13 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_14 : signature (index 14) = (minimumCode 14 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_15 : signature (index 15) = (minimumCode 15 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_16 : signature (index 16) = (minimumCode 16 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_17 : signature (index 17) = (minimumCode 17 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_18 : signature (index 18) = (minimumCode 18 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_19 : signature (index 19) = (minimumCode 19 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_20 : signature (index 20) = (minimumCode 20 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_21 : signature (index 21) = (minimumCode 21 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_22 : signature (index 22) = (minimumCode 22 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_23 : signature (index 23) = (minimumCode 23 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_24 : signature (index 24) = (minimumCode 24 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_25 : signature (index 25) = (minimumCode 25 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_26 : signature (index 26) = (minimumCode 26 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_27 : signature (index 27) = (minimumCode 27 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_28 : signature (index 28) = (minimumCode 28 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_29 : signature (index 29) = (minimumCode 29 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_30 : signature (index 30) = (minimumCode 30 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_31 : signature (index 31) = (minimumCode 31 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_32 : signature (index 32) = (minimumCode 32 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_33 : signature (index 33) = (minimumCode 33 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_34 : signature (index 34) = (minimumCode 34 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_35 : signature (index 35) = (minimumCode 35 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_36 : signature (index 36) = (minimumCode 36 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_37 : signature (index 37) = (minimumCode 37 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_38 : signature (index 38) = (minimumCode 38 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_39 : signature (index 39) = (minimumCode 39 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_40 : signature (index 40) = (minimumCode 40 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_41 : signature (index 41) = (minimumCode 41 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_42 : signature (index 42) = (minimumCode 42 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_43 : signature (index 43) = (minimumCode 43 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_44 : signature (index 44) = (minimumCode 44 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_45 : signature (index 45) = (minimumCode 45 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_46 : signature (index 46) = (minimumCode 46 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_47 : signature (index 47) = (minimumCode 47 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_48 : signature (index 48) = (minimumCode 48 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_49 : signature (index 49) = (minimumCode 49 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_50 : signature (index 50) = (minimumCode 50 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_51 : signature (index 51) = (minimumCode 51 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_52 : signature (index 52) = (minimumCode 52 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_53 : signature (index 53) = (minimumCode 53 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_54 : signature (index 54) = (minimumCode 54 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_55 : signature (index 55) = (minimumCode 55 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_56 : signature (index 56) = (minimumCode 56 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_57 : signature (index 57) = (minimumCode 57 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_58 : signature (index 58) = (minimumCode 58 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_59 : signature (index 59) = (minimumCode 59 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_60 : signature (index 60) = (minimumCode 60 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_61 : signature (index 61) = (minimumCode 61 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_62 : signature (index 62) = (minimumCode 62 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_63 : signature (index 63) = (minimumCode 63 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_64 : signature (index 64) = (minimumCode 64 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_65 : signature (index 65) = (minimumCode 65 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_66 : signature (index 66) = (minimumCode 66 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_67 : signature (index 67) = (minimumCode 67 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_68 : signature (index 68) = (minimumCode 68 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_69 : signature (index 69) = (minimumCode 69 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_70 : signature (index 70) = (minimumCode 70 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_71 : signature (index 71) = (minimumCode 71 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_72 : signature (index 72) = (minimumCode 72 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_73 : signature (index 73) = (minimumCode 73 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_74 : signature (index 74) = (minimumCode 74 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_75 : signature (index 75) = (minimumCode 75 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_76 : signature (index 76) = (minimumCode 76 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_77 : signature (index 77) = (minimumCode 77 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_78 : signature (index 78) = (minimumCode 78 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_79 : signature (index 79) = (minimumCode 79 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_80 : signature (index 80) = (minimumCode 80 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_81 : signature (index 81) = (minimumCode 81 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_82 : signature (index 82) = (minimumCode 82 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_83 : signature (index 83) = (minimumCode 83 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_84 : signature (index 84) = (minimumCode 84 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_85 : signature (index 85) = (minimumCode 85 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_86 : signature (index 86) = (minimumCode 86 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_87 : signature (index 87) = (minimumCode 87 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_88 : signature (index 88) = (minimumCode 88 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_89 : signature (index 89) = (minimumCode 89 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_90 : signature (index 90) = (minimumCode 90 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_91 : signature (index 91) = (minimumCode 91 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_92 : signature (index 92) = (minimumCode 92 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_93 : signature (index 93) = (minimumCode 93 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_94 : signature (index 94) = (minimumCode 94 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_95 : signature (index 95) = (minimumCode 95 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_96 : signature (index 96) = (minimumCode 96 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_97 : signature (index 97) = (minimumCode 97 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_98 : signature (index 98) = (minimumCode 98 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_99 : signature (index 99) = (minimumCode 99 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_100 : signature (index 100) = (minimumCode 100 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_101 : signature (index 101) = (minimumCode 101 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_102 : signature (index 102) = (minimumCode 102 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_103 : signature (index 103) = (minimumCode 103 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_104 : signature (index 104) = (minimumCode 104 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_105 : signature (index 105) = (minimumCode 105 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_106 : signature (index 106) = (minimumCode 106 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_107 : signature (index 107) = (minimumCode 107 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_108 : signature (index 108) = (minimumCode 108 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_109 : signature (index 109) = (minimumCode 109 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_110 : signature (index 110) = (minimumCode 110 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_111 : signature (index 111) = (minimumCode 111 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_112 : signature (index 112) = (minimumCode 112 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_113 : signature (index 113) = (minimumCode 113 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_114 : signature (index 114) = (minimumCode 114 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_115 : signature (index 115) = (minimumCode 115 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_116 : signature (index 116) = (minimumCode 116 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_117 : signature (index 117) = (minimumCode 117 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_118 : signature (index 118) = (minimumCode 118 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_119 : signature (index 119) = (minimumCode 119 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_120 : signature (index 120) = (minimumCode 120 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_121 : signature (index 121) = (minimumCode 121 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_122 : signature (index 122) = (minimumCode 122 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_123 : signature (index 123) = (minimumCode 123 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_124 : signature (index 124) = (minimumCode 124 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_125 : signature (index 125) = (minimumCode 125 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_126 : signature (index 126) = (minimumCode 126 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_127 : signature (index 127) = (minimumCode 127 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_128 : signature (index 128) = (minimumCode 128 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_129 : signature (index 129) = (minimumCode 129 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_130 : signature (index 130) = (minimumCode 130 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_131 : signature (index 131) = (minimumCode 131 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_132 : signature (index 132) = (minimumCode 132 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_133 : signature (index 133) = (minimumCode 133 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_134 : signature (index 134) = (minimumCode 134 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_135 : signature (index 135) = (minimumCode 135 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_136 : signature (index 136) = (minimumCode 136 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_137 : signature (index 137) = (minimumCode 137 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_138 : signature (index 138) = (minimumCode 138 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_139 : signature (index 139) = (minimumCode 139 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_140 : signature (index 140) = (minimumCode 140 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_141 : signature (index 141) = (minimumCode 141 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_142 : signature (index 142) = (minimumCode 142 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
private theorem signature_index_143 : signature (index 143) = (minimumCode 143 : WithTop ℕ) := by
  rw [signature_index_formula]
  decide +kernel
theorem signature_index (i : Fin 144) : signature (index i) = (minimumCode i : WithTop ℕ) := by
  fin_cases i
  · exact signature_index_0
  · exact signature_index_1
  · exact signature_index_2
  · exact signature_index_3
  · exact signature_index_4
  · exact signature_index_5
  · exact signature_index_6
  · exact signature_index_7
  · exact signature_index_8
  · exact signature_index_9
  · exact signature_index_10
  · exact signature_index_11
  · exact signature_index_12
  · exact signature_index_13
  · exact signature_index_14
  · exact signature_index_15
  · exact signature_index_16
  · exact signature_index_17
  · exact signature_index_18
  · exact signature_index_19
  · exact signature_index_20
  · exact signature_index_21
  · exact signature_index_22
  · exact signature_index_23
  · exact signature_index_24
  · exact signature_index_25
  · exact signature_index_26
  · exact signature_index_27
  · exact signature_index_28
  · exact signature_index_29
  · exact signature_index_30
  · exact signature_index_31
  · exact signature_index_32
  · exact signature_index_33
  · exact signature_index_34
  · exact signature_index_35
  · exact signature_index_36
  · exact signature_index_37
  · exact signature_index_38
  · exact signature_index_39
  · exact signature_index_40
  · exact signature_index_41
  · exact signature_index_42
  · exact signature_index_43
  · exact signature_index_44
  · exact signature_index_45
  · exact signature_index_46
  · exact signature_index_47
  · exact signature_index_48
  · exact signature_index_49
  · exact signature_index_50
  · exact signature_index_51
  · exact signature_index_52
  · exact signature_index_53
  · exact signature_index_54
  · exact signature_index_55
  · exact signature_index_56
  · exact signature_index_57
  · exact signature_index_58
  · exact signature_index_59
  · exact signature_index_60
  · exact signature_index_61
  · exact signature_index_62
  · exact signature_index_63
  · exact signature_index_64
  · exact signature_index_65
  · exact signature_index_66
  · exact signature_index_67
  · exact signature_index_68
  · exact signature_index_69
  · exact signature_index_70
  · exact signature_index_71
  · exact signature_index_72
  · exact signature_index_73
  · exact signature_index_74
  · exact signature_index_75
  · exact signature_index_76
  · exact signature_index_77
  · exact signature_index_78
  · exact signature_index_79
  · exact signature_index_80
  · exact signature_index_81
  · exact signature_index_82
  · exact signature_index_83
  · exact signature_index_84
  · exact signature_index_85
  · exact signature_index_86
  · exact signature_index_87
  · exact signature_index_88
  · exact signature_index_89
  · exact signature_index_90
  · exact signature_index_91
  · exact signature_index_92
  · exact signature_index_93
  · exact signature_index_94
  · exact signature_index_95
  · exact signature_index_96
  · exact signature_index_97
  · exact signature_index_98
  · exact signature_index_99
  · exact signature_index_100
  · exact signature_index_101
  · exact signature_index_102
  · exact signature_index_103
  · exact signature_index_104
  · exact signature_index_105
  · exact signature_index_106
  · exact signature_index_107
  · exact signature_index_108
  · exact signature_index_109
  · exact signature_index_110
  · exact signature_index_111
  · exact signature_index_112
  · exact signature_index_113
  · exact signature_index_114
  · exact signature_index_115
  · exact signature_index_116
  · exact signature_index_117
  · exact signature_index_118
  · exact signature_index_119
  · exact signature_index_120
  · exact signature_index_121
  · exact signature_index_122
  · exact signature_index_123
  · exact signature_index_124
  · exact signature_index_125
  · exact signature_index_126
  · exact signature_index_127
  · exact signature_index_128
  · exact signature_index_129
  · exact signature_index_130
  · exact signature_index_131
  · exact signature_index_132
  · exact signature_index_133
  · exact signature_index_134
  · exact signature_index_135
  · exact signature_index_136
  · exact signature_index_137
  · exact signature_index_138
  · exact signature_index_139
  · exact signature_index_140
  · exact signature_index_141
  · exact signature_index_142
  · exact signature_index_143

theorem index_injective : Function.Injective index := by
  have hi : Function.Injective minimumCode := by decide +kernel
  intro i j h
  apply hi
  have hs := congrArg signature h
  rw [signature_index, signature_index] at hs
  simpa using hs

def permA : Equiv.Perm (Fin 144) where
  toFun i := ![1, 0, 3, 2, 5, 4, 8, 9, 6, 7, 13, 14, 16, 10, 11, 19, 12, 21, 22, 15, 24, 17, 18, 28, 20, 31, 32, 30, 23, 36, 27, 25, 26, 39, 40, 41, 29, 44, 45, 33, 34, 35, 46, 50, 37, 38, 42, 54, 51, 57, 43, 48, 59, 61, 47, 64, 65, 49, 67, 52, 69, 53, 71, 72, 55, 56, 76, 58, 79, 60, 82, 62, 63, 80, 86, 88, 66, 91, 92, 68, 73, 95, 70, 98, 99, 101, 74, 103, 75, 94, 105, 77, 78, 108, 89, 81, 110, 111, 83, 84, 114, 85, 116, 87, 118, 90, 120, 113, 93, 122, 96, 97, 125, 107, 100, 117, 102, 115, 104, 123, 106, 130, 109, 119, 133, 112, 135, 137, 136, 131, 121, 129, 138, 124, 139, 126, 128, 127, 132, 134, 142, 143, 140, 141] i
  invFun i := ![1, 0, 3, 2, 5, 4, 8, 9, 6, 7, 13, 14, 16, 10, 11, 19, 12, 21, 22, 15, 24, 17, 18, 28, 20, 31, 32, 30, 23, 36, 27, 25, 26, 39, 40, 41, 29, 44, 45, 33, 34, 35, 46, 50, 37, 38, 42, 54, 51, 57, 43, 48, 59, 61, 47, 64, 65, 49, 67, 52, 69, 53, 71, 72, 55, 56, 76, 58, 79, 60, 82, 62, 63, 80, 86, 88, 66, 91, 92, 68, 73, 95, 70, 98, 99, 101, 74, 103, 75, 94, 105, 77, 78, 108, 89, 81, 110, 111, 83, 84, 114, 85, 116, 87, 118, 90, 120, 113, 93, 122, 96, 97, 125, 107, 100, 117, 102, 115, 104, 123, 106, 130, 109, 119, 133, 112, 135, 137, 136, 131, 121, 129, 138, 124, 139, 126, 128, 127, 132, 134, 142, 143, 140, 141] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permB : Equiv.Perm (Fin 144) where
  toFun i := ![1, 2, 0, 4, 6, 7, 3, 10, 11, 12, 5, 15, 17, 14, 18, 8, 20, 9, 13, 23, 25, 26, 27, 29, 30, 16, 33, 34, 35, 19, 37, 31, 38, 21, 22, 42, 43, 24, 46, 47, 48, 49, 28, 51, 52, 53, 32, 55, 56, 58, 50, 36, 60, 62, 63, 39, 40, 66, 41, 68, 44, 70, 45, 73, 74, 75, 77, 78, 80, 81, 83, 84, 85, 54, 87, 89, 90, 57, 93, 94, 59, 96, 97, 61, 100, 102, 98, 64, 104, 65, 106, 107, 79, 67, 92, 109, 69, 112, 113, 91, 71, 115, 72, 117, 119, 103, 76, 99, 121, 123, 124, 110, 82, 86, 126, 127, 116, 105, 128, 88, 129, 131, 132, 95, 111, 134, 136, 101, 137, 133, 130, 108, 139, 120, 140, 141, 114, 118, 135, 122, 125, 138, 142, 143] i
  invFun i := ![2, 0, 1, 6, 3, 10, 4, 5, 15, 17, 7, 8, 9, 18, 13, 11, 25, 12, 14, 29, 16, 33, 34, 19, 37, 20, 21, 22, 42, 23, 24, 31, 46, 26, 27, 28, 51, 30, 32, 55, 56, 58, 35, 36, 60, 62, 38, 39, 40, 41, 50, 43, 44, 45, 73, 47, 48, 77, 49, 80, 52, 83, 53, 54, 87, 89, 57, 93, 59, 96, 61, 100, 102, 63, 64, 65, 106, 66, 67, 92, 68, 69, 112, 70, 71, 72, 113, 74, 119, 75, 76, 99, 94, 78, 79, 123, 81, 82, 86, 107, 84, 127, 85, 105, 88, 117, 90, 91, 131, 95, 111, 124, 97, 98, 136, 101, 116, 103, 137, 104, 133, 108, 139, 109, 110, 140, 114, 115, 118, 120, 130, 121, 122, 129, 125, 138, 126, 128, 141, 132, 134, 135, 142, 143] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def edgeA : Fin 144 → Fin 39 :=
  ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 5, 12, 12, 34, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 12, 23, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 21, 12, 12, 12, 12, 37, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 27, 12, 24, 12, 5, 12, 12, 12, 34, 12, 12, 12, 12, 23, 4, 12, 18, 12, 12, 1, 12, 6, 12, 12, 28, 12, 12, 12, 12]

theorem edge_a (i : Fin 144) :
    a * representative i = representative (permA i) * member (edgeA i) := by
  revert i
  decide +kernel

def edgeB : Fin 144 → Fin 39 :=
  ![15, 12, 33, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 22, 12, 12, 12, 12, 29, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 26, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 23, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 31, 12, 12, 12, 12, 12, 7, 12, 2, 12, 12, 12, 12, 31, 12, 12, 12, 12, 12, 29, 12, 3, 12, 12, 12, 8, 12, 3, 12, 12, 24, 22, 12, 12, 12, 12, 12, 12, 26, 12, 12, 12, 21, 23, 18, 12, 12, 6, 12, 12, 12, 37, 28, 12, 12, 1, 21, 19]

theorem edge_b (i : Fin 144) :
    b * representative i = representative (permB i) * member (edgeB i) := by
  revert i
  decide +kernel

private theorem index_image (g : S) (i j : Fin 144) (h : Fin 39)
    (he : g * representative i = representative j * member h) :
    (index i).image (fun x => g * x) = index j := by
  calc
    _ = baseSet.image (fun x => (g * representative i) * x) := by
      simp only [index, Finset.image_image, Function.comp_def, mul_assoc]
    _ = baseSet.image (fun x => (representative j * member h) * x) := by rw [he]
    _ = (baseSet.image (fun x => member h * x)).image (fun x => representative j * x) := by
      simp only [Finset.image_image, Function.comp_def, mul_assoc]
    _ = index j := by rw [member_image]; rfl

def ambient : Q →* Equiv.Perm (Finset S) :=
  (MulAction.toPermHom S (Finset S)).comp
    PSLThreeThreeSemidihedralData.projectiveEquiv.symm.toMonoidHom

theorem a_index (i : Fin 144) :
    ambient (PSL33GoodSets.q a) (index i) = index (permA i) := by
  have h : PSLThreeThreeSemidihedralData.projectiveEquiv.symm (PSL33GoodSets.q a) = a :=
    PSLThreeThreeSemidihedralData.projectiveEquiv.symm_apply_apply a
  change (index i).image (fun x =>
    PSLThreeThreeSemidihedralData.projectiveEquiv.symm (PSL33GoodSets.q a) * x) = _
  rw [h]
  exact index_image a i (permA i) (edgeA i) (edge_a i)

theorem b_index (i : Fin 144) :
    ambient (PSL33GoodSets.q b) (index i) = index (permB i) := by
  have h : PSLThreeThreeSemidihedralData.projectiveEquiv.symm (PSL33GoodSets.q b) = b :=
    PSLThreeThreeSemidihedralData.projectiveEquiv.symm_apply_apply b
  change (index i).image (fun x =>
    PSLThreeThreeSemidihedralData.projectiveEquiv.symm (PSL33GoodSets.q b) * x) = _
  rw [h]
  exact index_image b i (permB i) (edgeB i) (edge_b i)

theorem generator_certificate (g : Q)
    (hg : g ∈ ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q)) :
    ∃ p : Equiv.Perm (Fin 144), ∀ i, ambient g (index i) = index (p i) := by
  rcases (show g = PSL33GoodSets.q a ∨ g = PSL33GoodSets.q b by simpa using hg) with rfl | rfl
  · exact ⟨permA, a_index⟩
  · exact ⟨permB, b_index⟩

def permutation : Q →* Equiv.Perm (Fin 144) :=
  SubactionCertificate.hom ambient index index_injective
    {PSL33GoodSets.q a, PSL33GoodSets.q b} generating_projective generator_certificate

theorem permutation_a : permutation (PSL33GoodSets.q a) = permA :=
  SubactionCertificate.hom_eq_of_spec ambient index index_injective _
    generating_projective generator_certificate _ permA a_index

theorem permutation_b : permutation (PSL33GoodSets.q b) = permB :=
  SubactionCertificate.hom_eq_of_spec ambient index index_injective _
    generating_projective generator_certificate _ permB b_index

def representation (k : Type*) [CommRing k] : Representation k Q (Fin 144 → k) where
  toFun g := LinearMap.pi fun i => LinearMap.proj ((permutation g).symm i)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change v ((permutation 1).symm i) = v i; rw [map_one]; rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    change v ((permutation (g * h)).symm i) =
      v ((permutation h).symm ((permutation g).symm i))
    rw [map_mul]
    rfl

@[simp] theorem representation_a (k : Type*) [CommRing k] (v : Fin 144 → k) (i : Fin 144) :
    representation k (PSL33GoodSets.q a) v i = v (permA.symm i) := by
  change v ((permutation (PSL33GoodSets.q a)).symm i) = _
  rw [permutation_a]

@[simp] theorem representation_b (k : Type*) [CommRing k] (v : Fin 144 → k) (i : Fin 144) :
    representation k (PSL33GoodSets.q b) v i = v (permB.symm i) := by
  change v ((permutation (PSL33GoodSets.q b)).symm i) = _
  rw [permutation_b]

end Kourovka2135.PSL33SingerCosetData
