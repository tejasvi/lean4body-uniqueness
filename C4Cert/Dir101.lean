module

public import C4Check

public section

/-! Cells `3373 ≤ n < 3425` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir101

theorem k3373_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3373) 1).1
      15926003917417439447608513164654819506251381415635107369068530294203192429147437954939964).isSome = true := by
  decide +kernel

theorem k3373_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3373) 1).2
      3981784106760289332434881772537971191260147917753563476459134938513189787533666928081980).isSome = true := by
  decide +kernel

theorem k3374_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3374) 1).1
      842852809325445712618076790310336128749557865691638976852348236348).isSome = true := by
  decide +kernel

theorem k3374_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3374) 1).2
      3371637294566600872810052391383278275596622960609879384277860676156).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 3375 3376 [
    5416655716638301742450148987099681739927136623834018102613070970610170514777640281950980566546715076113000379641002911612034481] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3376 3393 [
    205700676500137959461554781795534891653243481828178415093691345, 147553304620210603748, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    13393483361370604005498650167687800326616805941013156382692962823] = true := by
  decide +kernel

theorem k3393_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3393) 3).1
      18622719149012963320216393268792049738556207420314507805792142697221062655978647613707502389998366592333002).isSome = true := by
  decide +kernel

theorem k3393_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3393) 3).2
      5481635412226707331714151229251460232093091758585861482148910859517564980121128577263838976094916953242208777537938641135697074).isSome = true := by
  decide +kernel

theorem k3394_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3394) 3).1
      87618333464095596741272343152948518613849220606334852224290086792633390389744015932607633438098237841847958263982763086460702514).isSome = true := by
  decide +kernel

theorem k3394_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3394) 3).2
      87474606565607869660610049330283803399702365749866202446757984184051969769582341958839293585168756759863740723685071078055956274).isSome = true := by
  decide +kernel

theorem k3395_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3395) 2).1 1).1
      3914609609386609856887109693163418003331412896020473577190004997412199903030115031756).isSome = true := by
  decide +kernel

theorem k3395_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3395) 2).1 1).2
      212201409192552130835923411864455250048706069008983551252159253196).isSome = true := by
  decide +kernel

theorem k3395_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3395) 2).2 3).1
      3316983244405260174467171434353464176613966936341017588036654028).isSome = true := by
  decide +kernel

theorem k3395_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3395) 2).2 3).2
      978088282285049812438047253115082898754518226396241258323537676681868578447852821196).isSome = true := by
  decide +kernel

theorem k3396_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3396) 2).1 1).1
      13552562958934152651938553156597866979304702649192428343718673792060).isSome = true := by
  decide +kernel

theorem k3396_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3396) 2).1 1).2
      3388201961876406172296097351004202399404229058039855347738554082252).isSome = true := by
  decide +kernel

theorem k3396_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3396) 2).2 1).1
      13553153496113478041978512330659471397019124159259027772273530649660).isSome = true := by
  decide +kernel

theorem k3396_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3396) 2).2 1).2
      211774325684992754293234674347323636608484874190612482359935091660).isSome = true := by
  decide +kernel

theorem k3397_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3397) 2).1 1).1
      11736679610194756707221672924856798836127273991228).isSome = true := by
  decide +kernel

theorem k3397_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3397) 2).1 1).2
      13532042247121684417139029957879361555489019995341425234963657276476).isSome = true := by
  decide +kernel

theorem k3397_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3397) 2).2
      89095620418165808730681674266161294222183256653131054924085835398158397174556088472428750041333567864525395826497444220883964214332).isSome = true := by
  decide +kernel

theorem k3398_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3398) 2).1
      89011671763830757862343483750896975288248834160188947553343364280958177153103749009512607488560176852155200488004183208725993700412).isSome = true := by
  decide +kernel

theorem k3398_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3398) 2).2
      301448168674320029269147753550419989161686492968358842140226322125264196472125401348839554016357718460163898428).isSome = true := by
  decide +kernel

theorem k3399_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3399) 2).1
      22223715483666790042524578903280306905388771228049972406998185990731498892574252925517579984812964022069446979376762246695029031740).isSome = true := by
  decide +kernel

theorem k3399_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3399) 2).2
      16335915140971338387174509875517964103654765419862797867585291280993238605420723325623267569).isSome = true := by
  decide +kernel

theorem k3400_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3400) 1).1
      15934592674287823509721682390428469184835561028357800834004691910813468752763465397683004).isSome = true := by
  decide +kernel

theorem k3400_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3400) 1).2
      15943325606203101466823499648118739519669915576623005647465084261874659047686572486935356).isSome = true := by
  decide +kernel

theorem k3401_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3401) 1).1
      210790438243147868061283420944910535049324355531454236644464849468).isSome = true := by
  decide +kernel

theorem k3401_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3401) 1).2
      995502357689002005342405450733621395639877114924063767194346728156044883083326501143356).isSome = true := by
  decide +kernel

theorem k3402_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3402) 1).1
      52678782987927064444449663698984003915016281334667845383246705212).isSome = true := by
  decide +kernel

theorem k3402_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3402) 1).2
      52683125320172140748450731312201913988044705023195494287730405948).isSome = true := by
  decide +kernel

theorem c14 : allCells dirCell 3403 3404 [
    21159541029622443204207882847844790941354816095673332826358960371194972198889592013460032596872662883931140776005161722076593] = true := by
  decide +kernel

theorem c15 : allCells dirCell 3404 3421 [
    51425272544547562702865733073372651694428025239436115827072401, 147552305439044934372, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9617000082521333380387] = true := by
  decide +kernel

theorem k3421_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3421) 3).1
      15407084541924507310832984271838968537159881188305324811760709711067061400826311026).isSome = true := by
  decide +kernel

theorem k3421_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3421) 3).2
      62966582999850366707741942357973698192979541465681209536702744092644334337005809917106).isSome = true := by
  decide +kernel

theorem k3422_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3422) 2).1
      4630597735204600430689349359355239963417523304753455566333940773373208553891940245153907284789772180166451).isSome = true := by
  decide +kernel

theorem k3422_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3422) 2).2
      4630196406736516120914887116718556124309064748405051273803049776758169581963985536624900783639297428707123).isSome = true := by
  decide +kernel

theorem k3423_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3423) 2).1
      1182372907715311372672497369074932680217392951337867697343345495006197323387746310874071998850822449717959475).isSome = true := by
  decide +kernel

theorem k3423_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3423) 2).2
      16028974283777234805569171951557598773814407290718237529918527479158641063067594012347185).isSome = true := by
  decide +kernel

theorem k3424_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3424) 2).1
      22302850731263504837894850873389499005207396623928297059382410327331863090171006645978472465305999075545922922007222211933379902524).isSome = true := by
  decide +kernel

theorem k3424_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3424) 2).2
      255907536089947139478486199202001784780748298316120197546774403891836706387988093620129587).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3373 3425 :=
  (Cover.one (box := dirCellBox) (n := 3373)
      (.split 1 (.leaf _ k3373_0) (.leaf _ k3373_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3374)
      (.split 1 (.leaf _ k3374_0) (.leaf _ k3374_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 3393)
      (.split 3 (.leaf _ k3393_0) (.leaf _ k3393_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3394)
      (.split 3 (.leaf _ k3394_0) (.leaf _ k3394_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3395)
      (.split 2 (.split 1 (.leaf _ k3395_0) (.leaf _ k3395_1)) (.split 3 (.leaf _ k3395_2) (.leaf _ k3395_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3396)
      (.split 2 (.split 1 (.leaf _ k3396_0) (.leaf _ k3396_1)) (.split 1 (.leaf _ k3396_2) (.leaf _ k3396_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3397)
      (.split 2 (.split 1 (.leaf _ k3397_0) (.leaf _ k3397_1)) (.leaf _ k3397_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3398)
      (.split 2 (.leaf _ k3398_0) (.leaf _ k3398_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3399)
      (.split 2 (.leaf _ k3399_0) (.leaf _ k3399_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3400)
      (.split 1 (.leaf _ k3400_0) (.leaf _ k3400_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3401)
      (.split 1 (.leaf _ k3401_0) (.leaf _ k3401_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3402)
      (.split 1 (.leaf _ k3402_0) (.leaf _ k3402_1))).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.one (box := dirCellBox) (n := 3421)
      (.split 3 (.leaf _ k3421_0) (.leaf _ k3421_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3422)
      (.split 2 (.leaf _ k3422_0) (.leaf _ k3422_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3423)
      (.split 2 (.leaf _ k3423_0) (.leaf _ k3423_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3424)
      (.split 2 (.leaf _ k3424_0) (.leaf _ k3424_1)))

end C4.Cert.Dir101
