module

public import C4Check

public section

/-! Cells `4905 ≤ n < 4934` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir158

theorem k4905_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4905) 2).1
      1006572243066163181799627818595698996367716141458354128547700045006911880293544650437427).isSome = true := by
  decide +kernel

theorem k4905_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4905) 2).2
      1006725427663229150762297390658821504654821417238989960752896533572683156240097842131763).isSome = true := by
  decide +kernel

theorem k4906_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4906) 2).1
      4628812259367997112572237571530495435492180092753198683917941840085499902331885722570557565729654622204876).isSome = true := by
  decide +kernel

theorem k4906_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4906) 2).2
      15685715782643775182839273572847897698604774315858468638892853661171807556592331113420).isSome = true := by
  decide +kernel

theorem k4907_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4907) 2).1
      3908096640886385763051773194911684141016603688188326723831715945358688444738896353075).isSome = true := by
  decide +kernel

theorem k4907_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4907) 2).2
      250170786583876943066971493160490398457452916736735035600439237294396607264628662455091).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 4908 4909 [
    1392814447622232799385029594552082646949018850772630467046426581289843108954502590175333539276046870133784041106478995588448055538] = true := by
  decide +kernel

theorem k4909_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4909) 2).1
      974482430233924769453074967974948247163552706250109774696365549390400081466062896188).isSome = true := by
  decide +kernel

theorem k4909_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4909) 2).2
      52832408726751866668387615407984009306460309244962412719161293884).isSome = true := by
  decide +kernel

theorem k4910_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4910) 1).1
      973684745315860498931798403611708164603506852178471839708558289107032243643027913788).isSome = true := by
  decide +kernel

theorem k4910_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4910) 1).2
      973638774951836884378036725041725780910102364893190676321927060059560619587579771964).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4911 4912 [
    347203058345973576434588465177632293878818284624880689342507474595432349653655683118212655553455409889274291202503621356374313202] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4912 4913 [
    4592944066591084687468910781695786852840400673652742871860624367351500024937061363321274186462630298596156] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4913 4914 [
    286959718678541636286198358252756285547874887362422396006651483769763112488331392270481033856126981493564] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4914 4915 [
    4590146246108097822937306105929473796234777185798868070074466891246163632111799180195161382345502596337468] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4915 4916 [
    5291104050110072990220658126121916893625156680929563930019098695937192466902781757882085653394312072080439477795528497420092] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4916 4918 [
    60729594657724619980136186273355170579130801236659171548971973744377039232081188668,
    3291758154784228570469438231183691805715062387896877098267431164] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4918 4920 [
    3794817746172529916313842141899533347651384502390905310564455666954332707457490300,
    51425601504280042597886978414024075057302321254671400508937585] = true := by
  decide +kernel

theorem c13 : allCells dirCell 4920 4932 [
    43556236721288561899630800164140327788892, 147566588301213002580, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    995583315380939663997978868209283554117396541560605355381494943171261596867927921927] = true := by
  decide +kernel

theorem c14 : allCells dirCell 4932 4933 [
    4893144051472890368174289852125026044951521505396946734811743528549459240868499994947978110039698383855061916875] = true := by
  decide +kernel

theorem k4933_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4933) 2).1
      3411204129701885818425064724260888425817435502776442338410863235891).isSome = true := by
  decide +kernel

theorem k4933_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4933) 2).2
      3411297627132364336376614125395424309001074637906041499342825067315).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4905 4934 :=
  (Cover.one (box := dirCellBox) (n := 4905)
      (.split 2 (.leaf _ k4905_0) (.leaf _ k4905_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4906)
      (.split 2 (.leaf _ k4906_0) (.leaf _ k4906_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4907)
      (.split 2 (.leaf _ k4907_0) (.leaf _ k4907_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 4909)
      (.split 2 (.leaf _ k4909_0) (.leaf _ k4909_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4910)
      (.split 1 (.leaf _ k4910_0) (.leaf _ k4910_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.one (box := dirCellBox) (n := 4933)
      (.split 2 (.leaf _ k4933_0) (.leaf _ k4933_1)))

end C4.Cert.Dir158
