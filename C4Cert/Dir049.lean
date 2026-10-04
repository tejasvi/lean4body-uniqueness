module

public import C4Check

public section

/-! Cells `2498 ≤ n < 2524` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir049

theorem k2498_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).1 2).1 1).1
      4640867725338649400691020835818810019367154059383653221941925328745880500315702064305912074417080039371324).isSome = true := by
  decide +kernel

theorem k2498_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).1 2).1 1).2
      872687672897684313743659266041411270459049868513319373374970101756476).isSome = true := by
  decide +kernel

theorem k2498_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).1 2).2 1).1
      4022302265451070289113054128483039922213862523566379369545287475239773465193410690271804).isSome = true := by
  decide +kernel

theorem k2498_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).1 2).2 1).2
      1005558638022497113410163673951382002826243584818610877905216520294489370252032954321468).isSome = true := by
  decide +kernel

theorem k2498_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).2 2).1 1).1
      62709262437315840831530150341732603467773514132275930264119276758350288839731715095612).isSome = true := by
  decide +kernel

theorem k2498_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).2 2).1 1).2
      62768503812324180671824801418639306076061683370066743325768794164899149913227725225020).isSome = true := by
  decide +kernel

theorem k2498_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).2 2).2 1).1
      15681099933631290743162920627566858131608233701596757224422142401375071173575352106044).isSome = true := by
  decide +kernel

theorem k2498_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2498) 3).2 2).2 1).2
      3403568391662518213254710655301968084775497674367914808504961842236).isSome = true := by
  decide +kernel

theorem k2499_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).1 2).1 1).1
      62668416430436107386040763380952978814664704569623076301367891795658583805889588182076).isSome = true := by
  decide +kernel

theorem k2499_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).1 2).1 1).2
      54300693823989433983609799551869179382289211970355884773102099053628).isSome = true := by
  decide +kernel

theorem k2499_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).1 2).2 1).1
      3394681850088392048204068635776586461314225993069636508217098681404).isSome = true := by
  decide +kernel

theorem k2499_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).1 2).2 1).2
      3394675491384394140714466270688008423428854675955876998275409951804).isSome = true := by
  decide +kernel

theorem k2499_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).2 2).1 1).1
      847332116168240984897690996470251444908252516752274880741456694988).isSome = true := by
  decide +kernel

theorem k2499_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).2 2).1 1).2
      3392601595031903537320927209165823448231415959612091382939208463308).isSome = true := by
  decide +kernel

theorem k2499_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).2 2).2 1).1
      2940359569382774828202162192465537799589821365308).isSome = true := by
  decide +kernel

theorem k2499_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2499) 3).2 2).2 1).2
      13560087214062546399582576862093640084719018213697689882426795047996).isSome = true := by
  decide +kernel

theorem k2500_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).1 2).1 1).1
      183524518513191451990897036077670615477710170828).isSome = true := by
  decide +kernel

theorem k2500_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).1 2).1 1).2
      846506494861673700084360791167679844476758569361312616159712863180).isSome = true := by
  decide +kernel

theorem k2500_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).1 2).2 1).1
      211662089732609108144668960014602950428362591433949347858313894604).isSome = true := by
  decide +kernel

theorem k2500_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).1 2).2 1).2
      846669887427809475876711503339532462768805035201281906348730049484).isSome = true := by
  decide +kernel

theorem k2500_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).2 2).1 1).1
      845701178017634275793935835433392012752499082105497038469061354444).isSome = true := by
  decide +kernel

theorem k2500_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).2 2).1 1).2
      845685607274490291811933736829860379083712955500200605966418256844).isSome = true := by
  decide +kernel

theorem k2500_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).2 2).2 1).1
      845828424678071316815685335159683753245761104307254443940075480012).isSome = true := by
  decide +kernel

theorem k2500_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2500) 3).2 2).2 1).2
      183414231551918770328842335085761647568438109132).isSome = true := by
  decide +kernel

theorem k2501_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2501) 3).1 2).1 1).1
      211284129646181915908889938452011362264993156280599745703047578572).isSome = true := by
  decide +kernel

theorem k2501_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2501) 3).1 2).1 1).2
      845092186946077144136392002598814559169498736157497632589134898124).isSome = true := by
  decide +kernel

theorem k2501_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2501) 3).1 2).2 1).1
      211317864164094412623583548248830911104200086642142229563870528460).isSome = true := by
  decide +kernel

theorem k2501_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2501) 3).1 2).2 1).2
      845272204023827586352035233535507659008563763410722799070318896076).isSome = true := by
  decide +kernel

theorem k2501_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2501) 3).2 2).1
      1390540142660298743741621861978434610046022417050196852976971124862140360393000002085750951250061909356344542123327116754401665996).isSome = true := by
  decide +kernel

theorem k2501_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2501) 3).2 2).2
      77163598148984372339280222580994418340951288826661967416317573468966555593683341664913700865548901060926155722545).isSome = true := by
  decide +kernel

theorem k2502_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2502) 3).1 2).1
      63844397922698246524581118146430587913828963785014407801053643605464786736248484999383857).isSome = true := by
  decide +kernel

theorem k2502_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2502) 3).1 2).2
      1205074502783921279572377177307576681111924338171242980922990007450918376885696667991271543879310477830219566897).isSome = true := by
  decide +kernel

theorem k2502_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2502) 3).2 2).1
      3984852711985627332466023408170382187082198095039249769868069378537821896492110198436657).isSome = true := by
  decide +kernel

theorem k2502_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2502) 3).2 2).2
      15956922724775185906700142778665395483976421665325997153323922510235239920274930718323505).isSome = true := by
  decide +kernel

theorem k2503_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2503) 3).1 2).1
      62244909614093973993828185968428900290743930509955344814014274735553433254088608261068).isSome = true := by
  decide +kernel

theorem k2503_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2503) 3).1 2).2
      62311923504162739501462958268854730332015932570565518131002459918695996610990334485452).isSome = true := by
  decide +kernel

theorem k2503_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2503) 3).2 1).1
      3889218331063292195953887970945201601405281891122024313164125111831991830120727179980).isSome = true := by
  decide +kernel

theorem k2503_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2503) 3).2 1).2
      3891475410172203851885661227438935862191856662126872814178601136913082631756944110284).isSome = true := by
  decide +kernel

theorem k2504_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2504) 3).1 1).1
      13498345685327675109265989952679982845229113978184330477140167455538).isSome = true := by
  decide +kernel

theorem k2504_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2504) 3).1 1).2
      3888564628632865114027735832484909083102838130114213420085379072001809962702000747212).isSome = true := by
  decide +kernel

theorem k2504_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2504) 3).2
      5418702656528421369192955215314075815287473343835605080940305534388069661469559984596329705224982150700247287961137099799124786).isSome = true := by
  decide +kernel

theorem k2505_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2505) 3).1
      1174729094717990545887048980697557739367773227774670082275893624233830191059879059858954579828164660034919217).isSome = true := by
  decide +kernel

theorem k2505_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2505) 3).2
      15545698634994287641990438769546346392731701538721158901928441648248322464807524751153).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 2506 2523 [
    99900529763288585150874866742469069815370348519621648495184706223921254369407947681983532271165322349981900238228522947818860483093267424845407687,
    2360815740114612343617, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2523 2524 [
    16001237740711169647613365472264482015472438146577998783677153925232424584851520631987] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2498 2524 :=
  (Cover.one (box := dirCellBox) (n := 2498)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2498_0) (.leaf _ k2498_1)) (.split 1 (.leaf _ k2498_2) (.leaf _ k2498_3))) (.split 2 (.split 1 (.leaf _ k2498_4) (.leaf _ k2498_5)) (.split 1 (.leaf _ k2498_6) (.leaf _ k2498_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2499)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2499_0) (.leaf _ k2499_1)) (.split 1 (.leaf _ k2499_2) (.leaf _ k2499_3))) (.split 2 (.split 1 (.leaf _ k2499_4) (.leaf _ k2499_5)) (.split 1 (.leaf _ k2499_6) (.leaf _ k2499_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2500)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2500_0) (.leaf _ k2500_1)) (.split 1 (.leaf _ k2500_2) (.leaf _ k2500_3))) (.split 2 (.split 1 (.leaf _ k2500_4) (.leaf _ k2500_5)) (.split 1 (.leaf _ k2500_6) (.leaf _ k2500_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2501)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2501_0) (.leaf _ k2501_1)) (.split 1 (.leaf _ k2501_2) (.leaf _ k2501_3))) (.split 2 (.leaf _ k2501_4) (.leaf _ k2501_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2502)
      (.split 3 (.split 2 (.leaf _ k2502_0) (.leaf _ k2502_1)) (.split 2 (.leaf _ k2502_2) (.leaf _ k2502_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2503)
      (.split 3 (.split 2 (.leaf _ k2503_0) (.leaf _ k2503_1)) (.split 1 (.leaf _ k2503_2) (.leaf _ k2503_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2504)
      (.split 3 (.split 1 (.leaf _ k2504_0) (.leaf _ k2504_1)) (.leaf _ k2504_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2505)
      (.split 3 (.leaf _ k2505_0) (.leaf _ k2505_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9)

end C4.Cert.Dir049
