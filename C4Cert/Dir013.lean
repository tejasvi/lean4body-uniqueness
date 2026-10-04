module

public import C4Check

public section

/-! Cells `1631 ≤ n < 1658` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir013

theorem k1631_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).1 2).1 1).1
      16393478355233046549677942181357350381634581959917428838646515179294430134611709834580282567).isSome = true := by
  decide +kernel

theorem k1631_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).1 2).1 1).2
      16380147768884444710206745336904963444353773745157175905970823895017806966011628275846499531).isSome = true := by
  decide +kernel

theorem k1631_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).1 2).2 1).1
      302050311588230372523528726570469258998648221878663428046660480217237415036165038789723009091881472156566367431).isSome = true := by
  decide +kernel

theorem k1631_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).1 2).2 1).2
      4832390442256420203125996457466334130384232777931643760380117683888103892260733066184971716477954021133401533643).isSome = true := by
  decide +kernel

theorem k1631_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).2 2).1 1).1
      1022930597632859916851275431249095765408654746930652077478507285219110724515715506913430731).isSome = true := by
  decide +kernel

theorem k1631_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).2 2).1 1).2
      3992141275595278433013457993505629387837197106659930928516233715032534085643085197725235).isSome = true := by
  decide +kernel

theorem k1631_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).2 2).2 1).1
      999226077965576284355687810599849792623537206160473700081323187490387579949253893387059).isSome = true := by
  decide +kernel

theorem k1631_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1631) 3).2 2).2 1).2
      15972996452685392943451662517177361449375344174768207659659745482965895991953540150309683).isSome = true := by
  decide +kernel

theorem k1632_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).1 2).1 1).1
      997492661588454823659268552470294427083925087124601747591591923332270069564354528113458).isSome = true := by
  decide +kernel

theorem k1632_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).1 2).1 1).2
      997308055186448035653880024744017332724813173512520189728809098560297204933364179628851).isSome = true := by
  decide +kernel

theorem k1632_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).1 2).2 1).1
      998548688222272071025803627994443435223988742663235265290457700365281520514970238939955).isSome = true := by
  decide +kernel

theorem k1632_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).1 2).2 1).2
      3990534570506642306881225075484802656827498197795241656709214324562616725889508126871091).isSome = true := by
  decide +kernel

theorem k1632_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).2 2).1 1).1
      996826534246669094165709717960647723903187679056098238545371361619903841309038183805745).isSome = true := by
  decide +kernel

theorem k1632_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).2 2).1 1).2
      844176745410336065117015872911005053226581120171113572878793006643).isSome = true := by
  decide +kernel

theorem k1632_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).2 2).2 1).1
      997133842747701448478074826635814264218372604926202815703010388316680868502918384939826).isSome = true := by
  decide +kernel

theorem k1632_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1632) 3).2 2).2 1).2
      974986675378079470881161336605819354744607523911684118877193683095977445621057289420).isSome = true := by
  decide +kernel

theorem k1633_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1633) 2).1 3).1
      1204318164495947914490552035639177421249835384602929486334918852707283857500766679404702141541900685654636350257).isSome = true := by
  decide +kernel

theorem k1633_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1633) 2).1 3).2
      4079410271113406585536193294501493123138596530983323303390973133814351404196388255157605253).isSome = true := by
  decide +kernel

theorem k1633_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1633) 2).2 3).1 1).1
      973233312663784677736477806594588321411348968268065117546914131076287513803922177228).isSome = true := by
  decide +kernel

theorem k1633_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1633) 2).2 3).1 1).2
      973249040033713628136910271020384937482619890761424112743145202849819603443382058188).isSome = true := by
  decide +kernel

theorem k1633_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1633) 2).2 3).2
      1175986523830161133520170234401159099756547464274663844473439888088362615433070660169478709380299356154229553).isSome = true := by
  decide +kernel

theorem k1634_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1634) 2).1 3).1
      995766125578525652959535891405170388245066202887927035371757310712642037235800779244745).isSome = true := by
  decide +kernel

theorem k1634_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1634) 2).1 3).2
      3888501062377215168955521731587845483606951176828760748078093362713579957408910612273).isSome = true := by
  decide +kernel

theorem k1634_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1634) 2).2 3).1
      3982949262324211165991582530211755164874600187018542626551374405441685637567559177433905).isSome = true := by
  decide +kernel

theorem k1634_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1634) 2).2 3).2
      248885746471565389058174824856627813912359794409702972151131347551404120558462882116401).isSome = true := by
  decide +kernel

theorem k1635_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1635) 2).1
      1174778530953913089255221990744417421708824580897667500546306339609294378963964802431203091055601449234731911).isSome = true := by
  decide +kernel

theorem k1635_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1635) 2).2
      76983058488849799877841507545509801929645784313869029651231529994387302271527573693184742130734105437920681086151).isSome = true := by
  decide +kernel

theorem k1636_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1636) 2).1
      4587023262159745197468086470345164908948807046964741545156467177447777919896027359854507676689811247141575).isSome = true := by
  decide +kernel

theorem k1636_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1636) 2).2
      994653723020667266152741177114805409573947774582365744380811653557256633208719180797127).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 1637 1657 [
    44590794919553862065126279828689610547324166, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 12182276731448914243772099496437411400019070094164963] = true := by
  decide +kernel

theorem k1657_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1657) 3).1 2).1
      119533649713525037118390884420960735256906741949505323415274489163853183921298355448398332403570954594283454256249099751903413245103549638345596925706002417847312737351).isSome = true := by
  decide +kernel

theorem k1657_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1657) 3).1 2).2
      5490777202173032574728015766522369582890464003174513414876643756393106348171855326733463450075478047595169978536024621190804615).isSome = true := by
  decide +kernel

theorem k1657_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1657) 3).2 2).1 3).1
      21911297094600607050246825688049713474287031672375705464354467776547496403369492753313021707091711068542211717751012748772087369).isSome = true := by
  decide +kernel

theorem k1657_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1657) 3).2 2).1 3).2
      25861424673158934775449548476053649623814258352981903211568818007041271033534651301822844484833292757977127440911111823296228211805841062696639240261).isSome = true := by
  decide +kernel

theorem k1657_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1657) 3).2 2).2 3).1
      72562899442136779874175449120621986355327643893197417438343921462692844987500392099310890706368950898033).isSome = true := by
  decide +kernel

theorem k1657_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1657) 3).2 2).2 3).2
      87583905375327273986312550580460357532040678404335309334631042246302369573371602833775752760983887844662828717443869003934942021).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1631 1658 :=
  (Cover.one (box := dirCellBox) (n := 1631)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1631_0) (.leaf _ k1631_1)) (.split 1 (.leaf _ k1631_2) (.leaf _ k1631_3))) (.split 2 (.split 1 (.leaf _ k1631_4) (.leaf _ k1631_5)) (.split 1 (.leaf _ k1631_6) (.leaf _ k1631_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1632)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1632_0) (.leaf _ k1632_1)) (.split 1 (.leaf _ k1632_2) (.leaf _ k1632_3))) (.split 2 (.split 1 (.leaf _ k1632_4) (.leaf _ k1632_5)) (.split 1 (.leaf _ k1632_6) (.leaf _ k1632_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1633)
      (.split 2 (.split 3 (.leaf _ k1633_0) (.leaf _ k1633_1)) (.split 3 (.split 1 (.leaf _ k1633_2) (.leaf _ k1633_3)) (.leaf _ k1633_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1634)
      (.split 2 (.split 3 (.leaf _ k1634_0) (.leaf _ k1634_1)) (.split 3 (.leaf _ k1634_2) (.leaf _ k1634_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1635)
      (.split 2 (.leaf _ k1635_0) (.leaf _ k1635_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1636)
      (.split 2 (.leaf _ k1636_0) (.leaf _ k1636_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 1657)
      (.split 3 (.split 2 (.leaf _ k1657_0) (.leaf _ k1657_1)) (.split 2 (.split 3 (.leaf _ k1657_2) (.leaf _ k1657_3)) (.split 3 (.leaf _ k1657_4) (.leaf _ k1657_5)))))

end C4.Cert.Dir013
