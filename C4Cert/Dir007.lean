module

public import C4Check

public section

/-! Cells `1268 ≤ n < 1298` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir007

theorem k1268_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).1 2).1 1).1
      249344980908274074992812665804833462518760048754833609947932124201416930631165258980579).isSome = true := by
  decide +kernel

theorem k1268_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).1 2).1 1).2
      997832763335970450199868151069387045918929707767432937745419706932145090164414085428018).isSome = true := by
  decide +kernel

theorem k1268_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).1 2).2 1).1
      249390584464918724344509334042241076513552933741873342820839042750107132764923514543331).isSome = true := by
  decide +kernel

theorem k1268_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).1 2).2 1).2
      997816312059701348834103977039941428028475251997450533027160614099912435919926246077235).isSome = true := by
  decide +kernel

theorem k1268_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).2 2).1 1).1
      996962685829606019494107235246903456426137570722214455959379846902726267460561263227698).isSome = true := by
  decide +kernel

theorem k1268_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).2 2).1 1).2
      997031412602860700565502003514367915352719511694664134172580829456328035504511944061747).isSome = true := by
  decide +kernel

theorem k1268_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).2 2).2 1).1
      997103098096843943815113848769825712208080045217913044115351624761439091634711566054194).isSome = true := by
  decide +kernel

theorem k1268_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1268) 3).2 2).2 1).2
      997354654094877611646514014617373213042531469012547807565053106900749885667465395008306).isSome = true := by
  decide +kernel

theorem k1269_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1269) 3).1 2).1 1).1
      997438412070158394402787630650986998840618990695162491140462835006569079313065352983346).isSome = true := by
  decide +kernel

theorem k1269_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1269) 3).1 2).1 1).2
      53999995743163122023547925094478417433697269269622751631928957427251).isSome = true := by
  decide +kernel

theorem k1269_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1269) 3).1 2).2 1).1
      210998064171150156317715749071796665553787298813739256230544993484).isSome = true := by
  decide +kernel

theorem k1269_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1269) 3).1 2).2 1).2
      211043538242356703788384591789111951470047495464193428751622925516).isSome = true := by
  decide +kernel

theorem k1269_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1269) 3).2 2).1
      19266989213872060695382739079543841674392280658220127397415480705426021407550806841752307929094863956473895794885).isSome = true := by
  decide +kernel

theorem k1269_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1269) 3).2 2).2
      5554021967160704493937432028544137786659350258004140460028887169019668387247244472642313055845264257988908336519965005960734634801).isSome = true := by
  decide +kernel

theorem k1270_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1270) 3).1 2).1
      300917131074052733481194898851664277382799190150756176396159691588392414833115918023911520831671187980073789645).isSome = true := by
  decide +kernel

theorem k1270_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1270) 3).1 2).2
      1175517757177774102609260656016200038251459453950221643946023147588167331363491699373527499364600532178924337).isSome = true := by
  decide +kernel

theorem k1270_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1270) 3).2 2).1
      995287936673232521187879938870211711445449332823928911949544334001935999397796701726349).isSome = true := by
  decide +kernel

theorem k1270_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1270) 3).2 2).2
      248824914750485432347205080449808575882921331783563210820527020918601774021645310122801).isSome = true := by
  decide +kernel

theorem k1271_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1271) 3).1 2).1
      972746215601195529702050399409568983848254733405335378163752119879096552977283671473).isSome = true := by
  decide +kernel

theorem k1271_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1271) 3).1 2).2
      242948775071332391628960940242924282820594805504995130925584225524417603693021297009).isSome = true := by
  decide +kernel

theorem k1271_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1271) 3).2
      21158634212084456711239981737640432083972614636383405218048747128558208523283668678282536273300627068376692038024711969953606).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 1272 1294 [
    44583596443855583358707609819599823630861574, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51] = true := by
  decide +kernel

theorem k1294_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1294) 3).1
      87591955176226649175530170989760824792183717328814276276606745371878248042080054444528710265096953849216299368318961444499739678).isSome = true := by
  decide +kernel

theorem k1294_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1294) 3).2 2).1
      6437656324323715944642095453384855428129340608581710506846752486679133144974828521307584331257216407276953533595804344829210216289627302941575470663).isSome = true := by
  decide +kernel

theorem k1294_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1294) 3).2 2).2
      5454535143570450372672448243650278263329145199351709524040164506829362822019737791262346667864226305560186031611574055472933197).isSome = true := by
  decide +kernel

theorem k1295_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).1 2).1 1).1
      3909812732109736500734058927561881968442791543351122411488636513532402799835905815987).isSome = true := by
  decide +kernel

theorem k1295_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).1 2).1 1).2
      15628534464661037312724679985956594016580723837924396929914118232436190592210807822131).isSome = true := by
  decide +kernel

theorem k1295_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).1 2).2 1).1
      61057505359228267220441627587628921438973869065934648654632654802112838955412447603).isSome = true := by
  decide +kernel

theorem k1295_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).1 2).2 1).2
      3909892102161794988913923460317962924760552128584266122436701744753536259616761141042).isSome = true := by
  decide +kernel

theorem k1295_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).2 2).1 1).1
      3905886683722132471178867873285378011051100434707979216681489638144833219211334194995).isSome = true := by
  decide +kernel

theorem k1295_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).2 2).1 1).2
      340417759104970994371008138934040298948557100515254461271966193851634726327089655454927164018702032382624440920804001582534348).isSome = true := by
  decide +kernel

theorem k1295_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).2 2).2 1).1
      3903970463960306403492370025524634059311180980515048280737723775159662038344517441330).isSome = true := by
  decide +kernel

theorem k1295_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1295) 3).2 2).2 1).2
      15614092831875223685789702801539107088809664125890650208628269659607828236201976633139).isSome = true := by
  decide +kernel

theorem k1296_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).1 2).1 1).1
      249471503335019442725502537360289432418238202664440821599459223467846714729812278598451).isSome = true := by
  decide +kernel

theorem k1296_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).1 2).1 1).2
      999243415748975504492567159183136852596947128829491921781444767202525800617134116926257).isSome = true := by
  decide +kernel

theorem k1296_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).1 2).2 1).1
      3899637049956259321685247986056253946052417384757638774126863015117233168798214737612).isSome = true := by
  decide +kernel

theorem k1296_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).1 2).2 1).2
      287830395187180098078421401915230810236391501996296607201584985402771475405157286185619130197045627312844).isSome = true := by
  decide +kernel

theorem k1296_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).2 2).1 1).1
      974870168184308443556448787609923580195397219251828717727625341018222204314296614092).isSome = true := by
  decide +kernel

theorem k1296_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).2 2).1 1).2
      975136079289376186304205743669119121945988769351347418294735205996782913259680136396).isSome = true := by
  decide +kernel

theorem k1296_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).2 2).2 1).1
      3896106476784991703613142567763642390025678007122970380665626707205842961685449929420).isSome = true := by
  decide +kernel

theorem k1296_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1296) 3).2 2).2 1).2
      974308493326474108012320284431644579180904170501120682565626178802852464762189348044).isSome = true := by
  decide +kernel

theorem k1297_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1297) 3).1 2).1
      22228801937448370553885165157600143975206488420482675267965477077947213115534180945853782948110437092720850074379689789421329380145).isSome = true := by
  decide +kernel

theorem k1297_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1297) 3).1 2).2
      22231025089341492598707496737066188480665224259190958531810999284572889061941558407999827664171386736495995957962671988758652711729).isSome = true := by
  decide +kernel

theorem k1297_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1297) 3).2 2).1
      5554357068313303226396224027157226750598786620741150639705175170269487602891092557754405855869474525095564628424711078752923480881).isSome = true := by
  decide +kernel

theorem k1297_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1297) 3).2 2).2
      4705048327526859868627136469136310736502899615883025273610371063190840023946485649103067552005647514677392177).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1268 1298 :=
  (Cover.one (box := dirCellBox) (n := 1268)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1268_0) (.leaf _ k1268_1)) (.split 1 (.leaf _ k1268_2) (.leaf _ k1268_3))) (.split 2 (.split 1 (.leaf _ k1268_4) (.leaf _ k1268_5)) (.split 1 (.leaf _ k1268_6) (.leaf _ k1268_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1269)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1269_0) (.leaf _ k1269_1)) (.split 1 (.leaf _ k1269_2) (.leaf _ k1269_3))) (.split 2 (.leaf _ k1269_4) (.leaf _ k1269_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1270)
      (.split 3 (.split 2 (.leaf _ k1270_0) (.leaf _ k1270_1)) (.split 2 (.leaf _ k1270_2) (.leaf _ k1270_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1271)
      (.split 3 (.split 2 (.leaf _ k1271_0) (.leaf _ k1271_1)) (.leaf _ k1271_2))).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1294)
      (.split 3 (.leaf _ k1294_0) (.split 2 (.leaf _ k1294_1) (.leaf _ k1294_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1295)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1295_0) (.leaf _ k1295_1)) (.split 1 (.leaf _ k1295_2) (.leaf _ k1295_3))) (.split 2 (.split 1 (.leaf _ k1295_4) (.leaf _ k1295_5)) (.split 1 (.leaf _ k1295_6) (.leaf _ k1295_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1296)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1296_0) (.leaf _ k1296_1)) (.split 1 (.leaf _ k1296_2) (.leaf _ k1296_3))) (.split 2 (.split 1 (.leaf _ k1296_4) (.leaf _ k1296_5)) (.split 1 (.leaf _ k1296_6) (.leaf _ k1296_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1297)
      (.split 3 (.split 2 (.leaf _ k1297_0) (.leaf _ k1297_1)) (.split 2 (.leaf _ k1297_2) (.leaf _ k1297_3))))

end C4.Cert.Dir007
