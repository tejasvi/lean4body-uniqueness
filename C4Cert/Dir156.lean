module

public import C4Check

public section

/-! Cells `5303 ≤ n < 5338` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir156

theorem k5303_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5303) 2).1
      249039465102808567932308533713478911877909798074974989009274881968176576520350159494323).isSome = true := by
  decide +kernel

theorem k5303_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5303) 2).2
      62264728732912030221003089970228947723089656177234045270748308038981961330582147390643).isSome = true := by
  decide +kernel

theorem k5304_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5304) 2).1
      17939979525703923827661292120636272991831343436515024049372974888120452612983930252024276788509487816113).isSome = true := by
  decide +kernel

theorem k5304_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5304) 2).2
      15561269132118359709552318714488400326683232941181202845967543321275639339574816655932).isSome = true := by
  decide +kernel

theorem k5305_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5305) 2).1
      60764519174509249391034976494488206395399955109263802040610239440902088530684401468).isSome = true := by
  decide +kernel

theorem k5305_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5305) 2).2
      15556215335724486139454100985690156719930889150021880481353926675241601512454706524849).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 5306 5307 [
    21676890366152538097472527589684485740302321740590066031596308479587381715234661238783660520451642021996027905625641104707515634] = true := by
  decide +kernel

theorem c4 : allCells dirCell 5307 5308 [
    338622181786624372602487232498703609422004321938370639628584955472793759139677887737221370175972127122387868559753517965604083] = true := by
  decide +kernel

theorem c5 : allCells dirCell 5308 5309 [
    99931296927994153052639638097946551343348039579651152804844038742401835769080903355990366035444442149204296656155951120306975210249885394788631539] = true := by
  decide +kernel

theorem c6 : allCells dirCell 5309 5310 [
    1322471800103981327768116167845899432791224533179767882201992799226970733652815412863623412867706213676109753822365982012786] = true := by
  decide +kernel

theorem c7 : allCells dirCell 5310 5323 [
    15179873140305198878303855675878264845210296255503792814525960508547517425478368625,
    174243965700641468566414293529785006540625, 2361289814346658228802, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 5323 5324 [
    22146697696843693263429236763442204799176994522737291711952827761866049274008638141710480729915311206717054004172304508468180027] = true := by
  decide +kernel

theorem k5324_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5324) 3).1
      253305790819652907971100861800071192637828778309578474396046347832872156938547793064754).isSome = true := by
  decide +kernel

theorem k5324_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5324) 3).2
      4771494117385947030870747107320485198610357295219490786388906585373867704145161039124773711000636891398992690).isSome = true := by
  decide +kernel

theorem k5325_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5325) 2).1 3).1
      3414218533621332711233171226838978704871334969523439320916304551474).isSome = true := by
  decide +kernel

theorem k5325_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5325) 2).1 3).2
      62831467787269475305049360281370215195200845152862904400024074336662902536548210799409).isSome = true := by
  decide +kernel

theorem k5325_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 5325) 2).2
      311476559414623054460593553896204997033590266296242946902568882525166239079522797149050446045680191940401604916019).isSome = true := by
  decide +kernel

theorem k5326_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5326) 2).1 3).1
      62744146077968573765885339323770239643465390213642281990834000846060481127588401607473).isSome = true := by
  decide +kernel

theorem k5326_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5326) 2).1 3).2
      250708289756787359848242944582021885639670355397553041911942533658066406679346830471985).isSome = true := by
  decide +kernel

theorem k5326_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5326) 2).2 3).1
      2952212879603882448189983571697609366881926721074).isSome = true := by
  decide +kernel

theorem k5326_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5326) 2).2 3).2
      54361874198721681824996646245815368479497630606098452155997351932722).isSome = true := by
  decide +kernel

theorem k5327_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5327) 2).1 3).1
      250385069803189824269998802583959815219963662396337340513366868646044149063944927540017).isSome = true := by
  decide +kernel

theorem k5327_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5327) 2).1 3).2
      15633165171266965013251682985626510249096156992443137800773909885362291753555512980172).isSome = true := by
  decide +kernel

theorem k5327_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5327) 2).2 3).1
      3913085266236683729538451506790656440134880456552248277939616124193451538020685966540).isSome = true := by
  decide +kernel

theorem k5327_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5327) 2).2 3).2
      3908855328748823665327302698688742528388663012462637807497635791459213425734550154444).isSome = true := by
  decide +kernel

theorem k5328_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5328) 2).1 3).1
      13546318504403161297595920804743715050743118386669621939972999574321).isSome = true := by
  decide +kernel

theorem k5328_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5328) 2).1 3).2
      211517186173967626380706708472830096237452174998681438822391032524).isSome = true := by
  decide +kernel

theorem k5328_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5328) 2).2 3).1
      976330235418953223898144710375197973875322029965486133853449394648702779977262529740).isSome = true := by
  decide +kernel

theorem k5328_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5328) 2).2 3).2
      3384506246042695990034929935332236804751482433720249726828512375601).isSome = true := by
  decide +kernel

theorem k5329_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5329) 2).1
      5432094373358519383426500863319089163442315937091563285446693984014906452244984524409452832889676889733042191620155444802476851).isSome = true := by
  decide +kernel

theorem k5329_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5329) 2).2
      18848010659875966333539442982462326111223408782968154853867631591277140795129577771799706573851853638463900467).isSome = true := by
  decide +kernel

theorem k5330_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5330) 2).1
      5428452904249842766151015666686517483605040574528540229791585380226065774614761911294084384793991320702214153669371470571494193).isSome = true := by
  decide +kernel

theorem k5330_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5330) 2).2
      255221863254961578052478047799370287587697676135645298304638844811360664124367110808218419).isSome = true := by
  decide +kernel

theorem k5331_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5331) 2).1
      15567377360224677605127342069473636376841296575101484401289864938312314866453412469555).isSome = true := by
  decide +kernel

theorem k5331_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5331) 2).2
      18382252590721782530992297965475772570245767316264408704742193552390081114312017851408140020974900160541644).isSome = true := by
  decide +kernel

theorem k5332_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5332) 2).1
      3890486214641968340046391933193985092153391262390191423773312759550436122260065490737).isSome = true := by
  decide +kernel

theorem k5332_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5332) 2).2
      15561486539005546565857491439444755484560981475787161724524568883299338404465381890867).isSome = true := by
  decide +kernel

theorem k5333_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5333) 2).1
      3889207605825965379643761984255024702939594050673702425219063344142276205130187928124).isSome = true := by
  decide +kernel

theorem k5333_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5333) 2).2
      972347390107432720905516474343614350548496994702612624467889109393844668106192813116).isSome = true := by
  decide +kernel

theorem k5334_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5334) 2).1
      52694859945021255343304883349691698114499499735485858570258860604).isSome = true := by
  decide +kernel

theorem k5334_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5334) 2).2
      972082419812979813613632174711320647320763045129857695557663119873852477673953918012).isSome = true := by
  decide +kernel

theorem c20 : allCells dirCell 5335 5336 [
    86694710575326263743349063744586703591687997248391460868556866412863277010989153205844607065010398466775331778646124665958160626] = true := by
  decide +kernel

theorem c21 : allCells dirCell 5336 5337 [
    1354400470435519246861205702750916053414982941622860398890722452124945594721923681452701974095159086029924057419686494473909490] = true := by
  decide +kernel

theorem c22 : allCells dirCell 5337 5338 [
    338559183022242058858722331111917845738118342895389839564840780979415396723442404244840844525939091734715658211242575298655473] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 5303 5338 :=
  (Cover.one (box := dirCellBox) (n := 5303)
      (.split 2 (.leaf _ k5303_0) (.leaf _ k5303_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5304)
      (.split 2 (.leaf _ k5304_0) (.leaf _ k5304_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5305)
      (.split 2 (.leaf _ k5305_0) (.leaf _ k5305_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 5324)
      (.split 3 (.leaf _ k5324_0) (.leaf _ k5324_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5325)
      (.split 2 (.split 3 (.leaf _ k5325_0) (.leaf _ k5325_1)) (.leaf _ k5325_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 5326)
      (.split 2 (.split 3 (.leaf _ k5326_0) (.leaf _ k5326_1)) (.split 3 (.leaf _ k5326_2) (.leaf _ k5326_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5327)
      (.split 2 (.split 3 (.leaf _ k5327_0) (.leaf _ k5327_1)) (.split 3 (.leaf _ k5327_2) (.leaf _ k5327_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5328)
      (.split 2 (.split 3 (.leaf _ k5328_0) (.leaf _ k5328_1)) (.split 3 (.leaf _ k5328_2) (.leaf _ k5328_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5329)
      (.split 2 (.leaf _ k5329_0) (.leaf _ k5329_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5330)
      (.split 2 (.leaf _ k5330_0) (.leaf _ k5330_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5331)
      (.split 2 (.leaf _ k5331_0) (.leaf _ k5331_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5332)
      (.split 2 (.leaf _ k5332_0) (.leaf _ k5332_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5333)
      (.split 2 (.leaf _ k5333_0) (.leaf _ k5333_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5334)
      (.split 2 (.leaf _ k5334_0) (.leaf _ k5334_1))).trans <|
  (Cover.dir c20).trans <|
  (Cover.dir c21).trans <|
  (Cover.dir c22)

end C4.Cert.Dir156
