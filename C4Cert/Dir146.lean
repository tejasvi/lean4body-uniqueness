module

public import C4Check

public section

/-! Cells `4573 ≤ n < 4610` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir146

theorem k4573_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4573) 2).1
      16749634831940405203454321411461771543362807801306799242849449975010342670226396252294720982833).isSome = true := by
  decide +kernel

theorem k4573_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4573) 2).2
      301762048462289572173893499340530690608467064434669705824459538815877137899877867960076467330411319907302880049).isSome = true := by
  decide +kernel

theorem k4574_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4574) 2).1
      77152670094036405716015156324345493165021848457930316102332638665011289712194222456978725805267907128600556408627).isSome = true := by
  decide +kernel

theorem k4574_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4574) 2).2
      4825594525911586100071542853493334350332875320233702151752736668402655436595195194329354683805695836069124050737).isSome = true := by
  decide +kernel

theorem k4575_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4575) 2).1
      4818569539650327098873007066749404398758848998857127231148014287252547514213623354261539760051840843367078367027).isSome = true := by
  decide +kernel

theorem k4575_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4575) 2).2
      63788010310063452752878691265862524614913708947920836304709805641583339841444685862812732).isSome = true := by
  decide +kernel

theorem k4576_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4576) 2).1
      996089606069774466669323083944509920373599761961611327176573179574491718664961341930556).isSome = true := by
  decide +kernel

theorem k4576_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4576) 2).2
      996131035089873651398002151758990693580022597180079880380739269173151401919756136299580).isSome = true := by
  decide +kernel

theorem k4577_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4577) 1).1
      995694734202919574434719414377353617830347027578143048933736211778136754941481876667452).isSome = true := by
  decide +kernel

theorem k4577_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4577) 1).2
      863631050829593987574336500069624710397851542165429411629798953532476).isSome = true := by
  decide +kernel

theorem k4578_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4578) 3).1
      13490948472466491928006058097193742172457892697407791052354047753276).isSome = true := by
  decide +kernel

theorem k4578_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4578) 3).2
      182809822182122992488738477079044065142267624508).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4579 4580 [
    75210294422866583752071993076349244015417182112741378795548482061276121222752222444886337114006056057097405244] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4580 4581 [
    346701215673839670723290288834701655527550706648169042930160911999661022206731969507379556854571350317875300232998093898026787644] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4581 4582 [
    18351658711703843413336306143809544507983891450754892229035586892470530370699921047797132077135521369760572] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4582 4584 [
    62171698936799831940068878579209140770873316299565487846293109146929769396837476251057,
    51423307621869254579594571411139776399368436780077433331775377] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4584 4597 [
    147564151027574829572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    856719106741666450408691744443593792697230416098166198666610327823] = true := by
  decide +kernel

theorem k4597_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4597) 3).1
      3941155886656104375542068380352242797227684752462160244559350772845915908636196132658).isSome = true := by
  decide +kernel

theorem k4597_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4597) 3).2
      3408081944808195580704580976411990738165781180301038424693093004082).isSome = true := by
  decide +kernel

theorem k4598_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4598) 2).1
      4014722698707106352428799107469605445172767003143654489482594391661344394259642982953779).isSome = true := by
  decide +kernel

theorem k4598_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4598) 2).2
      1003649962909139339346021858562422395509170254150427953702913624463042688797978418574131).isSome = true := by
  decide +kernel

theorem k4599_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4599) 2).1
      302691015350397469555458511740534672392911522593916177751866999567752694904292157550912603108072048230326448945).isSome = true := by
  decide +kernel

theorem k4599_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4599) 2).2
      4728553715877923552592578801307959882980521222845209859652614968138529830464501170092968686064894879216284467).isSome = true := by
  decide +kernel

theorem k4600_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4600) 2).1
      302194846517471092782191811323070142702251796271830442651737481501172745631667391662303475738210818574467838769).isSome = true := by
  decide +kernel

theorem k4600_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4600) 2).2
      18881452743573746331643682785920865377839843170265398002181388494312667044629013644885005913666489776514904883).isSome = true := by
  decide +kernel

theorem k4601_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4601) 2).1
      1022195869450293056665064623761943500672433747047757926898391555673410363110404341748052787).isSome = true := by
  decide +kernel

theorem k4601_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4601) 2).2
      15972655271833868508395595249222970637275644753181109957085110208996305427358723164451635).isSome = true := by
  decide +kernel

theorem k4602_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4602) 2).1
      63825705781843065560045170900228172533839495189768461172484099300153962964671790434405171).isSome = true := by
  decide +kernel

theorem k4602_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4602) 2).2
      15960559515326149229459748216873724911607384762224374172597207401645448461909183152114481).isSome = true := by
  decide +kernel

theorem k4603_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4603) 2).1
      249186970445320216030669977598428789562676595932272281795300790327345986635347386580028).isSome = true := by
  decide +kernel

theorem k4603_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4603) 2).2
      249196245970671734739197826561178909366046609287437113185871030082199337032828996435004).isSome = true := by
  decide +kernel

theorem k4604_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4604) 2).1
      996168571179923517105512345592553169459213536269531220291988223234853370353406342478908).isSome = true := by
  decide +kernel

theorem k4604_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4604) 2).2
      210954213516091282636779409221763011604512095261280642056909634620).isSome = true := by
  decide +kernel

theorem k4605_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4605) 3).1
      210878869071624286102453930033131560601935180934987204345648692284).isSome = true := by
  decide +kernel

theorem k4605_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4605) 3).2
      210843741037191957163034619954554064565873056453650690218636704828).isSome = true := by
  decide +kernel

theorem c20 : allCells dirCell 4606 4607 [
    75212899945927416888319012254481072906566902650651342449076952204142027820860690925394316903855163759469249340] = true := by
  decide +kernel

theorem c21 : allCells dirCell 4607 4608 [
    346772990761760315071447992969905598306888739433236043722736930594110565015015599630377201146103219298636873782399235442541011772] = true := by
  decide +kernel

theorem c22 : allCells dirCell 4608 4609 [
    73418193202400318994548930565828068274426329469224574698483359518877729842398536160060615098441051043488572] = true := by
  decide +kernel

theorem c23 : allCells dirCell 4609 4610 [
    248744581441987805876440259764659600182676229556675069353632553074694578191637998947132] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4573 4610 :=
  (Cover.one (box := dirCellBox) (n := 4573)
      (.split 2 (.leaf _ k4573_0) (.leaf _ k4573_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4574)
      (.split 2 (.leaf _ k4574_0) (.leaf _ k4574_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4575)
      (.split 2 (.leaf _ k4575_0) (.leaf _ k4575_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4576)
      (.split 2 (.leaf _ k4576_0) (.leaf _ k4576_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4577)
      (.split 1 (.leaf _ k4577_0) (.leaf _ k4577_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4578)
      (.split 3 (.leaf _ k4578_0) (.leaf _ k4578_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 4597)
      (.split 3 (.leaf _ k4597_0) (.leaf _ k4597_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4598)
      (.split 2 (.leaf _ k4598_0) (.leaf _ k4598_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4599)
      (.split 2 (.leaf _ k4599_0) (.leaf _ k4599_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4600)
      (.split 2 (.leaf _ k4600_0) (.leaf _ k4600_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4601)
      (.split 2 (.leaf _ k4601_0) (.leaf _ k4601_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4602)
      (.split 2 (.leaf _ k4602_0) (.leaf _ k4602_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4603)
      (.split 2 (.leaf _ k4603_0) (.leaf _ k4603_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4604)
      (.split 2 (.leaf _ k4604_0) (.leaf _ k4604_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4605)
      (.split 3 (.leaf _ k4605_0) (.leaf _ k4605_1))).trans <|
  (Cover.dir c20).trans <|
  (Cover.dir c21).trans <|
  (Cover.dir c22).trans <|
  (Cover.dir c23)

end C4.Cert.Dir146
