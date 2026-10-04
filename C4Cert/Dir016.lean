module

public import C4Check

public section

/-! Cells `1693 ≤ n < 1742` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir016

theorem c0 : allCells dirCell 1693 1713 [
    2787795104845436516009327735722130892975366, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 63429107523846239335601152958540650576874446850767214907014858679484196346134656807011] = true := by
  decide +kernel

theorem k1713_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1713) 3).1
      29967303921657765738506412866889514272771663245918829301009350075745536467337018708308524139653626733291427287621762688805608133056669742866840665476709630974889036614).isSome = true := by
  decide +kernel

theorem k1713_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1713) 3).2 2).1
      7467895453656876872287028647652072546730774901533754355039551990479961388416053507268887822241548331758234284135975276029826398893022348132155637659072742905947115845).isSome = true := by
  decide +kernel

theorem k1713_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1713) 3).2 2).2
      290627479289142499803880288872940235336837679753413849969240075195625453484014194251605800157905713267021).isSome = true := by
  decide +kernel

theorem k1714_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).1 2).1 1).1
      61305167902581006347243809619359623958966046314798308042512790873246772027404421491).isSome = true := by
  decide +kernel

theorem k1714_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).1 2).1 1).2
      18126342225220902268484705934896650521597829927039049506128318535608434730672543491952638086056060485036).isSome = true := by
  decide +kernel

theorem k1714_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1714) 3).1 2).2
      403921194872333430292405414876259704055691902278878154935893928156522726629559807837899306330035457011881424506500402386906417285313375440530142449).isSome = true := by
  decide +kernel

theorem k1714_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).2 2).1 1).1
      62743259921051127033568541382775267040427747334732475244888352436132939620751388007601).isSome = true := by
  decide +kernel

theorem k1714_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).2 2).1 1).2
      980603484122908651788063551769689090500757911781251723786352169942820461318745452332).isSome = true := by
  decide +kernel

theorem k1714_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).2 2).2 1).1
      61235052795982838411171871227465302963585776527373392999422295546121687421121035692).isSome = true := by
  decide +kernel

theorem k1714_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1714) 3).2 2).2 1).2
      53117362786593181896544103871211035931167154463944752541207198892).isSome = true := by
  decide +kernel

theorem k1715_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).1 2).1 1).1
      3913983313491030374907843301543893833298462577017196282580633470151658874359138096947).isSome = true := by
  decide +kernel

theorem k1715_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).1 2).1 1).2
      62593467945379541425546393759380270626608647157631872888562580522342345927551371492412).isSome = true := by
  decide +kernel

theorem k1715_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).1 2).2 1).1
      244538035292245043974591036340691167352403701045860125137856119552889606880154312492).isSome = true := by
  decide +kernel

theorem k1715_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).1 2).2 1).2
      3913202205387973212101038810262725249328147409456826471307058090850016836968544320572).isSome = true := by
  decide +kernel

theorem k1715_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).2 2).1 1).1
      52938080203541643031433779094792562638788531876936333865281990348).isSome = true := by
  decide +kernel

theorem k1715_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1715) 3).2 2).1 1).2
      3906784403510708315795946764752604052106097361997052199808501494513263119846168547020).isSome = true := by
  decide +kernel

theorem k1715_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1715) 3).2 2).2
      348912904947363451412732610688020913587331284746526592974343097342886964207373120832471932872366092460790129328981078442253963057).isSome = true := by
  decide +kernel

theorem k1716_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1716) 3).1 2).1 1).1
      975554055713842424687822287262235322380886561487480020139810260303347413291556657868).isSome = true := by
  decide +kernel

theorem k1716_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1716) 3).1 2).1 1).2
      846172614251052256806987655609749357407989400336904503383172262604).isSome = true := by
  decide +kernel

theorem k1716_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1716) 3).1 2).2
      1607459874903145101582328065522337966378069475597069401402016901262465537005507181672769028624033991581862408226173354483448793709869322175215164209).isSome = true := by
  decide +kernel

theorem k1716_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1716) 3).2 2).1 1).1
      52835038145753745011858910041113479090372079425385016672601371340).isSome = true := by
  decide +kernel

theorem k1716_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1716) 3).2 2).1 1).2
      52843905361112970463118958134373613740838106409843546424122667724).isSome = true := by
  decide +kernel

theorem k1716_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1716) 3).2 2).2
      1391437228534209032821435439158491408192693080378123966208815788687552914599687995257975409626841681539649620991449078266041191217).isSome = true := by
  decide +kernel

theorem k1717_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1717) 3).1 2).1
      88965660904847949267591701651068644004163774451583079453924865687015679295171945566056418092347237788210466753724483055970629776177).isSome = true := by
  decide +kernel

theorem k1717_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1717) 3).1 2).2
      4711224465215128481030976054052720551474622649309647924644261864438358505024561383962643423184061101453456177).isSome = true := by
  decide +kernel

theorem k1717_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1717) 3).2 2).1
      1389326383218641621689733920492362043870418887805839203859039548982617623229758004449014863544994807712712203856835816283174712113).isSome = true := by
  decide +kernel

theorem k1717_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1717) 3).2 2).2
      63800305184418472946628884067593427410509965625243312792968489012691618887288128750859057).isSome = true := by
  decide +kernel

theorem k1718_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1718) 3).1 2).1
      3985036565738293331630981729059494280043661037502590475619361187727495388495904505164593).isSome = true := by
  decide +kernel

theorem k1718_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1718) 3).1 2).2
      996355703700312241550903457204531344422572980067842358600333741295161230756891643179825).isSome = true := by
  decide +kernel

theorem k1718_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1718) 3).2 2).1
      3983347826118652872803734182414286801182573253321158249202390011549459738915387071646513).isSome = true := by
  decide +kernel

theorem k1718_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1718) 3).2 2).2
      287051247992250139613123474912374171777963284813265738653846411009376106510499474803808217550887337843404).isSome = true := by
  decide +kernel

theorem k1719_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1719) 3).1 1).1
      3888405273388887124580437795839670451490814901903582604461578686417582643627940599602).isSome = true := by
  decide +kernel

theorem k1719_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1719) 3).1 1).2
      216048688964058128120415172514226154511075025083974127664858939116338).isSome = true := by
  decide +kernel

theorem k1719_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1719) 3).2
      4699841970884180345029224437226676672673507783370521380306145062818469704848286448338561452567724302315934601).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 1720 1721 [
    102297997765204178517495000765714711897808988190847728111275394557220421032646280355939677584369628186869527536651800028022207254193174503796479215911] = true := by
  decide +kernel

theorem c9 : allCells dirCell 1721 1741 [
    2360438288767516416321, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    728209397194382665587014484750769697146982499] = true := by
  decide +kernel

theorem k1741_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1741) 3).1
      21502926361476111165953713818921941981528387830418244483025599006800181213776410004334438900924781039183145375341666339621446).isSome = true := by
  decide +kernel

theorem k1741_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1741) 3).2 2).1
      1340035644542995501890436154463652106087920366953871854917036945035315112386274190716234604071571172505002201935835641422193).isSome = true := by
  decide +kernel

theorem k1741_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1741) 3).2 2).2
      1340062833158810029731819341756027781034347749421297044448655356851910927483887901981205582816591230146609588586112450426225).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1693 1742 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 1713)
      (.split 3 (.leaf _ k1713_0) (.split 2 (.leaf _ k1713_1) (.leaf _ k1713_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1714)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1714_0) (.leaf _ k1714_1)) (.leaf _ k1714_2)) (.split 2 (.split 1 (.leaf _ k1714_3) (.leaf _ k1714_4)) (.split 1 (.leaf _ k1714_5) (.leaf _ k1714_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1715)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1715_0) (.leaf _ k1715_1)) (.split 1 (.leaf _ k1715_2) (.leaf _ k1715_3))) (.split 2 (.split 1 (.leaf _ k1715_4) (.leaf _ k1715_5)) (.leaf _ k1715_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1716)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1716_0) (.leaf _ k1716_1)) (.leaf _ k1716_2)) (.split 2 (.split 1 (.leaf _ k1716_3) (.leaf _ k1716_4)) (.leaf _ k1716_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1717)
      (.split 3 (.split 2 (.leaf _ k1717_0) (.leaf _ k1717_1)) (.split 2 (.leaf _ k1717_2) (.leaf _ k1717_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1718)
      (.split 3 (.split 2 (.leaf _ k1718_0) (.leaf _ k1718_1)) (.split 2 (.leaf _ k1718_2) (.leaf _ k1718_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1719)
      (.split 3 (.split 1 (.leaf _ k1719_0) (.leaf _ k1719_1)) (.leaf _ k1719_2))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 1741)
      (.split 3 (.leaf _ k1741_0) (.split 2 (.leaf _ k1741_1) (.leaf _ k1741_2))))

end C4.Cert.Dir016
