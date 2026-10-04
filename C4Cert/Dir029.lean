module

public import C4Check

public section

/-! Cells `2108 ≤ n < 2135` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir029

theorem k2108_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).1 2).1 1).1
      846269420106346368618446843208342695201840978804854647649172662988).isSome = true := by
  decide +kernel

theorem k2108_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).1 2).1 1).2
      846328756764429729458073983252291744018646033576626523977946180300).isSome = true := by
  decide +kernel

theorem k2108_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).1 2).2 1).1
      975982866387165627668954466473290518528239770442134807642462361274064159266783615692).isSome = true := by
  decide +kernel

theorem k2108_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).1 2).2 1).2
      846605073998450069968076413965205167864560297686262625554635676364).isSome = true := by
  decide +kernel

theorem k2108_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).2 2).1 1).1
      52850094558904796718130359404509491391697004468739238829710766796).isSome = true := by
  decide +kernel

theorem k2108_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).2 2).1 1).2
      52854096995899782400309081607860079183299410710039690262893425356).isSome = true := by
  decide +kernel

theorem k2108_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).2 2).2 1).1
      52856839721576718299583384740123715850639440579781972113614041804).isSome = true := by
  decide +kernel

theorem k2108_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2108) 3).2 2).2 1).2
      52861483967704046586997123203805525040949854340312177181928583884).isSome = true := by
  decide +kernel

theorem k2109_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2109) 3).1 2).1
      1045996388608899548777110447993060259121365489992267141261943812320523806815060672324129977137).isSome = true := by
  decide +kernel

theorem k2109_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2109) 3).1 2).2 1).1
      52821576901097150131055060700935003309671857187188498864829493964).isSome = true := by
  decide +kernel

theorem k2109_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2109) 3).1 2).2 1).2
      211305545155775487812571868065917085355950824061427471162990379980).isSome = true := by
  decide +kernel

theorem k2109_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2109) 3).2 2).1
      18833019330868621287341867594932795212989029774672128852485349343534067056781058799468281431324449462541988657).isSome = true := by
  decide +kernel

theorem k2109_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2109) 3).2 2).2
      255267736278724826214253735000569729595678579947821383225638811106416626004478024402711345).isSome = true := by
  decide +kernel

theorem k2110_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2110) 3).1 2).1
      255105657411470335165028625891804403159956623954457325818970413547600823137521928404316977).isSome = true := by
  decide +kernel

theorem k2110_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2110) 3).1 2).2
      63782839276122748635614547967569729536813713355614032537505965387036887241180522330043185).isSome = true := by
  decide +kernel

theorem k2110_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2110) 3).2 2).1
      3984347434214095687924179147786164359405707542753141126556728176331995787978090375377713).isSome = true := by
  decide +kernel

theorem k2110_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2110) 3).2 2).2
      996195280708192176667349163927498754717752485896246898287918070164342472053439744275249).isSome = true := by
  decide +kernel

theorem k2111_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2111) 3).1 1).1
      248917141992080424774845306282188014651349574044956634925623033762219249509063757394636).isSome = true := by
  decide +kernel

theorem k2111_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2111) 3).1 1).2
      15559802762792563348081636270836136747122030690178744424760874409264842773897175036620).isSome = true := by
  decide +kernel

theorem k2111_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2111) 3).2 1).1
      844062692044750318377616541594864630791783888685772352990963059506).isSome = true := by
  decide +kernel

theorem k2111_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2111) 3).2 1).2
      3888711203325143409255932261483295399725147424971186340830939670229329469640717759180).isSome = true := by
  decide +kernel

theorem k2112_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2112) 3).1
      5418940357167814835165458862569313038147529452422368486200197310593759729239016341565451842160922048144674464846764539236440881).isSome = true := by
  decide +kernel

theorem k2112_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2112) 3).2
      18355424636244639204684191725265834482204184670444981008809306584394776846599462837988742871345483479932081).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2113 2114 [
    399613241802154979955692728802620791994138797118417231117626442572183787034305992404136058814320102287928535476621567975871417309731814026971649479] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2114 2132 [
    2360666868439013832001, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    39860325023437384785727603] = true := by
  decide +kernel

theorem k2132_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2132) 3).1
      1889521420905256186336178622695781877816370558329866259785105714537486571009740930423652364264563651838383381025896794284865128138358556176227118974041257360558540230).isSome = true := by
  decide +kernel

theorem k2132_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2132) 3).2 2).1
      398040099653742950140530142298361022994027758321421670021117195486578259945240649353774784129236825745286625402921842771070185128802950709745137).isSome = true := by
  decide +kernel

theorem k2132_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2132) 3).2 2).2
      1349199727437135204210751365108448677717215373269607506051971776851280529648556398168965887092634925317718113433879120526705).isSome = true := by
  decide +kernel

theorem k2133_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2133) 3).1 2).1 1).1
      3857633090562515749980015844607253725587221549643666558742056581557327323149065596).isSome = true := by
  decide +kernel

theorem k2133_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2133) 3).1 2).1 1).2
      214134090075419201188141352706033072086882130459540579390590907068).isSome = true := by
  decide +kernel

theorem k2133_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2133) 3).1 2).2
      25392757144075820112720388200848380318292524143041155718316310242814620014357552696635822004080209188195381843973475743885914953401566336091518449).isSome = true := by
  decide +kernel

theorem k2133_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2133) 3).2 2).1 1).1
      61534728065915118258795873682176215501705192538374163649947307573840999707056658236).isSome = true := by
  decide +kernel

theorem k2133_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2133) 3).2 2).1 1).2
      3938700741558463087761280335431567595086415407203780502128784862229237688049493071676).isSome = true := by
  decide +kernel

theorem k2133_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2133) 3).2 2).2
      6481353757171213459778548351836074077507481877004107322174474774482743608366458296602781153030998536660428923760872780714845639144683031079817671921).isSome = true := by
  decide +kernel

theorem k2134_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).1 2).1 1).1
      982144971287034347569119248572608285641770576572303750009916705098284657144412632636).isSome = true := by
  decide +kernel

theorem k2134_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).1 2).1 1).2
      212991949150457120274692198263914953385777981930195336610680534588).isSome = true := by
  decide +kernel

theorem k2134_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2134) 3).1 2).2
      350509610916432008249408706988522806666788241595747871957182911554955422132980353293792169112671985257676446665058136965219997937).isSome = true := by
  decide +kernel

theorem k2134_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).2 2).1 1).1
      53132853594812763589491045779756847166073841163016100019029013052).isSome = true := by
  decide +kernel

theorem k2134_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).2 2).1 1).2
      53189903279122486547016345377713744221330188290263820458084659772).isSome = true := by
  decide +kernel

theorem k2134_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).2 2).2 1).1
      212550454692371511886179057007130354639698565153189288182426356284).isSome = true := by
  decide +kernel

theorem k2134_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2134) 3).2 2).2 1).2
      11523710662575263475800353655372605825483141692).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2108 2135 :=
  (Cover.one (box := dirCellBox) (n := 2108)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2108_0) (.leaf _ k2108_1)) (.split 1 (.leaf _ k2108_2) (.leaf _ k2108_3))) (.split 2 (.split 1 (.leaf _ k2108_4) (.leaf _ k2108_5)) (.split 1 (.leaf _ k2108_6) (.leaf _ k2108_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2109)
      (.split 3 (.split 2 (.leaf _ k2109_0) (.split 1 (.leaf _ k2109_1) (.leaf _ k2109_2))) (.split 2 (.leaf _ k2109_3) (.leaf _ k2109_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2110)
      (.split 3 (.split 2 (.leaf _ k2110_0) (.leaf _ k2110_1)) (.split 2 (.leaf _ k2110_2) (.leaf _ k2110_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2111)
      (.split 3 (.split 1 (.leaf _ k2111_0) (.leaf _ k2111_1)) (.split 1 (.leaf _ k2111_2) (.leaf _ k2111_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2112)
      (.split 3 (.leaf _ k2112_0) (.leaf _ k2112_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2132)
      (.split 3 (.leaf _ k2132_0) (.split 2 (.leaf _ k2132_1) (.leaf _ k2132_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2133)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2133_0) (.leaf _ k2133_1)) (.leaf _ k2133_2)) (.split 2 (.split 1 (.leaf _ k2133_3) (.leaf _ k2133_4)) (.leaf _ k2133_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2134)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2134_0) (.leaf _ k2134_1)) (.leaf _ k2134_2)) (.split 2 (.split 1 (.leaf _ k2134_3) (.leaf _ k2134_4)) (.split 1 (.leaf _ k2134_5) (.leaf _ k2134_6)))))

end C4.Cert.Dir029
