module

public import C4Check

public section

/-! Cells `1381 ≤ n < 1464` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir010

theorem k1381_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1381) 1).1
      52765702628636690656460393154874247822848285915825843273880910908).isSome = true := by
  decide +kernel

theorem k1381_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1381) 1).2
      4597134977818648332646190706092527057976084551014478173544711271677282302833031824866488266123833729473331).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 1382 1383 [
    6399464316041349858700604931433418920839791218251839708871589873597694959561534157559205045309661744251233684167687790017606335904167348418301615303] = true := by
  decide +kernel

theorem c2 : allCells dirCell 1383 1406 [
    3290476545620356121113249742704106484932075277142730373960520435, 147470640037455202484, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2391273522826391515971] = true := by
  decide +kernel

theorem c3 : allCells dirCell 1406 1407 [
    979680812501122169524607682919341274631334420579388969171128769732142113423866677511] = true := by
  decide +kernel

theorem k1407_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1407) 3).1
      15281847679819804918932752508087270757565323297473470949092404727221212678392357234).isSome = true := by
  decide +kernel

theorem k1407_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1407) 3).2
      1153410465000591435041721354584843329722770738488051503329558564888889345938276708060067783250693083927793).isSome = true := by
  decide +kernel

theorem k1408_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1408) 2).1
      15604598546386591541047814619643114007842919461727202345982473202872087636358569902908).isSome = true := by
  decide +kernel

theorem k1408_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1408) 2).2
      15603915445431761812038258687299947117669924162730825973390756153757338963293710566204).isSome = true := by
  decide +kernel

theorem k1409_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1409) 1).1
      973467170171109773899957847835886114207761080355477676219905236662585268247814044732).isSome = true := by
  decide +kernel

theorem k1409_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1409) 1).2
      844537307631157693521583389306067926175848554450170879988567440444).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 1410 1411 [
    293912375326865136125736929408197333555105503733244711383913528935565712784463394181948898675319818629510385] = true := by
  decide +kernel

theorem c8 : allCells dirCell 1411 1434 [
    51439948559921660103877229151792494197555719403513631564256657, 147469545611111511156, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2391033173982878209603] = true := by
  decide +kernel

theorem c9 : allCells dirCell 1434 1435 [
    18070032567378724300814431005551850578697326425576598367600063003807463824312280330297605224368793032051] = true := by
  decide +kernel

theorem k1435_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1435) 3).1
      3820346834604861413251933764370888434257408085507828992717719332775744939573665148).isSome = true := by
  decide +kernel

theorem k1435_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1435) 3).2
      976736362602603756852635544215062778434622515128228502806561480637490686379018776828).isSome = true := by
  decide +kernel

theorem k1436_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1436) 1).1
      15599394668974730786589852893029828623474640178983419343147064538863762215065934611260).isSome = true := by
  decide +kernel

theorem k1436_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1436) 1).2
      15605521474474420522188527605744855846508344913111440557075886558397145144907307402044).isSome = true := by
  decide +kernel

theorem c12 : allCells dirCell 1437 1438 [
    1388944710549844104394908832924047449202685845701995101247740238331342146853292821758962524332690745030260677222917771047302721779] = true := by
  decide +kernel

theorem c13 : allCells dirCell 1438 1439 [
    84713315919530765360131418109470490467194170313138620209458368113022836609015099707654300826334514068744878837054840063750396] = true := by
  decide +kernel

theorem c14 : allCells dirCell 1439 1462 [
    51437469461051922906073109882142046767903919453061064261095889, 147469663739922538756, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c15 : allCells dirCell 1462 1463 [
    18067545302257823632441798006378959696006438956948845732459412680798335947752191153543808044259555912051] = true := by
  decide +kernel

theorem c16 : allCells dirCell 1463 1464 [
    115807602002764411598954034653158586628267036610013908743635983071243078090910393113054659545751709230039083585234301955369010023395744376099274710308665936334386675] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1381 1464 :=
  (Cover.one (box := dirCellBox) (n := 1381)
      (.split 1 (.leaf _ k1381_0) (.leaf _ k1381_1))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 1407)
      (.split 3 (.leaf _ k1407_0) (.leaf _ k1407_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1408)
      (.split 2 (.leaf _ k1408_0) (.leaf _ k1408_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1409)
      (.split 1 (.leaf _ k1409_0) (.leaf _ k1409_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 1435)
      (.split 3 (.leaf _ k1435_0) (.leaf _ k1435_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1436)
      (.split 1 (.leaf _ k1436_0) (.leaf _ k1436_1))).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16)

end C4.Cert.Dir010
