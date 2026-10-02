module

public import C4Check

public section

/-! Cells `1324 ≤ n < 1381` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir009

theorem k1324_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1324) 3).1
      87014155260715012467646670506759676363787140001110378268748060503749368398569630840571188215996454023299560647248894912078761777).isSome = true := by
  decide +kernel

theorem k1324_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1324) 3).2
      86947474548362056544932620060550874427248930490204665806468522589745536066231519617378834278893103668226754992874921863192989489).isSome = true := by
  decide +kernel

theorem k1325_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1325) 3).1
      15953554994301842628422314612658230170550398053224659750164227793956930419551218146069297).isSome = true := by
  decide +kernel

theorem k1325_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1325) 3).2
      4595757343071528957500565361007367123664056520558367565195216953021808817948817402087602373816747166610380).isSome = true := by
  decide +kernel

theorem k1326_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1326) 3).1
      3890759013562766843150626998791009107352969946661898154431191181633023045168673658674).isSome = true := by
  decide +kernel

theorem k1326_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1326) 3).2
      972198084800965459845991811667543530062444687519678152320473577106337364502583802940).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1327 1350 [
    971329597995762898910161594688662872508146284731235695802651365042355115859384021831,
    147477846305237902708, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1350 1351 [
    85330070124429183120480537714590389099910798991499938979071800602041724899156466694696293647876808465160889797081464850470663] = true := by
  decide +kernel

theorem k1351_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1351) 3).1
      85212080580441594363363935317710200290140314795659839825604633385030727546031285599097377723480888442477665095062158872225225).isSome = true := by
  decide +kernel

theorem k1351_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1351) 3).2
      340399688715082412176909027206118055180211703001909160247667270456005837425596205220054383997993019367031469409333882303116530).isSome = true := by
  decide +kernel

theorem k1352_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1352) 3).1
      998968743946378798906731317875305696162635365696044699821829123628953061865845054599410).isSome = true := by
  decide +kernel

theorem k1352_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1352) 3).2
      5434167869572500112167578504634546156463839323915091817913651581596648648082498621879988162288313912200867361000691828290010172).isSome = true := by
  decide +kernel

theorem k1353_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1353) 1).1
      249126883382586508747210966313924363468935582014964311456096489899506959902905602526003).isSome = true := by
  decide +kernel

theorem k1353_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1353) 1).2
      63776195678166889360473156409727583519835155859091162619679017546043621024347549649455923).isSome = true := by
  decide +kernel

theorem k1354_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1354) 1).1
      52678521997763797410715472179244798902493976580074252531458365235).isSome = true := by
  decide +kernel

theorem k1354_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1354) 1).2
      972645667814667586088578346588014202241562040342331223465604435211383055352634113084).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1355 1378 [
    3885547448639583660871542348211670542700023590037946159260048790418188607876480525681,
    147473301611448425172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2391303637349954808387] = true := by
  decide +kernel

theorem c10 : allCells dirCell 1378 1379 [
    289165568777549126318803878500957267576528368024771111440915684525057030534958637993642392944398895486727] = true := by
  decide +kernel

theorem k1379_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1379) 3).1
      72178842865605511849520029424649363964436692271652277244389903868579602013685897423892485919120975391089).isSome = true := by
  decide +kernel

theorem k1379_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1379) 3).2
      4612774525377521005788912290644785212279378689152047720481261293362143476222083681135594411116715826810684).isSome = true := by
  decide +kernel

theorem k1380_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1380) 3).1
      249772396605906107768597487441171439550769329688564671699394649846086087827341507834684).isSome = true := by
  decide +kernel

theorem k1380_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1380) 3).2
      998160250231460898608768023190436881728213974790393870929983035931244103297444465701106).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1324 1381 :=
  (Cover.one (box := dirCellBox) (n := 1324)
      (.split 3 (.leaf _ k1324_0) (.leaf _ k1324_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1325)
      (.split 3 (.leaf _ k1325_0) (.leaf _ k1325_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1326)
      (.split 3 (.leaf _ k1326_0) (.leaf _ k1326_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1351)
      (.split 3 (.leaf _ k1351_0) (.leaf _ k1351_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1352)
      (.split 3 (.leaf _ k1352_0) (.leaf _ k1352_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1353)
      (.split 1 (.leaf _ k1353_0) (.leaf _ k1353_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1354)
      (.split 1 (.leaf _ k1354_0) (.leaf _ k1354_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 1379)
      (.split 3 (.leaf _ k1379_0) (.leaf _ k1379_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1380)
      (.split 3 (.leaf _ k1380_0) (.leaf _ k1380_1)))

end C4.Cert.Dir009
