module

public import C4Check

public section

/-! Cells `2164 ≤ n < 2194` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir033

theorem k2164_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2164) 3).1
      348470325232828495870098729834816434106837080307862619810068711119605462261774515734573441431028539986113905512361104712624227132).isSome = true := by
  decide +kernel

theorem k2164_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2164) 3).2
      1179503987724694524493200831287892379723737367073943212733155229210985185842551486961696328230661236638940220).isSome = true := by
  decide +kernel

theorem k2165_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2165) 1).1
      15965054834710666988150481867144368558613183802876159359227749846098031121008263007779900).isSome = true := by
  decide +kernel

theorem k2165_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2165) 1).2
      15967600037465745925026403301854412087862609015267112988371921434211734489807197496884284).isSome = true := by
  decide +kernel

theorem k2166_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2166) 3).1
      294238003372058596237849104321784353109142195950352228648504400592251723371995986282823583656586944048741436).isSome = true := by
  decide +kernel

theorem k2166_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2166) 3).2
      211003250136631200211790123829640820864883587179531284731483438140).isSome = true := by
  decide +kernel

theorem k2167_0 : (checkBoxH dirMode depth (dirCellBox 2167)
      118091846475970327414741521190305503505483336472048696932608967052495430569177351446919468233543335259697457728572415980946914938381318569480048138272449554736008381244).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 2168 2169 [
    1147474570911066748441327553151306724940873236133558891593956316427721454683636701509843069006600667614012] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2169 2189 [
    51432626631443690838650749807493939295888858276596675008364305, 147522837702712882996, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2843308620706816452945522472701571931067667] = true := by
  decide +kernel

theorem k2189_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2189) 3).1
      15426289356771782510489152139663566390824521960882817148412072126874895415124769137).isSome = true := by
  decide +kernel

theorem k2189_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2189) 3).2
      1340021842759675380889583346329698360409683692733293756989215936691099938090703959034994332233821905691062538123435906790898).isSome = true := by
  decide +kernel

theorem k2190_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2190) 3).1
      1369262402197181940422520112974843898122133257630140252503668301075111196189274502195156504562948826022132006279840465618947324).isSome = true := by
  decide +kernel

theorem k2190_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2190) 3).2
      74085687784101644277786194256379076659378013109211442891457933921922359576354644031353639900469104852759794).isSome = true := by
  decide +kernel

theorem k2191_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2191) 2).1
      4841205121213092147904285828662007998589357310192720072222407834393380488168386426813644246267708364054994570483).isSome = true := by
  decide +kernel

theorem k2191_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2191) 2).2
      250472945114446109130784262397698970494127344819157576334964367895292488368155279569724).isSome = true := by
  decide +kernel

theorem k2192_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2192) 1).1
      1180088015930468191183930650343101152472646237868992998927117272673076518363246768565278231835492883602144316).isSome = true := by
  decide +kernel

theorem k2192_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2192) 1).2
      18884330448102832780998956519163265900470929129941172334056930323975736959602761327860245666363662332083553084).isSome = true := by
  decide +kernel

theorem k2193_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2193) 1).1
      18408496942249164852797761361654699299847979553963181714168128814916259933730401513810724072138417836080188).isSome = true := by
  decide +kernel

theorem k2193_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2193) 1).2
      3992419078439744615186679347102095855539268617253349007988563543070517360981929331473468).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2164 2194 :=
  (Cover.one (box := dirCellBox) (n := 2164)
      (.split 3 (.leaf _ k2164_0) (.leaf _ k2164_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2165)
      (.split 1 (.leaf _ k2165_0) (.leaf _ k2165_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2166)
      (.split 3 (.leaf _ k2166_0) (.leaf _ k2166_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2167)
      (.leaf _ k2167_0)).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 2189)
      (.split 3 (.leaf _ k2189_0) (.leaf _ k2189_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2190)
      (.split 3 (.leaf _ k2190_0) (.leaf _ k2190_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2191)
      (.split 2 (.leaf _ k2191_0) (.leaf _ k2191_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2192)
      (.split 1 (.leaf _ k2192_0) (.leaf _ k2192_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2193)
      (.split 1 (.leaf _ k2193_0) (.leaf _ k2193_1)))

end C4.Cert.Dir033
