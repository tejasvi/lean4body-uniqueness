module

public import C4Check

public section

/-! Cells `3317 ≤ n < 3343` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir104

theorem c0 : allCells dirCell 3317 3318 [
    21676568997073234254012403817982013572570947218847671823514103977164654556826955213714080343928207702660514176507880709121178684] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3318 3319 [
    4698716068266005881550224705429896469826519772423588914623328647503746485972221196161125314758717702388642035] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3319 3321 [
    62177356248749943695863492055918227144579767260640525022524901819235883333705386631996,
    51425611992273069505361634881413228207946884731528150327655185] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3321 3336 [
    147555414445509167204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    846460881763163859890195426044363551357698374539236454604232483] = true := by
  decide +kernel

theorem k3336_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3336) 3).1
      73359797290414309888305890187939258155729212161456544920799800984445501859602895692928335134579687257330).isSome = true := by
  decide +kernel

theorem k3336_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3336) 3).2
      345060327279393322745012474121269858345750351611852326625753361403612023081642347926724664758560842742716843581471733655631090).isSome = true := by
  decide +kernel

theorem k3337_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3337) 2).1
      76173831841057640533257758015409219417464322224142199005603070454658059929947569525157260216980992022309882099).isSome = true := by
  decide +kernel

theorem k3337_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3337) 2).2
      4032514705315123733551302438231255163939858602692648021664278386932677917761111016720627).isSome = true := by
  decide +kernel

theorem k3338_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3338) 2).1
      19437187318355493208088906736201780706125056721488475651133546432831873778818070339717271534337221949767980085489).isSome = true := by
  decide +kernel

theorem k3338_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3338) 2).2
      296634530793172789192444738205045378816957301477602952799350511940857103032813107544716145943272282523761724).isSome = true := by
  decide +kernel

theorem k3339_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3339) 2).1
      1049877371902331477539100134777781855727748571617017782569562566911618183450320783589774782707).isSome = true := by
  decide +kernel

theorem k3339_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3339) 2).2
      18484732865658591357602372836872467932731639009155362984905338110946442173643391523491510663975148176489532).isSome = true := by
  decide +kernel

theorem k3340_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3340) 2).1
      102818123296652679246424338642454182165032961777349387861632013158682684448903594633315816419870847786561756132835206497139218493792885770050889530428).isSome = true := by
  decide +kernel

theorem k3340_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3340) 2).2
      3999405876765096606262928328772244476827236431069550016770480886458838968055567609969724).isSome = true := by
  decide +kernel

theorem k3341_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3341) 2).1
      15972265261833902625780590964060681472420202992650550473526237178140472728245077972302908).isSome = true := by
  decide +kernel

theorem k3341_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3341) 2).2
      3993285662729643918472035848218688186108984890485049072535973677131325393332525633584188).isSome = true := by
  decide +kernel

theorem k3342_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3342) 1).1
      864855983142514208046754134150020508079189229340765009147358800985148).isSome = true := by
  decide +kernel

theorem k3342_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3342) 1).2
      15955076335628052610425768411051240444300779280538725202672577580232464988295565642103868).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3317 3343 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 3336)
      (.split 3 (.leaf _ k3336_0) (.leaf _ k3336_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3337)
      (.split 2 (.leaf _ k3337_0) (.leaf _ k3337_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3338)
      (.split 2 (.leaf _ k3338_0) (.leaf _ k3338_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3339)
      (.split 2 (.leaf _ k3339_0) (.leaf _ k3339_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3340)
      (.split 2 (.leaf _ k3340_0) (.leaf _ k3340_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3341)
      (.split 2 (.leaf _ k3341_0) (.leaf _ k3341_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3342)
      (.split 1 (.leaf _ k3342_0) (.leaf _ k3342_1)))

end C4.Cert.Dir104
