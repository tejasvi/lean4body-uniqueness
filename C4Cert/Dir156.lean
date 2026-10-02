module

public import C4Check

public section

/-! Cells `4848 ≤ n < 4877` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir156

theorem k4848_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4848) 2).1
      4775375085394434857604251721174040858753046218393543873733184087054297859712463765632296656938299627316012235).isSome = true := by
  decide +kernel

theorem k4848_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4848) 2).2
      88119066777560218273054506991223872977343814446666362385319447406703971301890074244307293305565914123007515477480487382381186867).isSome = true := by
  decide +kernel

theorem k4849_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4849) 2).1
      1005089944530337111313847309392472113071275954262990289226426133749893634005461151327435).isSome = true := by
  decide +kernel

theorem k4849_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4849) 2).2
      18552347150803211280317332362070707756853001836983577487355650114863837504673292520997216564751163062701875).isSome = true := by
  decide +kernel

theorem k4850_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4850) 2).1
      250379727619189262319385922619121718816466662632288472018372102541567428047375896425671).isSome = true := by
  decide +kernel

theorem k4850_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4850) 2).2
      3914182351049151626510317105748862494976355642381340734537290762973821749094263625523).isSome = true := by
  decide +kernel

theorem k4851_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4851) 2).1
      72042593492382510661783685504895323484273396016722918414120488723406289936779320426988695943538757432561).isSome = true := by
  decide +kernel

theorem k4851_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4851) 2).2
      62479414879666815723163179993608132121029838576360863112835810660301323759958928219315).isSome = true := by
  decide +kernel

theorem k4852_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4852) 2).1
      15228143515182548913301911876193976072596926299747513762518635497527061891711136115).isSome = true := by
  decide +kernel

theorem k4852_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4852) 2).2
      3899382005218913240086827306674044713359642083805288129397244777605303794707896881863).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 4853 4854 [
    1357563992577565308735948756444191884517139276117867762262101030536027386706706179235250426997417226691064071212603037092283846] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4854 4855 [
    339065542616604340531542525779333246648505577137813683799512406475576302410616265023622714580425171132173571206763530368677107] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4855 4856 [
    71775279887920958512847827002308353431422096393311826635502538723509608871475563528864142085357835531634] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4856 4857 [
    17936516389839875767477205851032006101985314916219472090468611753718115345063368979203171274988400094578] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4857 4859 [
    15189034715841828305261498182794727283950838907411028573414627759948143770949730674,
    15185708499028194088529076994885189890894704474815650313928351976637036862382866801] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4859 4874 [
    51443321702294347896294049766052782437957628166387254457335153,
    43568935193111486858782787219407281476188, 147603020275304892020, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4874 4875 [
    1011171058272725327701162519319366360655502909312436761477641931975980456905724785763] = true := by
  decide +kernel

theorem k4875_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4875) 3).1
      16431476093459376162883042971050286589556838937219229742000917960569846998167950783235270).isSome = true := by
  decide +kernel

theorem k4875_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4875) 3).2
      4180274250904275170515603825206194792428347917595315848203505012761815196319280667197000906).isSome = true := by
  decide +kernel

theorem k4876_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4876) 3).1
      65017395634427553593425085402439618331473788322470474591376692233354204599812070353681202).isSome = true := by
  decide +kernel

theorem k4876_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4876) 3).2
      298692309535371153019553731583245756302066995086561842630234430559724295224409372374044566270266257612164914).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4848 4877 :=
  (Cover.one (box := dirCellBox) (n := 4848)
      (.split 2 (.leaf _ k4848_0) (.leaf _ k4848_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4849)
      (.split 2 (.leaf _ k4849_0) (.leaf _ k4849_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4850)
      (.split 2 (.leaf _ k4850_0) (.leaf _ k4850_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4851)
      (.split 2 (.leaf _ k4851_0) (.leaf _ k4851_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4852)
      (.split 2 (.leaf _ k4852_0) (.leaf _ k4852_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 4875)
      (.split 3 (.leaf _ k4875_0) (.leaf _ k4875_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4876)
      (.split 3 (.leaf _ k4876_0) (.leaf _ k4876_1)))

end C4.Cert.Dir156
