module

public import C4Check

public section

/-! Cells `4428 ≤ n < 4455` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir147

theorem k4428_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4428) 2).1 3).1
      3966129179050010267235698872222988781369656274480948822541994302823166087186280372018).isSome = true := by
  decide +kernel

theorem k4428_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4428) 2).1 3).2
      3948558214386167380075546943780289880838908112070517433839288197097045685642471692082).isSome = true := by
  decide +kernel

theorem k4428_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4428) 2).2 3).1
      3968641769687490303958035222804936540176320658175715419703417091977362579836616496946).isSome = true := by
  decide +kernel

theorem k4428_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4428) 2).2 3).2
      3949804515400736794013297838496506276553570410946909986533207730581854571424490215217).isSome = true := by
  decide +kernel

theorem k4429_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4429) 2).1 3).1
      15740493676554707854179468856625512093081726721850139273147677692451501091811120833734).isSome = true := by
  decide +kernel

theorem k4429_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4429) 2).1 3).2
      980996406032878950717796595987054866944805828984619341050179617424346095636776967345).isSome = true := by
  decide +kernel

theorem k4429_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4429) 2).2 3).1
      3936459609190385362206086435707581487234754543688695714832014090799596479248221017905).isSome = true := by
  decide +kernel

theorem k4429_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4429) 2).2 3).2
      981741986320363094514177535165860714953352759367612550545640769545768958905544440892).isSome = true := by
  decide +kernel

theorem k4430_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4430) 2).1
      1608806665890588752686095436252126908888228795160193584682982405301440171624526687533653295093747287580383787569237254648479677943934770005077669323).isSome = true := by
  decide +kernel

theorem k4430_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4430) 2).2 3).1
      53097264585709359468444616816898835648430883558933228443189745457).isSome = true := by
  decide +kernel

theorem k4430_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4430) 2).2 3).2
      978102749510339997634895767149116015999561155066636049015891052875279465231651658929).isSome = true := by
  decide +kernel

theorem k4431_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4431) 2).1
      339940523109392556550866018927642692090506798902910878561675241798637868575192900814465239540198797481905597696140260069176563).isSome = true := by
  decide +kernel

theorem k4431_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4431) 2).2
      340070265877904665891958744095645878332813749457778221034098911594642109775360147895199113330447331596268415169102869404415219).isSome = true := by
  decide +kernel

theorem k4432_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4432) 2).1
      287522283596264985093422057235476031644582295802779549549785060041780953634092558722721991603381739025649).isSome = true := by
  decide +kernel

theorem k4432_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4432) 2).2
      339567227399506818020142599931073304917034847222575641548314045068125418913392256870007896854832280627917525136745733119374579).isSome = true := by
  decide +kernel

theorem k4433_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4433) 2).1
      15209792610444755447317349084058796668627698973048010491873954189895964501691670899).isSome = true := by
  decide +kernel

theorem k4433_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4433) 2).2
      5301801143158711613424392808014829453213353261480220833193946532546341686732835475886501447539070888637405771199936745428796).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4434 4435 [
    1845831680173021559237138148999226458212857273231608325923931417926345189575878131156149909294008091440537783448566474522481218680790858523956494482569686172465415630] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4435 4436 [
    115325503084110074942972589788583454738681065552435994480147254094768756626159499716452639035936343199988896631964280156014953907008378606065334766009940085418587634] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4436 4437 [
    1562381246962849846410947325042006493376442069852921181298451955093461266201941920488833365005678378284342241898019614697868522822970277590341062] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4437 4454 [
    15187629295004071827540906999222959795135627545887603801506276015407998955578933618,
    51447971533186539248533217136967299874319597158763790044584305, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4454 4455 [
    5638703784620888813503270626858086996414364375322080989916567426948986588184953833972266618300439072847004804009459949369674503] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4428 4455 :=
  (Cover.one (box := dirCellBox) (n := 4428)
      (.split 2 (.split 3 (.leaf _ k4428_0) (.leaf _ k4428_1)) (.split 3 (.leaf _ k4428_2) (.leaf _ k4428_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4429)
      (.split 2 (.split 3 (.leaf _ k4429_0) (.leaf _ k4429_1)) (.split 3 (.leaf _ k4429_2) (.leaf _ k4429_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4430)
      (.split 2 (.leaf _ k4430_0) (.split 3 (.leaf _ k4430_1) (.leaf _ k4430_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4431)
      (.split 2 (.leaf _ k4431_0) (.leaf _ k4431_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4432)
      (.split 2 (.leaf _ k4432_0) (.leaf _ k4432_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4433)
      (.split 2 (.leaf _ k4433_0) (.leaf _ k4433_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10)

end C4.Cert.Dir147
