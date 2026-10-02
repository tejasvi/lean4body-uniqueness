module

public import C4Check

public section

/-! Cells `1630 ≤ n < 1657` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir014

theorem k1630_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1630) 3).1 2).1
      100657497847869663661501700569789837792465280772074936502455608301345892455144512255370470474560295027041644561876877501856618011958498901691823345).isSome = true := by
  decide +kernel

theorem k1630_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1630) 3).1 2).2
      87308798162115016768368072927244110333850077149515499042351042594652006487450233169295413622885690408728190757107869756863116531).isSome = true := by
  decide +kernel

theorem k1630_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1630) 3).2 2).1
      1181198801361603734797494398843092199093912800483074908101246102205654135412121964279987476387559464336839885).isSome = true := by
  decide +kernel

theorem k1630_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1630) 3).2 2).2
      4617124785490824071668661816483460658150676705030090829707777276999871694535266097115152855333027528939313).isSome = true := by
  decide +kernel

theorem k1631_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1631) 3).1 2).1
      75457362134753210529455176790684495986751434533549953634561823523151123160431185532989397475431379009494440753).isSome = true := by
  decide +kernel

theorem k1631_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1631) 3).1 2).2
      1360947585322081136539978700591358816558734738202877962605368179297840979787102873367735323655508856915280737193116103162558257).isSome = true := by
  decide +kernel

theorem k1631_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1631) 3).2 2).1
      3992783534480038557523535318264389286159004321173871481894997337357567508296234544493361).isSome = true := by
  decide +kernel

theorem k1631_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1631) 3).2 2).2
      4606032527916069735512701419543432216131598270190032686185847136036876240834618878526839035502734828450764).isSome = true := by
  decide +kernel

theorem k1632_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1632) 3).1 2).1
      3989726486226224744437503285958659700430766144424445585179560466933019151251627204768561).isSome = true := by
  decide +kernel

theorem k1632_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1632) 3).1 2).2
      997776449936441005290241956865517913772344444347727052548076201122329416073925610533681).isSome = true := by
  decide +kernel

theorem k1632_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1632) 3).2 2).1
      211158406751496049025920319974189973144514289919893764757322388273).isSome = true := by
  decide +kernel

theorem k1632_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1632) 3).2 2).2
      997090670824731976129691088188925952517931315048113454625046360863461152775847876326193).isSome = true := by
  decide +kernel

theorem k1633_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1633) 2).1
      86768634215624603867930186196150527834046685248934504509067747942267680899174995868223154569624401628397063169121054244826730291).isSome = true := by
  decide +kernel

theorem k1633_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1633) 2).2
      75278470432657465546093645222716711282707296470415928691778641198236170805436656355274320152943887446059076807).isSome = true := by
  decide +kernel

theorem k1634_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1634) 2).1
      73449640911891629574913907442559399266047328420899668933702213549056567566818863632659005905385766231432391).isSome = true := by
  decide +kernel

theorem k1634_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1634) 2).2
      300926394518095943464515084476354481630982734985643258699057026629878762246403871722649562990412660594611866829).isSome = true := by
  decide +kernel

theorem k1635_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1635) 2).1
      3886768675220011162584216114036186744839237880132930578060046103818596889725499594547).isSome = true := by
  decide +kernel

theorem k1635_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1635) 2).2
      3886928238531939322480762960117067849201755853806910587596541064566988863485961869107).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 1636 1637 [
    117941164166867829756258890565233820100788754634671088103940426708627202549265831553948033129712411206575839468887519896922191620417860786073739199520108608660364426550] = true := by
  decide +kernel

theorem c7 : allCells dirCell 1637 1657 [
    174166142418807313219157928015002821535186, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 63333360405721731134998599186941983730798960861724023033553837913996237005082293530723] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1630 1657 :=
  (Cover.one (box := dirCellBox) (n := 1630)
      (.split 3 (.split 2 (.leaf _ k1630_0) (.leaf _ k1630_1)) (.split 2 (.leaf _ k1630_2) (.leaf _ k1630_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1631)
      (.split 3 (.split 2 (.leaf _ k1631_0) (.leaf _ k1631_1)) (.split 2 (.leaf _ k1631_2) (.leaf _ k1631_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1632)
      (.split 3 (.split 2 (.leaf _ k1632_0) (.leaf _ k1632_1)) (.split 2 (.leaf _ k1632_2) (.leaf _ k1632_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1633)
      (.split 2 (.leaf _ k1633_0) (.leaf _ k1633_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1634)
      (.split 2 (.leaf _ k1634_0) (.leaf _ k1634_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1635)
      (.split 2 (.leaf _ k1635_0) (.leaf _ k1635_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7)

end C4.Cert.Dir014
