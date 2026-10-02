module

public import C4Check

public section

/-! Cells `2583 ≤ n < 2614` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir054

theorem k2583_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2583) 2).1
      87297230812760533397344139277293598212154127787296084379716888884726320984157123646392418094169143876864468987189306737265984316).isSome = true := by
  decide +kernel

theorem k2583_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2583) 2).2
      64131160140583424089186999433659310859789418186599276031937732598912719632157696725074748).isSome = true := by
  decide +kernel

theorem k2584_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2584) 1).1
      1023838241381686977117004625273569242576791056840074789025273554493660444403370040690197308).isSome = true := by
  decide +kernel

theorem k2584_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2584) 1).2
      295134453003033703055067657162261394958446624707992618479475708112367738135877080459442899777525999268592700).isSome = true := by
  decide +kernel

theorem k2585_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2585) 1).1
      3992977954053286124965367886539274676628308996751421865291076711489422154994403090316348).isSome = true := by
  decide +kernel

theorem k2585_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2585) 1).2
      3993402935105531132306423622722699562269368960507095870125686323481427467538449049271356).isSome = true := by
  decide +kernel

theorem k2586_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2586) 3).1
      15957314498525363529787874650079850681598357331269501641484599822933576503533910894623804).isSome = true := by
  decide +kernel

theorem k2586_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2586) 3).2
      3377142862035061404882329310187327676914294916103024802108780823356).isSome = true := by
  decide +kernel

theorem k2587_0 : (checkBoxH dirMode depth (dirCellBox 2587)
      102454309882891968649571208052787402144050593162418693183099952655892166490146877104774065341246988693009981138590274185653694191391590560946110579516).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2588 2589 [
    995540919696688288956282001279697159715205254941235204637429861383995923607021388182332] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2589 2607 [
    71709633830769747146980978426740147563274433192796137544598007961784498220894677315538742410694654348657,
    43558831612209810726046096559808615913052, 147535623167559666820, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2607 2609 [
    0, 710341755251907135652033246522966011266499] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2609 2610 [
    6326973238705996795022275530470628896610022383359716676914853271134063115662012371164734880297079214995669071562903407474142627506403990455162439] = true := by
  decide +kernel

theorem k2610_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2610) 2).1
      289697736197205741043172704646710325661751791002811504938041945119031534294558533754641640884985459626812).isSome = true := by
  decide +kernel

theorem k2610_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2610) 2).2
      251016673964884693640378624381485716201350093483580125399670104186264736876541323678963).isSome = true := by
  decide +kernel

theorem k2611_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2611) 2).1
      15657592048032415689275541038463941951862829257174583313510967046500772909723334198076).isSome = true := by
  decide +kernel

theorem k2611_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2611) 2).2
      15657127519119169064282546309406361300616401385307134886677565322217476295271732724540).isSome = true := by
  decide +kernel

theorem k2612_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2612) 2).1
      15997983770528957725675532753177637362167474834965058399146623909305365668889937594596412).isSome = true := by
  decide +kernel

theorem k2612_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2612) 2).2
      211726944061417488334890220342036012165702340419529495048736783420).isSome = true := by
  decide +kernel

theorem k2613_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2613) 2).1
      255562329495427435758135273675621963537307636426901290396120531463578889265127392740885308).isSome = true := by
  decide +kernel

theorem k2613_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2613) 2).2
      733403349149794359331008303466148827438085030716).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2583 2614 :=
  (Cover.one (box := dirCellBox) (n := 2583)
      (.split 2 (.leaf _ k2583_0) (.leaf _ k2583_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2584)
      (.split 1 (.leaf _ k2584_0) (.leaf _ k2584_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2585)
      (.split 1 (.leaf _ k2585_0) (.leaf _ k2585_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2586)
      (.split 3 (.leaf _ k2586_0) (.leaf _ k2586_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2587)
      (.leaf _ k2587_0)).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 2610)
      (.split 2 (.leaf _ k2610_0) (.leaf _ k2610_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2611)
      (.split 2 (.leaf _ k2611_0) (.leaf _ k2611_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2612)
      (.split 2 (.leaf _ k2612_0) (.leaf _ k2612_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2613)
      (.split 2 (.leaf _ k2613_0) (.leaf _ k2613_1)))

end C4.Cert.Dir054
