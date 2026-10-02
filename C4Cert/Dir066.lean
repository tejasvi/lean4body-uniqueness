module

public import C4Check

public section

/-! Cells `2780 ≤ n < 2803` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir066

theorem k2780_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2780) 2).1
      71836697457855628738139688061620478308495327761400253938672121050657848764994978669073776544139346044359).isSome = true := by
  decide +kernel

theorem k2780_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2780) 2).2
      1847089840542270955288530615290015739140522712036550006194534671211422320200579076277127789175603757640543434408555129665431024596466571070541392404249263102667785671).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 2781 2801 [
    249074625253372990521393300571412468575042241520463319981809402372989299244137329269766,
    9456413304195345984786, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c2 : allCells dirCell 2801 2802 [
    4395542120730095365910028565605925066772940296105050362649058075639298052452349364771662125172801475179707951310346900011324645902259] = true := by
  decide +kernel

theorem k2802_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).1 2).1
      6726384747413230758614480337191638272384612012526490891386920714477105949455222700310360386303260844800523085776422706900687887004450873429919174).isSome = true := by
  decide +kernel

theorem k2802_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).1 2).2
      261676582653547899370779699720189985318477252185306331687748842328697129252423666245).isSome = true := by
  decide +kernel

theorem k2802_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).1
      1961416805489139319832352066241636390760788694057647995297535884637799367889979729464269122671408685975172430843591873130905056561172454405537683112334499567178061254).isSome = true := by
  decide +kernel

theorem k2802_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).2
      22539984810369126705820208290749179426821830680896280368089008026130373112770157244786507688495445763179735759290136356120006).isSome = true := by
  decide +kernel

theorem k2802_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 2).1
      1207513649056821292497219995122485965585408298398585875157082925870384632184496355142945910194014224147953).isSome = true := by
  decide +kernel

theorem k2802_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 2).2
      15997577022241401119191793284619710972830496445888452413782021681802764044045921649).isSome = true := by
  decide +kernel

theorem k2802_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 2).1
      1197746060688558812287798517220989618085583252765749283675613109400745790071260739768007657861697089398257).isSome = true := by
  decide +kernel

theorem k2802_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 2).2
      1199060891004978036999434451657377319600781553882952159544946749326404844115802713637446960894341268661745).isSome = true := by
  decide +kernel

theorem k2802_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).1
      486406964813466581838583315102450814217359002491523356898730028543423510571975392914820358670220436760877550395039994358327715039318849064041522867250938989476881862).isSome = true := by
  decide +kernel

theorem k2802_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).2
      482648112031893342101840956496138257319179835107796125814001415940207130618896669780879579042601333016531434867796459139566303961106026338402189171913972248356087238).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2780 2803 :=
  (Cover.one (box := dirCellBox) (n := 2780)
      (.split 2 (.leaf _ k2780_0) (.leaf _ k2780_1))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 2802)
      (.split 3 (.split 3 (.split 2 (.leaf _ k2802_0) (.leaf _ k2802_1)) (.split 2 (.leaf _ k2802_2) (.leaf _ k2802_3))) (.split 2 (.split 3 (.split 2 (.leaf _ k2802_4) (.leaf _ k2802_5)) (.split 2 (.leaf _ k2802_6) (.leaf _ k2802_7))) (.split 3 (.leaf _ k2802_8) (.leaf _ k2802_9)))))

end C4.Cert.Dir066
