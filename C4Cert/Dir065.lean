module

public import C4Check

public section

/-! Cells `2804 ≤ n < 2805` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir065

theorem k2804_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).1 1).1
      253684814222419101461676799917957168258998404822158226623997215994313758552245562503740).isSome = true := by
  decide +kernel

theorem k2804_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).1 1).2
      54972201068714577837845071099795791187284425776003644276956130439740).isSome = true := by
  decide +kernel

theorem k2804_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).2 1).1
      3441183633490896761750939595057223365955289544448049022190008922684).isSome = true := by
  decide +kernel

theorem k2804_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).2 1).2
      3439714645742313962152295425623184485487832090036258734712460669500).isSome = true := by
  decide +kernel

theorem k2804_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).2 2).1 1).1
      11684484861401053789167172382935410697488026172).isSome = true := by
  decide +kernel

theorem k2804_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).2 2).1 1).2
      860674883290408468825207292049102342148567823813662808946425459260).isSome = true := by
  decide +kernel

theorem k2804_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).2 2).2
      1201629502464966088795437908594182016458480213705089228783229740708037015432166214631284218061781995357595313).isSome = true := by
  decide +kernel

theorem k2804_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).1 2).1 1).1
      15810412601914979424136211394480180993486479561794122380454832970280147131620761910332).isSome = true := by
  decide +kernel

theorem k2804_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).1 2).1 1).2
      3426964722235386873551025977806946940099224200060861885803086593084).isSome = true := by
  decide +kernel

theorem k2804_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).1 2).2 1).1
      857836968324603843935890077692564266033277915053146013081909705788).isSome = true := by
  decide +kernel

theorem k2804_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).1 2).2 1).2
      857490405614652859375552141483757989490103279063180462538681596988).isSome = true := by
  decide +kernel

theorem k2804_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).2 2).1 1).1
      858636430987067250149778683800634917384263383964729862314478006844).isSome = true := by
  decide +kernel

theorem k2804_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).2 2).1 1).2
      3433268103061734369679839772512408658639896168721835302871237128764).isSome = true := by
  decide +kernel

theorem k2804_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).2 2).2
      19614789714246906291350841018607787902836510110051570221217520885237624481137900564574534424106606553306683132145).isSome = true := by
  decide +kernel

theorem k2804_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).1 2).1 1).1
      3420111002794434914149763667903921260173002597928100029330269322300).isSome = true := by
  decide +kernel

theorem k2804_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).1 2).1 1).2
      15769157081857207746835114135571648901907157345435283149837241215452100408360841362492).isSome = true := by
  decide +kernel

theorem k2804_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).1 2).2 1).1
      15787570933332983240522782347368970346330275722861625700476132718452981852449076526140).isSome = true := by
  decide +kernel

theorem k2804_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).1 2).2 1).2
      3422181693117644777965463846617659459705187133600615256802318990396).isSome = true := by
  decide +kernel

theorem k2804_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).2 2).1 1).1
      3334229969130051018092218859761929607258530116818282020890631884).isSome = true := by
  decide +kernel

theorem k2804_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).2 2).1 1).2
      15739034319849142980280047987251890987134366431123317741621312395984556009225556180028).isSome = true := by
  decide +kernel

theorem k2804_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).2 2).2 1).1
      53440409658850540486785334945843346503108318836094504861849480252).isSome = true := by
  decide +kernel

theorem k2804_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).2 2).2 1).2
      740483911630751704613004283860065942422531783740).isSome = true := by
  decide +kernel

theorem k2804_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).1 2).1
      19551345629585311092291731873034016084918166987162996176382824763476921040538960182896276600149833132397173338353).isSome = true := by
  decide +kernel

theorem k2804_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).1 2).2
      1060625146265145439479758432502378990726849563172778064695036924049653689201228094352054012145).isSome = true := by
  decide +kernel

theorem k2804_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).2 1).1 2).1
      11858655234714665800268076382622707714962825059121).isSome = true := by
  decide +kernel

theorem k2804_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).2 1).1 2).2
      2897750050820752040544675948096039799205772348).isSome = true := by
  decide +kernel

theorem k2804_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).2 1).2 2).1
      3417917963918497392579733954095843137086671718003906927145361718332).isSome = true := by
  decide +kernel

theorem k2804_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).2 1).2 2).2
      855004192344890597667821425399158879722771601130605419910091619388).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2804 2805 :=
  (Cover.one (box := dirCellBox) (n := 2804)
      (.split 3 (.split 3 (.split 2 (.split 2 (.split 1 (.leaf _ k2804_0) (.leaf _ k2804_1)) (.split 1 (.leaf _ k2804_2) (.leaf _ k2804_3))) (.split 2 (.split 1 (.leaf _ k2804_4) (.leaf _ k2804_5)) (.leaf _ k2804_6))) (.split 2 (.split 2 (.split 1 (.leaf _ k2804_7) (.leaf _ k2804_8)) (.split 1 (.leaf _ k2804_9) (.leaf _ k2804_10))) (.split 2 (.split 1 (.leaf _ k2804_11) (.leaf _ k2804_12)) (.leaf _ k2804_13)))) (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2804_14) (.leaf _ k2804_15)) (.split 1 (.leaf _ k2804_16) (.leaf _ k2804_17))) (.split 2 (.split 1 (.leaf _ k2804_18) (.leaf _ k2804_19)) (.split 1 (.leaf _ k2804_20) (.leaf _ k2804_21)))) (.split 3 (.split 2 (.leaf _ k2804_22) (.leaf _ k2804_23)) (.split 1 (.split 2 (.leaf _ k2804_24) (.leaf _ k2804_25)) (.split 2 (.leaf _ k2804_26) (.leaf _ k2804_27)))))))

end C4.Cert.Dir065
