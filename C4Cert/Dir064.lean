module

public import C4Check

public section

/-! Cells `2776 ≤ n < 2777` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir064

theorem k2776_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).1
      252311774206556461680940947866982291589599317650255201910742907637081615643780441167665).isSome = true := by
  decide +kernel

theorem k2776_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).2
      3936646161070765408940641695260921010992569949965511672813575648663830684176846549564).isSome = true := by
  decide +kernel

theorem k2776_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 3).1
      63156770984947661956958690901557591694867466282348721865293256900639105693049886299953).isSome = true := by
  decide +kernel

theorem k2776_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 3).2
      3940970170590965479398312645022081629733052606245653991612811283537930223216928092732).isSome = true := by
  decide +kernel

theorem k2776_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).1 1).1
      3927204117689318131480376217590645202592312556800843577756117497886850214299283354172).isSome = true := by
  decide +kernel

theorem k2776_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).1 1).2
      15705738181490406683380793768206227235490271219527484857016551397624206438909439628092).isSome = true := by
  decide +kernel

theorem k2776_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).2 1).1
      3926987112463799569956767077696206206167052639438338935069633212036504219764880365363).isSome = true := by
  decide +kernel

theorem k2776_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).2 1).2
      982455754533833303799240744250725086698902158769087829109857486651975180587157026364).isSome = true := by
  decide +kernel

theorem k2776_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).1
      253083308129639648249480633159534072819631247272034269317977986461316391783982477853500).isSome = true := by
  decide +kernel

theorem k2776_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).2
      858368997812368872857066545842229458756153060571680166205839624764).isSome = true := by
  decide +kernel

theorem k2776_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).1
      3422020759205970224169399567190125292753093540893829818685404463932).isSome = true := by
  decide +kernel

theorem k2776_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).2
      856270325348874014798234058651233290498269845750467085951449940796).isSome = true := by
  decide +kernel

theorem k2776_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).1
      19498762792818382051735626164835226929603594894252998678801247333856064337367785782856891028099182025055573045489).isSome = true := by
  decide +kernel

theorem k2776_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).2
      19464300942418436647445792371455949269269008391442533626592436134740759032254595029694441102483487601464095994097).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2776 2777 :=
  (Cover.one (box := dirCellBox) (n := 2776)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2776_0) (.leaf _ k2776_1)) (.split 3 (.leaf _ k2776_2) (.leaf _ k2776_3))) (.split 2 (.split 1 (.leaf _ k2776_4) (.leaf _ k2776_5)) (.split 1 (.leaf _ k2776_6) (.leaf _ k2776_7)))) (.split 3 (.split 3 (.split 2 (.leaf _ k2776_8) (.leaf _ k2776_9)) (.split 2 (.leaf _ k2776_10) (.leaf _ k2776_11))) (.split 3 (.leaf _ k2776_12) (.leaf _ k2776_13)))))

end C4.Cert.Dir064
