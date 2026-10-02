module

public import C4Check

public section

/-! Cells `2383 ≤ n < 2384` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir040

theorem k2383_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 2).1
      73955100481404566804051743456835040125810302166318059331225247961169161403917057821092300036525746464113).isSome = true := by
  decide +kernel

theorem k2383_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 2).2
      74104026136756373123918052841050295248591734236733792339824640979761171083849908186165661550740885839217).isSome = true := by
  decide +kernel

theorem k2383_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).1
      18395473612955411740106375441885880153262559174300844721974904293887635852567047104177244472527843251569).isSome = true := by
  decide +kernel

theorem k2383_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).2
      18428420662328603508031529050738858978182859811802727238951899716098191013787062210263987232589089587569).isSome = true := by
  decide +kernel

theorem k2383_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).1
      30592788848327607592885571046714531095252250061858552467490384033833267244741106074197705425744741977115312073014797212280823427698114634605204212566378843165883786694).isSome = true := by
  decide +kernel

theorem k2383_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 2).1
      18459019452604849626061966314566602163251050999236063327702542446776066969116587847176690194857448246641).isSome = true := by
  decide +kernel

theorem k2383_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 2).2
      250541996692844621699046265749340099206293376584713938827813930906150556436478921073).isSome = true := by
  decide +kernel

theorem k2383_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).1
      3969836892380190354119600881594619775898476465758731920989009552672937277338719840625).isSome = true := by
  decide +kernel

theorem k2383_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).2
      18349865325249399669988788069119100986869696761071584803145905956599106439190275440107584822566676454769).isSome = true := by
  decide +kernel

theorem k2383_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).1
      4675737429583394118354643715596492194256275857434243158884700001169290376335805859778519374873316954723132).isSome = true := by
  decide +kernel

theorem k2383_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).2
      990613268323120986380493636952373850157481918933245822531288923548960362111243509105).isSome = true := by
  decide +kernel

theorem k2383_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).1
      18376518555317170040993400536990619019752371377475881028143483407936027655690025038678221999115471656305).isSome = true := by
  decide +kernel

theorem k2383_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).2
      18400831995144217088541951199883111578327957622465359479161724213789484264854331113625128138526036718961).isSome = true := by
  decide +kernel

theorem k2383_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 1).1
      15537005131777294557059602631334150423038383148459055465262339333928801902993625458).isSome = true := by
  decide +kernel

theorem k2383_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 1).2
      15889672757396073425975736852146830534529463462727786959848272026716740030923510633276).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2383 2384 :=
  (Cover.one (box := dirCellBox) (n := 2383)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2383_0) (.leaf _ k2383_1)) (.split 2 (.leaf _ k2383_2) (.leaf _ k2383_3))) (.split 3 (.leaf _ k2383_4) (.split 2 (.leaf _ k2383_5) (.leaf _ k2383_6)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2383_7) (.leaf _ k2383_8)) (.split 2 (.leaf _ k2383_9) (.leaf _ k2383_10))) (.split 3 (.split 2 (.leaf _ k2383_11) (.leaf _ k2383_12)) (.split 1 (.leaf _ k2383_13) (.leaf _ k2383_14))))))

end C4.Cert.Dir040
