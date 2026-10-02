module

public import C4Check

public section

/-! Cells `2830 ≤ n < 2833` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir070

theorem k2830_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2830) 3).1
      8042856051905816665486499815337757137317204388948618158981509461149578676661403106635261780302522693616279885115082052277824372263376588930096489827190974449651635096859).isSome = true := by
  decide +kernel

theorem k2830_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).1 3).1
      256449216518307385138838223107206351631675501144333106540126943724391675308096793417).isSome = true := by
  decide +kernel

theorem k2830_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).1 3).2
      1635612006664023658879752199905983159125911111284359476394441729739879808001612698325508887228257339011433274015829150734696321614032231868057033).isSome = true := by
  decide +kernel

theorem k2830_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2830) 3).2 2).2
      6545284718295376682405180794769043277666892421323256943807888791971639544334263718338564276458685245373620940292862053776185457476468925330848583).isSome = true := by
  decide +kernel

theorem k2831_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 2).1
      6481840442978247021783995728473037969843673010132373302020087503288379705465331017327722180433647146484806404474346202253590111820722612500264433).isSome = true := by
  decide +kernel

theorem k2831_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 2).2
      6484785692340760404440549766117510354879876624332314572713751942474192166085603530362048318808653452830399728843865219849083185422708229584549361).isSome = true := by
  decide +kernel

theorem k2831_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).2 3).1
      18671674041672998761521616247467749596832295990800197629729393049418160550567200489556952328997840842097).isSome = true := by
  decide +kernel

theorem k2831_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).2 3).2
      87734921374587726143597968120570399557645365830280426835984405740645025278514485381754166892055903465700190904701976934446332).isSome = true := by
  decide +kernel

theorem k2831_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 1).1
      1206592274840894241247791692908559434432154627713304655715526117228560777806295851761689791850997473878332147).isSome = true := by
  decide +kernel

theorem k2831_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 1).2
      89190483608306013804500195458432260796150955792436961332707552899054407576445748001294614148152527219602900666924945545060931826).isSome = true := by
  decide +kernel

theorem k2831_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 1).1
      18868878121288624579687400167202397515051896163228915244056431948430831107282476621470504180223132490561011).isSome = true := by
  decide +kernel

theorem k2831_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 1).2
      73825667276846021157575064652840981855876800887352237617171095934999714745132672261878829644557162370876).isSome = true := by
  decide +kernel

theorem k2832_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 1).1
      19211726876828583866258957038341978152500380935663577256780599779218012501211885325670703483680029495143108412).isSome = true := by
  decide +kernel

theorem k2832_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 1).2
      1200267256467111298115750205883422108568760461584305559891020024293678884284413194798666426539345959102264124).isSome = true := by
  decide +kernel

theorem k2832_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 1).1
      3977300873997207366736504867702115300948276764625785336625222561991023489021352859452).isSome = true := by
  decide +kernel

theorem k2832_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 1).2
      862056238776835741270356939960001096805512360507347857447228789564).isSome = true := by
  decide +kernel

theorem k2832_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 1).1
      1194748732116731885443787785627926962004695044257255559770847818602730951230421483385941759455390506556404540).isSome = true := by
  decide +kernel

theorem k2832_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 1).2
      64737323612932907436069132325293784640946065358738387284811416488945752184309683733701436).isSome = true := by
  decide +kernel

theorem k2832_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 2).1
      1195449780423861817258837487515592883707642254609491974543343720365111838172820214002219851952827964963238716).isSome = true := by
  decide +kernel

theorem k2832_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 2).2
      858126115563653833920581763358360668553239284832336503361720800060).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2830 2833 :=
  (Cover.one (box := dirCellBox) (n := 2830)
      (.split 3 (.leaf _ k2830_0) (.split 2 (.split 3 (.leaf _ k2830_1) (.leaf _ k2830_2)) (.leaf _ k2830_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2831)
      (.split 3 (.split 2 (.split 2 (.leaf _ k2831_0) (.leaf _ k2831_1)) (.split 3 (.leaf _ k2831_2) (.leaf _ k2831_3))) (.split 2 (.split 1 (.leaf _ k2831_4) (.leaf _ k2831_5)) (.split 1 (.leaf _ k2831_6) (.leaf _ k2831_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2832)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2832_0) (.leaf _ k2832_1)) (.split 1 (.leaf _ k2832_2) (.leaf _ k2832_3))) (.split 2 (.split 1 (.leaf _ k2832_4) (.leaf _ k2832_5)) (.split 2 (.leaf _ k2832_6) (.leaf _ k2832_7)))))

end C4.Cert.Dir070
