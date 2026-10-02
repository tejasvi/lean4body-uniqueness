module

public import C4Check

public section

/-! Cells `2837 ≤ n < 2860` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir072

theorem k2837_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2837) 3).1 1).1
      15581463279678176093336703686014560749505467090062906393971103963613532426225466891442).isSome = true := by
  decide +kernel

theorem k2837_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2837) 3).1 1).2
      973781970864611636523712933589849226138676249146285366903720833825201397602715532348).isSome = true := by
  decide +kernel

theorem k2837_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2837) 3).2
      1389329320526152867446070648249482522679567640352525661236248896186118994432693891608714125443028014750253126963713110592920602866).isSome = true := by
  decide +kernel

theorem k2838_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2838) 2).1
      73494403818374580975615602249377434675997480388432164666638783492795225365070137935308835874817030148814023).isSome = true := by
  decide +kernel

theorem k2838_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2838) 2).2
      15936521366569642494541099566287043474920717826599324430171308252021415817436395433478387).isSome = true := by
  decide +kernel

theorem k2839_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2839) 2).1
      17934796486359311304919336149729582418718340265382635830827842851279479299947721622613069060494861884851).isSome = true := by
  decide +kernel

theorem k2839_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2839) 2).2
      3982202747954077334617092425674993985936504629500048422385399990439203657752643973269747).isSome = true := by
  decide +kernel

theorem k2840_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2840) 2).1
      15186921382965093758784581082771441908750432973505981257405201787826438064989931889).isSome = true := by
  decide +kernel

theorem k2840_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2840) 2).2
      15552646898502914746424026269105266849061285736250570078345194598329235846755925472461).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 2841 2842 [
    286799996242316161820502833122031767569861200271220386749591444655562895549406591304443693700041360867654] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2842 2858 [
    60719346605385249671757566277667682181003140729791436474288075322186373276905007474,
    696896551440121954662563766053565879387586, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2858 2859 [
    26814645027097258343849116963364006235521504355815901338523547991621578725184177098642546870219899767637235679304745302078148936080966216721357413127] = true := by
  decide +kernel

theorem k2859_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2859) 3).1 2).1
      1910822317408658914763574380630594618762316088173873601993914255248620622530705800662175354659653398638689787738799109263665485995658170940685034769965650156450280903).isSome = true := by
  decide +kernel

theorem k2859_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2859) 3).1 2).2
      21937174886741459896846157955563417056015380442624507324220769800657082203055278676973240674108066133868273177810567393101257).isSome = true := by
  decide +kernel

theorem k2859_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 1).1
      15992271785540636349209246066974709574010131677301093286253882243249748399007545149043).isSome = true := by
  decide +kernel

theorem k2859_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 1).2
      73862546161041539378078329335027206411526228310299947149800983534692685743147647040149656395675535398716).isSome = true := by
  decide +kernel

theorem k2859_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2859) 3).2 2).2
      6435822192955817776791396432068009926365342807140560010174004227444642948640015790523663466743367965813698425411690973974878276847639736229131761).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2837 2860 :=
  (Cover.one (box := dirCellBox) (n := 2837)
      (.split 3 (.split 1 (.leaf _ k2837_0) (.leaf _ k2837_1)) (.leaf _ k2837_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2838)
      (.split 2 (.leaf _ k2838_0) (.leaf _ k2838_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2839)
      (.split 2 (.leaf _ k2839_0) (.leaf _ k2839_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2840)
      (.split 2 (.leaf _ k2840_0) (.leaf _ k2840_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2859)
      (.split 3 (.split 2 (.leaf _ k2859_0) (.leaf _ k2859_1)) (.split 2 (.split 1 (.leaf _ k2859_2) (.leaf _ k2859_3)) (.leaf _ k2859_4))))

end C4.Cert.Dir072
