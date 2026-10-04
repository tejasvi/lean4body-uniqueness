module

public import C4Check

public section

/-! Cells `2082 ≤ n < 2108` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir028

theorem k2082_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2082) 3).1 2).1
      3988970473205952758615719848455178135173360975353114365449043775832021603954414615638833).isSome = true := by
  decide +kernel

theorem k2082_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2082) 3).1 2).2
      4705314511565768783543234857333925766916361709991242012989413790272800346896835540346509877853391834870297393).isSome = true := by
  decide +kernel

theorem k2082_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2082) 3).2 2).1
      995910466905108186606334445512828292428795680017651004694071853035917410179374150153009).isSome = true := by
  decide +kernel

theorem k2082_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2082) 3).2 2).2
      3988044143904583487288431236570422737062141836087544632297261716392061971237359707337521).isSome = true := by
  decide +kernel

theorem k2083_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2083) 3).1 2).1
      995611218924542950096474966679208601238313608426532219393624209934394766502900633269041).isSome = true := by
  decide +kernel

theorem k2083_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2083) 3).1 2).2
      15557853388487325795185554309458787089229351761355200485045687671124511722575580558028).isSome = true := by
  decide +kernel

theorem k2083_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2083) 3).2 1).1
      3891725135711492263002060377518964259332102065757338240514500925942070613638370409676).isSome = true := by
  decide +kernel

theorem k2083_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2083) 3).2 1).2
      15553182161916475079201114599008985169477361844827255826653406750580757704912607329484).isSome = true := by
  decide +kernel

theorem k2084_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2084) 3).1
      75268989173438936061979713864549237425655643666262393125727068009630400076785355511775060157286872106502999238).isSome = true := by
  decide +kernel

theorem k2084_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2084) 3).2
      63708420526611023968139352448036083261118531310054560708257715314035631131028407197533385).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2085 2086 [
    102296995877063602037370821140012517398134221787375818447038420963428997042819521331179772972455218813732870109260814053796317592708347806175085934875] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2086 2104 [
    2360708497047730290497, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    374496548106133431574416133756643087289045055788822823666730123441412658340587824089131601329619211404082592496660755145042629571789199] = true := by
  decide +kernel

theorem k2104_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2104) 3).1 3).1
      21725382730153796762446915776323354215600719257756514098911063133883185312931095912939658545249742794407614204991539274052166).isSome = true := by
  decide +kernel

theorem k2104_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2104) 3).1 3).2
      21663194918085981745020964149374552629173015030844895002836628908717352963074874010048157992966534477697702852564415955636550).isSome = true := by
  decide +kernel

theorem k2104_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2104) 3).2 2).1 1).1
      15485483277768312322106281557100942017723377087422101493660403312778187917180519794).isSome = true := by
  decide +kernel

theorem k2104_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2104) 3).2 2).1 1).2
      1168659741027577307747603818735386514551770672500634428807295688451298222469626211634257943961389663049203).isSome = true := by
  decide +kernel

theorem k2104_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2104) 3).2 2).2
      7521980702506652015183147716870105653513919301560738477362598765963206258061854203308337207532310284974355669420674159815992506475858321222284470574978047522369330765).isSome = true := by
  decide +kernel

theorem k2105_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).1 3).1 2).1
      3952019091575977502571546616287875310002721467018616439672122378297874796615025067441).isSome = true := by
  decide +kernel

theorem k2105_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).1 3).1 2).2
      3952755619727069310598438525741020061102054454342853096612347012549138168161040495985).isSome = true := by
  decide +kernel

theorem k2105_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).1 3).2 2).1
      15781825706235943323226969625317373785220152283625578085763625452576957951409676065201).isSome = true := by
  decide +kernel

theorem k2105_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).1 3).2 2).2
      3946174263333986508401088783687904890931756839464954847139793085432492177868873921969).isSome = true := by
  decide +kernel

theorem k2105_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).2 2).1 1).1
      63032030888671364031272966220551245315844651843567314549134011291539604661669703142204).isSome = true := by
  decide +kernel

theorem k2105_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).2 2).1 1).2
      873317649255790529847853065731430063665079494581688227703461813460403).isSome = true := by
  decide +kernel

theorem k2105_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).2 2).2 1).1
      72640854158112213577792900998632883366230974010997333166567211458889102227832354304100075064414784968508).isSome = true := by
  decide +kernel

theorem k2105_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2105) 3).2 2).2 1).2
      853839579299507457813095016667271861286905895032534360383016129340).isSome = true := by
  decide +kernel

theorem k2106_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).1 2).1 1).1
      251313668631140816346048174628999363627395641264345038341208239498008566561278089218620).isSome = true := by
  decide +kernel

theorem k2106_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).1 2).1 1).2
      4636295331099186717653749179456701536684396484558895149811498611330410179506664088889352296302039367414332).isSome = true := by
  decide +kernel

theorem k2106_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).1 2).2 1).1
      982022697554449682767572216068097849382664733403825779817206542629946069909659579964).isSome = true := by
  decide +kernel

theorem k2106_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).1 2).2 1).2
      213074169571306931111081884138533031711694203271911820430918797884).isSome = true := by
  decide +kernel

theorem k2106_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).2 2).1 1).1
      250817929812106083958860852824216432994384398201241779958928268713107869091241264004156).isSome = true := by
  decide +kernel

theorem k2106_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).2 2).1 1).2
      62708315286973092866821034194222003621534077277074411061971020244273398302613457189948).isSome = true := by
  decide +kernel

theorem k2106_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).2 2).2 1).1
      53177274755734291051196562481534930203503429066700442101497590332).isSome = true := by
  decide +kernel

theorem k2106_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2106) 3).2 2).2 1).2
      15680655646621691763645892563502726003818056724706856477432848833153684696823590927420).isSome = true := by
  decide +kernel

theorem k2107_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).1 2).1 1).1
      1001625574906655928712587478519138639577567237551146979345384667714002461548861602970684).isSome = true := by
  decide +kernel

theorem k2107_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).1 2).1 1).2
      13575552046833716921712055391478813162459948083586474316234336189500).isSome = true := by
  decide +kernel

theorem k2107_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).1 2).2 1).1
      13577020901198322805042144714212168412029815521612539002087953710140).isSome = true := by
  decide +kernel

theorem k2107_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).1 2).2 1).2
      3394550627276563732846240699878747888609897443018850653222421183548).isSome = true := by
  decide +kernel

theorem k2107_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).2 2).1 1).1
      15628967288267094168798231045845728111166907658053348200187233016581496308889028611788).isSome = true := by
  decide +kernel

theorem k2107_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).2 2).1 1).2
      847307046600849595318210143233041138615730207983053827363154382540).isSome = true := by
  decide +kernel

theorem k2107_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).2 2).2 1).1
      211849821564302818249484148664400271582511127850098959965440519884).isSome = true := by
  decide +kernel

theorem k2107_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2107) 3).2 2).2 1).2
      45941710332044131451392723645145424996966411980).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2082 2108 :=
  (Cover.one (box := dirCellBox) (n := 2082)
      (.split 3 (.split 2 (.leaf _ k2082_0) (.leaf _ k2082_1)) (.split 2 (.leaf _ k2082_2) (.leaf _ k2082_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2083)
      (.split 3 (.split 2 (.leaf _ k2083_0) (.leaf _ k2083_1)) (.split 1 (.leaf _ k2083_2) (.leaf _ k2083_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2084)
      (.split 3 (.leaf _ k2084_0) (.leaf _ k2084_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 2104)
      (.split 3 (.split 3 (.leaf _ k2104_0) (.leaf _ k2104_1)) (.split 2 (.split 1 (.leaf _ k2104_2) (.leaf _ k2104_3)) (.leaf _ k2104_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2105)
      (.split 3 (.split 3 (.split 2 (.leaf _ k2105_0) (.leaf _ k2105_1)) (.split 2 (.leaf _ k2105_2) (.leaf _ k2105_3))) (.split 2 (.split 1 (.leaf _ k2105_4) (.leaf _ k2105_5)) (.split 1 (.leaf _ k2105_6) (.leaf _ k2105_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2106)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2106_0) (.leaf _ k2106_1)) (.split 1 (.leaf _ k2106_2) (.leaf _ k2106_3))) (.split 2 (.split 1 (.leaf _ k2106_4) (.leaf _ k2106_5)) (.split 1 (.leaf _ k2106_6) (.leaf _ k2106_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2107)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2107_0) (.leaf _ k2107_1)) (.split 1 (.leaf _ k2107_2) (.leaf _ k2107_3))) (.split 2 (.split 1 (.leaf _ k2107_4) (.leaf _ k2107_5)) (.split 1 (.leaf _ k2107_6) (.leaf _ k2107_7)))))

end C4.Cert.Dir028
