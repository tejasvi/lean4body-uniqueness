module

public import C4Check

public section

/-! Cells `4455 ≤ n < 4463` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir148

theorem k4455_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).1 2).1
      4018842065804502582923524586431932411525877611129375558791390359418205038388601476913).isSome = true := by
  decide +kernel

theorem k4455_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).1 2).2
      250728432699725383825155527093991945400544604242032793197302884858143031534172068211).isSome = true := by
  decide +kernel

theorem k4455_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).2 2).1
      55396984796263234230618304918922516758660434170924119105345384991538).isSome = true := by
  decide +kernel

theorem k4455_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).2 2).2
      3990936320655280595691757708545149534504483326800459800800765870694609615674167858993).isSome = true := by
  decide +kernel

theorem k4456_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4456) 2).1 3).1
      254015104905055681669364259428121319534609715731104638506067191100756785301812657113905).isSome = true := by
  decide +kernel

theorem k4456_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4456) 2).1 3).2
      3953394880712238582991912363126847057625151485186795650864717930584130023039220029234).isSome = true := by
  decide +kernel

theorem k4456_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4456) 2).2
      5011478555577729721892265080042633317351814261902136275014781545100110675035626464070631093372806823303730041007303).isSome = true := by
  decide +kernel

theorem k4457_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4457) 2).1
      350468850102004319008915337656003917735723985397911029193276996323330235938106064155707346450545479596047568241477436510102310707).isSome = true := by
  decide +kernel

theorem k4457_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4457) 2).2
      87658513715975769857707605932742529165539918607159137213779033447951798345006476159596936698929841768602835401751053709304352563).isSome = true := by
  decide +kernel

theorem k4458_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4458) 2).1 3).1
      980227505852566416113640478098474482488946979883987527513191786635619322158552808508).isSome = true := by
  decide +kernel

theorem k4458_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4458) 2).1 3).2
      978574621271420611928092393284868408982963899118702163264347457460236538753048214588).isSome = true := by
  decide +kernel

theorem k4458_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4458) 2).2
      5588546826221570585288824725200291474889395085464782855289239350671613940912446625937329168092657062367274028469632248758958247731).isSome = true := by
  decide +kernel

theorem k4459_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4459) 2).1
      4720478626794141618719081124588496971654686280749060039445860207168206850865086106919485432639192387590932723).isSome = true := by
  decide +kernel

theorem k4459_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4459) 2).2
      87106606544456685976597671954476683831217977993539983312656023445322322063487880319530489019781608040737858370920864636112072947).isSome = true := by
  decide +kernel

theorem k4460_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4460) 2).1
      339658096306290511289842808187288378797767391851476380945039554956664529897516164038090091796724997233649154045704234974672115).isSome = true := by
  decide +kernel

theorem k4460_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4460) 2).2
      3993167184262129137669757289711551765347257471589579855959373871113297631362840031228147).isSome = true := by
  decide +kernel

theorem k4461_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4461) 2).1
      5302907002328705709899217697270123628768952079068903623529013357458801055805377858950608640152833302529777614584213608585020).isSome = true := by
  decide +kernel

theorem k4461_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4461) 2).2
      287515254063147866170012701280617450505027598031325905152107463924659801701074120674055312347472319730492).isSome = true := by
  decide +kernel

theorem k4462_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4462) 2).1
      5298711075300788423888604031100358589961724913813136180421189954540284261734675380606206184765875673611819981778486769997628).isSome = true := by
  decide +kernel

theorem k4462_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4462) 2).2
      1149095417681111846324391185219129906865717248172821095797606938911594467748391253267051316345448305740604).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4455 4463 :=
  (Cover.one (box := dirCellBox) (n := 4455)
      (.split 3 (.split 2 (.leaf _ k4455_0) (.leaf _ k4455_1)) (.split 2 (.leaf _ k4455_2) (.leaf _ k4455_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4456)
      (.split 2 (.split 3 (.leaf _ k4456_0) (.leaf _ k4456_1)) (.leaf _ k4456_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4457)
      (.split 2 (.leaf _ k4457_0) (.leaf _ k4457_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4458)
      (.split 2 (.split 3 (.leaf _ k4458_0) (.leaf _ k4458_1)) (.leaf _ k4458_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4459)
      (.split 2 (.leaf _ k4459_0) (.leaf _ k4459_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4460)
      (.split 2 (.leaf _ k4460_0) (.leaf _ k4460_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4461)
      (.split 2 (.leaf _ k4461_0) (.leaf _ k4461_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4462)
      (.split 2 (.leaf _ k4462_0) (.leaf _ k4462_1)))

end C4.Cert.Dir148
