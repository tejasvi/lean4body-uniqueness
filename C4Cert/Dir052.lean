module

public import C4Check

public section

/-! Cells `2527 ≤ n < 2554` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir052

theorem k2527_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2527) 2).1 3).1
      849008892462331395675218808218854416822504258216404576698260505404).isSome = true := by
  decide +kernel

theorem k2527_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2527) 2).1 3).2
      212000369316532398211459052892551174822220245796068298393353288764).isSome = true := by
  decide +kernel

theorem k2527_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2527) 2).2 3).1
      849099450639974676926970334233234340956648278593890457038196556604).isSome = true := by
  decide +kernel

theorem k2527_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2527) 2).2 3).2
      212019931119500560340594187786390057553976062734331733242931936316).isSome = true := by
  decide +kernel

theorem k2528_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2528) 2).1
      22278228865034236529419561931787947390125435355807923465225681594338686289667767485951553600880411570785105291752932840760050774259).isSome = true := by
  decide +kernel

theorem k2528_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2528) 2).2
      19325131500250369807177636334882375812145920323002175789898084398136892664912212069522133007715432331730039795955).isSome = true := by
  decide +kernel

theorem k2529_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).1 2).1
      62395320556408198474619864206817252198573066170114192918997614411665320492791490231356).isSome = true := by
  decide +kernel

theorem k2529_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).1 2).2
      52855039836235464199331793446251374143055108820161912007695350844).isSome = true := by
  decide +kernel

theorem k2529_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2529) 3).2
      75374076107038788479846109408909190341687271546151206167992268644845149181286620646567814581993218691120184380).isSome = true := by
  decide +kernel

theorem k2530_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2530) 2).1
      73553189496832814963890959782915170070287249554167510815712497752028194405609722304166318601475551527124028).isSome = true := by
  decide +kernel

theorem k2530_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2530) 2).2
      73555406104581091731744049184287956166354122758176141168721894875635604881831029198353369000448502095100988).isSome = true := by
  decide +kernel

theorem k2531_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2531) 3).1
      73505723353697631774877321195521481932640565326358144323864890410890425530849230711241390272383224210734140).isSome = true := by
  decide +kernel

theorem k2531_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2531) 3).2
      52720775449895149099044187482623865291664465647560536929846770748).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2532 2533 [
    22199781766376151938521238869038426277682734620822112704419203436153638544027832403717815018728306672259448385834778414182013661425] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2533 2534 [
    3980232624301705406443394211355745933749550836372368402694817745744606495737429040154865] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2534 2552 [
    51429887702716181288618274541231463022622997107665814230459985, 147539677273001106788, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k2552_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2552) 3).1
      52687646590209184368418001954629696247657156947656940338361714).isSome = true := by
  decide +kernel

theorem k2552_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2552) 3).2
      1348695623710822517036159188807336620918550799700514737583675513744009478799873924976204169474103741420529948259732157724146).isSome = true := by
  decide +kernel

theorem k2553_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2553) 3).1
      88084692149640090782597974421296573363344777241322172503058648231609503345904958634755625951473284758342618561290993821879321586).isSome = true := by
  decide +kernel

theorem k2553_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2553) 3).2
      343140738922947340857906284885598104957547779363515081141331393587967624464819867798136469097625185393471424020018850886415602).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2527 2554 :=
  (Cover.one (box := dirCellBox) (n := 2527)
      (.split 2 (.split 3 (.leaf _ k2527_0) (.leaf _ k2527_1)) (.split 3 (.leaf _ k2527_2) (.leaf _ k2527_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2528)
      (.split 2 (.leaf _ k2528_0) (.leaf _ k2528_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2529)
      (.split 3 (.split 2 (.leaf _ k2529_0) (.leaf _ k2529_1)) (.leaf _ k2529_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2530)
      (.split 2 (.leaf _ k2530_0) (.leaf _ k2530_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2531)
      (.split 3 (.leaf _ k2531_0) (.leaf _ k2531_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2552)
      (.split 3 (.leaf _ k2552_0) (.leaf _ k2552_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2553)
      (.split 3 (.leaf _ k2553_0) (.leaf _ k2553_1)))

end C4.Cert.Dir052
