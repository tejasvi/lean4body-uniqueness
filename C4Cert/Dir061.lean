module

public import C4Check

public section

/-! Cells `2750 ≤ n < 2774` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir061

theorem k2750_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2750) 2).1
      536128848945852747013481662981929467309541126).isSome = true := by
  decide +kernel

theorem k2750_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2750) 2).2 2).1
      71980670993726452780273258706586375206792775830362507335815240850234757139371177604401035840035102811591).isSome = true := by
  decide +kernel

theorem k2750_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2750) 2).2 2).2
      21244415551269935290436496394545567923902444574862700043639653112569049317226932633662314296239662936554864948195572114511303).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 2751 2773 [
    3991233061712553346095834671359308822043871274549635481999998898792031987753575900447106, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2773_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2773) 3).1 3).1
      17438).isSome = true := by
  decide +kernel

theorem k2773_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2773) 3).1 3).2 2).1
      98530725884713783092467918057832507552153888151032405616077704688380911270103856420151506005155478703260430991601705047076784151).isSome = true := by
  decide +kernel

theorem k2773_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2773) 3).1 3).2 2).2
      239956056170899458871019901710988709139280328727388344793012438535).isSome = true := by
  decide +kernel

theorem k2773_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).1
      23485892500185949848506209157132401448289830256724272344525913184095682192287418352209148388360266091946229239056164022752710).isSome = true := by
  decide +kernel

theorem k2773_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).2
      6913325710667404192668015557121781287561126533446018429445333710098123981957428755187310348142689444506897204833502345612813444791785782704285130).isSome = true := by
  decide +kernel

theorem k2773_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).2
      130847446896115092921135774803919393826231646013073332379214150953391588656114436475707215893124461925637179113637000923733193765782916998256617085673175667980724557083).isSome = true := by
  decide +kernel

theorem k2773_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).1
      503138048107587915790488854440790800666241249247891028099608936528604062558372770074699202061140073825924723494459225538231192863166579841686273837072266196209780174).isSome = true := by
  decide +kernel

theorem k2773_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).2 2).1
      19403104621380848922627321636542296677780952945197659033366592456523597772733878693950132938564823736691).isSome = true := by
  decide +kernel

theorem k2773_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).2 2).2
      4136092868366840472248406853175662532753807409584757844510003482176285519626067324).isSome = true := by
  decide +kernel

theorem k2773_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).2 1).1
      19622039946797308271454712057653027823743141194595607347246012669802508737944922813938823077451570707790).isSome = true := by
  decide +kernel

theorem k2773_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).2 1).2
      19582148419777993231834776283469944751191342334264679870605048703617757795816195677738740109972397445966).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2750 2774 :=
  (Cover.one (box := dirCellBox) (n := 2750)
      (.split 2 (.leaf _ k2750_0) (.split 2 (.leaf _ k2750_1) (.leaf _ k2750_2)))).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 2773)
      (.split 3 (.split 3 (.leaf _ k2773_0) (.split 2 (.leaf _ k2773_1) (.leaf _ k2773_2))) (.split 3 (.split 2 (.split 1 (.leaf _ k2773_3) (.leaf _ k2773_4)) (.leaf _ k2773_5)) (.split 2 (.split 1 (.leaf _ k2773_6) (.split 2 (.leaf _ k2773_7) (.leaf _ k2773_8))) (.split 1 (.leaf _ k2773_9) (.leaf _ k2773_10))))))

end C4.Cert.Dir061
