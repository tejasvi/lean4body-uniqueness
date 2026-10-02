module

public import C4Check

public section

/-! Cells `2386 ≤ n < 2411` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir042

theorem k2386_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).1 2).1
      288346832528405378810297797785998328425921648288998090488623894286723650615276738630601277174088117017777).isSome = true := by
  decide +kernel

theorem k2386_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).1 2).2
      249962880032840004310953052678821031634628287857851135473009217480021275368985735829297).isSome = true := by
  decide +kernel

theorem k2386_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).2 1).1
      975889314060684942015161606841850976532411313295242030329984189089115914765402123634).isSome = true := by
  decide +kernel

theorem k2386_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).2 1).2
      15252161419201698544635383329161515129866939464365017401221822860988727233639126386).isSome = true := by
  decide +kernel

theorem k2386_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).1
      3911157684347296925980121621630592876807766225751401280015939250520030414949992388402).isSome = true := by
  decide +kernel

theorem k2386_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).2
      977526328342687626479163757104163772156028236159748501884462786505356275177209297980).isSome = true := by
  decide +kernel

theorem k2386_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).2 1).1
      61028837855347323083541083722744705404619778481802092195717061149168350349966563276).isSome = true := by
  decide +kernel

theorem k2386_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).2 1).2
      244067479760320266843061466168800881907856760745424008124325577173389951348006936364).isSome = true := by
  decide +kernel

theorem k2387_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2387) 2).1 3).1
      18421299809155988559394106393451825544777301030262606380384309736699405721468579198281165777138022084924621).isSome = true := by
  decide +kernel

theorem k2387_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2387) 2).1 3).2
      71899063406578391472925214563140167778921076552550119774574065651044815041597729875604668131403137846601).isSome = true := by
  decide +kernel

theorem k2387_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2387) 2).2 3).1
      4605486018534283165034081091757509378580263671929081747498903442745541681224902064311247044253405100996401).isSome = true := by
  decide +kernel

theorem k2387_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2387) 2).2 3).2
      997704340642146932956191181523102735068093212491926985973428129729126085653141502909617).isSome = true := by
  decide +kernel

theorem k2388_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2388) 2).1
      21200846901168558049164196041764430255562058921990502652858267013139364031379160902323377897372568608679969025022498095916487).isSome = true := by
  decide +kernel

theorem k2388_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2388) 2).2 3).1
      1150135007370873404868152615034994197232085316960497643114651079790813927865001116287457507580486586752177).isSome = true := by
  decide +kernel

theorem k2388_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2388) 2).2 3).2
      15213300141023924977286371101384566487883922335075028930058238402767219728092695921).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2389 2390 [
    30239216426754102728398961673694428401364398806109368205323769593157100081605260328390177117263477898827736587640166274261951996712619853031788599022668905785667278018846] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2390 2410 [
    3889440726033823492877426542088259981247888037354286305229370723498418320061617164738, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    667251906418096822955457637013589087616414725448315620970291974496371] = true := by
  decide +kernel

theorem k2410_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2410) 3).1 3).1
      1075438521005989450150755918705097151991198279007824838117021463561895597414051379778586).isSome = true := by
  decide +kernel

theorem k2410_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).1 3).2 2).1
      22570988278945269221427975540735152875970212444340178945224070789940687515953910153377181657437975938303394531293703808793158).isSome = true := by
  decide +kernel

theorem k2410_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).1 3).2 2).2
      219741490297565909771264012246202015782608630017006885243986513).isSome = true := by
  decide +kernel

theorem k2410_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).1
      22338310113750940635721032221254765504995997087383791747054678982271642341938020800670472854083914667202653103351584312879430).isSome = true := by
  decide +kernel

theorem k2410_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).2
      22151834297754704589542465312372148170639455782641269315049323669116110738492654621891028982506227265819746513169940255503942).isSome = true := by
  decide +kernel

theorem k2410_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).2 3).1
      4735443816938934050703987883574721934765378941100488558031200908836062797731729532531890911433000304337).isSome = true := by
  decide +kernel

theorem k2410_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).2 3).2
      1386206376707239379793305067579230356472092828373827060023131524099832656437650790310872410096805108952846126291400113732977).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2386 2411 :=
  (Cover.one (box := dirCellBox) (n := 2386)
      (.split 2 (.split 3 (.split 2 (.leaf _ k2386_0) (.leaf _ k2386_1)) (.split 1 (.leaf _ k2386_2) (.leaf _ k2386_3))) (.split 3 (.split 1 (.leaf _ k2386_4) (.leaf _ k2386_5)) (.split 1 (.leaf _ k2386_6) (.leaf _ k2386_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2387)
      (.split 2 (.split 3 (.leaf _ k2387_0) (.leaf _ k2387_1)) (.split 3 (.leaf _ k2387_2) (.leaf _ k2387_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2388)
      (.split 2 (.leaf _ k2388_0) (.split 3 (.leaf _ k2388_1) (.leaf _ k2388_2)))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 2410)
      (.split 3 (.split 3 (.leaf _ k2410_0) (.split 2 (.leaf _ k2410_1) (.leaf _ k2410_2))) (.split 2 (.split 3 (.leaf _ k2410_3) (.leaf _ k2410_4)) (.split 3 (.leaf _ k2410_5) (.leaf _ k2410_6)))))

end C4.Cert.Dir042
