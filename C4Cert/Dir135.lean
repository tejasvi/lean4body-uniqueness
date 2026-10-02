module

public import C4Check

public section

/-! Cells `4009 ≤ n < 4034` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir135

theorem k4009_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 1).1
      15721844224354394266127992768766857957504283152399825593493759034791213976049948281404).isSome = true := by
  decide +kernel

theorem k4009_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 1).2
      208031295431028767864562782758144291431028035481232245531368764).isSome = true := by
  decide +kernel

theorem k4009_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4009) 2).1 3).2
      341625285753197524124715604964306161632148754078517824273270113838986224018920841927297774316119728216647101252948925281826034).isSome = true := by
  decide +kernel

theorem k4009_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4009) 2).2 3).1
      350875604004522362558568527048714692267227139783684896646963544113576131720060282897792408394798599593324198297575131644788338929).isSome = true := by
  decide +kernel

theorem k4009_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4009) 2).2 3).2
      4743931481744411522541656139976415591966962204827056743156167604107662457899164173403714523810143429516970226).isSome = true := by
  decide +kernel

theorem k4010_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4010) 2).1 3).1
      5327075257125236640847307352470429530196521801185840476028240396619592548760761070944541771571111721420147823200709555771196).isSome = true := by
  decide +kernel

theorem k4010_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4010) 2).1 3).2
      72080398527053219840814017664007056150985141588163342352078091752211460027714546772675039913094146258161).isSome = true := by
  decide +kernel

theorem k4010_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4010) 2).2 3).1
      288962777633851631184193837759900225063909943851149022587380938002296429134130676941696595006878096282428).isSome = true := by
  decide +kernel

theorem k4010_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4010) 2).2 3).2
      288510679023252534375038309652138415706226639289780574517896711512873077101153030450966358524505326342972).isSome = true := by
  decide +kernel

theorem k4011_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4011) 2).1 3).1
      72003067586143098537184627506327119333732855386832053599201453652692336831634909930175103419276841809137).isSome = true := by
  decide +kernel

theorem k4011_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4011) 2).1 3).2
      206477655857407946291826883952837007539128948891847754070449468).isSome = true := by
  decide +kernel

theorem k4011_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4011) 2).2 3).1
      1152645102929478000615986210188692152513671146076910796322152043798628986476945785289643105615793723755324).isSome = true := by
  decide +kernel

theorem k4011_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4011) 2).2 3).2
      17994728302662773212020361141766337070124046324003604118886179872410136208113632040926020511162045421372).isSome = true := by
  decide +kernel

theorem k4012_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4012) 2).1
      115488787444888716442172451994033589207186683803943922963395153396585377830335422652292665160067542122270479538436307865275385380372148157203498247297216256790066675).isSome = true := by
  decide +kernel

theorem k4012_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4012) 2).2
      339437301175046693545302987146839936072768696793923858852289455930578507770321867074150297238856023182459519562000818033489139).isSome = true := by
  decide +kernel

theorem k4013_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4013) 2).1
      115408839314134903325159682103393316800410787050648683131398546261657362794452234307086947281754015049015503820092512781300168866104937004818793531765881359891789297).isSome = true := by
  decide +kernel

theorem k4013_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4013) 2).2
      25026828269404672749102375528157586968925996302391176506968197977967043190539250069867900296552056022689889312428332110588632697652821630451569395).isSome = true := by
  decide +kernel

theorem k4014_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4014) 2).1
      15198407782950256682637654063018346814960432767125253408633531756668353576236250483).isSome = true := by
  decide +kernel

theorem k4014_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4014) 2).2
      1563407308471223641832748623293060266699902563280673095938621115778284852369391311008844687573242892114244245103175514287776467566854873766786300).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4015 4016 [
    21178083613689788215480519234681722353294259753605212062270463957569581779181079169291421405632261895484965207426583124203590] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4016 4034 [
    60759316587198435587307387247787321789624199384166802540452790743805462699717008754,
    174328725808850129317892459575885145213297, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4009 4034 :=
  (Cover.one (box := dirCellBox) (n := 4009)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4009_0) (.leaf _ k4009_1)) (.leaf _ k4009_2)) (.split 3 (.leaf _ k4009_3) (.leaf _ k4009_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4010)
      (.split 2 (.split 3 (.leaf _ k4010_0) (.leaf _ k4010_1)) (.split 3 (.leaf _ k4010_2) (.leaf _ k4010_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4011)
      (.split 2 (.split 3 (.leaf _ k4011_0) (.leaf _ k4011_1)) (.split 3 (.leaf _ k4011_2) (.leaf _ k4011_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4012)
      (.split 2 (.leaf _ k4012_0) (.leaf _ k4012_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4013)
      (.split 2 (.leaf _ k4013_0) (.leaf _ k4013_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4014)
      (.split 2 (.leaf _ k4014_0) (.leaf _ k4014_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7)

end C4.Cert.Dir135
