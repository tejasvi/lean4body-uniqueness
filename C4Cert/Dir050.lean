module

public import C4Check

public section

/-! Cells `2496 ≤ n < 2501` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir050

theorem k2496_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2496) 3).1 2).1
      25570765680963862902213971592393879075378778088001658922389133633060212510772797991888634805871320666527715899443936041835777143078072086150346227).isSome = true := by
  decide +kernel

theorem k2496_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2496) 3).1 2).2
      1355416862255077806267869066117050723191738546659294378870658124103440577609834667098099683612803806128246457048688244456817).isSome = true := by
  decide +kernel

theorem k2496_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2496) 3).2 2).1
      74884875604131842995499969325980197727897293764440448223077365948306768417000402862791931304745399578217724).isSome = true := by
  decide +kernel

theorem k2496_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2496) 3).2 2).2
      86348306500902794855166591699597062564586703534275403931514135720702828938145268461860876072701939030931351176605829246579964).isSome = true := by
  decide +kernel

theorem k2497_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2497) 3).1 2).1
      252754734529947557266391966887321404986464578728424973261358293952145530746200620101884).isSome = true := by
  decide +kernel

theorem k2497_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2497) 3).1 2).2
      252797935284790501619121665361145415077840547723827752799924281440143345656177002115324).isSome = true := by
  decide +kernel

theorem k2497_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2497) 3).2 2).1
      62991587751450862854068686850440238250388116195865420067786749402790911983775784061756).isSome = true := by
  decide +kernel

theorem k2497_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2497) 3).2 2).2
      15754942814125363866741908150131069423617377502680837755834464368412483664573260879676).isSome = true := by
  decide +kernel

theorem k2498_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2498) 3).1 2).1
      16085437181735786323567993574339668290659925995194540141711199585647558448504141000094524).isSome = true := by
  decide +kernel

theorem k2498_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2498) 3).1 2).2
      15715359606845044127555201314711236729666643987656840508052447352693783690384216937276).isSome = true := by
  decide +kernel

theorem k2498_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2498) 3).2 2).1
      4109680687390780676607120268182309378898072772569821083030734315582305126505481537569407804).isSome = true := by
  decide +kernel

theorem k2498_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2498) 3).2 2).2
      3400490819700316196076375576568212409717444184273024468488793563964).isSome = true := by
  decide +kernel

theorem k2499_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2499) 3).1 2).1
      256435130764838527061454663347951607684073817152381577504970851845350705846474099690896444).isSome = true := by
  decide +kernel

theorem k2499_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2499) 3).1 2).2
      3395544634583148151488850607372708537268292813303963488812604572476).isSome = true := by
  decide +kernel

theorem k2499_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2499) 3).2 2).1
      16008606496016372653887854757300398662967106716163717217385676493347659167906239367396412).isSome = true := by
  decide +kernel

theorem k2499_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2499) 3).2 2).2
      183786672474099452668232897169097931082398219324).isSome = true := by
  decide +kernel

theorem k2500_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2500) 3).1 1).1
      999489781946744099750399212041588984160106381617056979564457833110091601804999538195516).isSome = true := by
  decide +kernel

theorem k2500_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2500) 3).1 1).2
      216731616039677307758240972247059768898066207342331448941198687026236).isSome = true := by
  decide +kernel

theorem k2500_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2500) 3).2
      7761002723290477910184561774576299538571710234872475787763327668710808569076021718478911363698207483940538738089095839542425496156272738137578675021067059760308110276377660).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2496 2501 :=
  (Cover.one (box := dirCellBox) (n := 2496)
      (.split 3 (.split 2 (.leaf _ k2496_0) (.leaf _ k2496_1)) (.split 2 (.leaf _ k2496_2) (.leaf _ k2496_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2497)
      (.split 3 (.split 2 (.leaf _ k2497_0) (.leaf _ k2497_1)) (.split 2 (.leaf _ k2497_2) (.leaf _ k2497_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2498)
      (.split 3 (.split 2 (.leaf _ k2498_0) (.leaf _ k2498_1)) (.split 2 (.leaf _ k2498_2) (.leaf _ k2498_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2499)
      (.split 3 (.split 2 (.leaf _ k2499_0) (.leaf _ k2499_1)) (.split 2 (.leaf _ k2499_2) (.leaf _ k2499_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2500)
      (.split 3 (.split 1 (.leaf _ k2500_0) (.leaf _ k2500_1)) (.leaf _ k2500_2)))

end C4.Cert.Dir050
