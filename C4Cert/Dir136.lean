module

public import C4Check

public section

/-! Cells `4034 ≤ n < 4039` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir136

theorem k4034_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4034) 3).1
      55677939777780809670949465967404085254163185890896628320638486023).isSome = true := by
  decide +kernel

theorem k4034_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4034) 3).2 2).1
      416955027084249226651272742503698201213479818327615870342284410223278082542806988213601494262111999287131462384208969048464380593552662144194696647).isSome = true := by
  decide +kernel

theorem k4034_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4034) 3).2 2).2
      18691510002089067476104618680679761384980313651252795661263477191301288823140694068961417863798533742963).isSome = true := by
  decide +kernel

theorem k4035_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4035) 3).1 2).1
      89759187145263710685196132189555147631687396964924743086030079205141903634519718157355466167455611110907105151919523233982271282).isSome = true := by
  decide +kernel

theorem k4035_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4035) 3).1 2).2
      65792607939007650466047648039035988470676648078388322667514904062390255454880620810523851).isSome = true := by
  decide +kernel

theorem k4035_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4035) 3).2 2).1
      89023780334625011409620603758428352058157486218389014271823522655858666238849448213061979990950552490062465013932486396527202097).isSome = true := by
  decide +kernel

theorem k4035_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4035) 3).2 2).2
      77255046042970047319695958391119076898997493612689846743374282521795702663122318499419835332663225932836196145).isSome = true := by
  decide +kernel

theorem k4036_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4036) 2).1 3).1
      88493857591270631217000482552191040376641692745729474308222592827970869797341223231075638032554628444644688010394244907351363377).isSome = true := by
  decide +kernel

theorem k4036_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4036) 2).1 3).2
      88089560860667247796953476993954265078230771972803494990634509596006807351192109682030786575681324397612070890917711643590217521).isSome = true := by
  decide +kernel

theorem k4036_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4036) 2).2 3).1
      76809374214988686442034431723301122742534468450597578441321098695766489703848741922114055910262411095550843697).isSome = true := by
  decide +kernel

theorem k4036_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4036) 2).2 3).2
      74683240034186762728471717076040361267862065380211421782058449303456844496807294408911196653794128137614284).isSome = true := by
  decide +kernel

theorem k4037_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4037) 2).1 3).1
      404936642670105370646540544247486592592373743358390140191819096440194437447294016093863530632114601148980197134737989829131336119867117400862555196).isSome = true := by
  decide +kernel

theorem k4037_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4037) 2).1 3).2
      296621203600790801790018176968764375699586724218957217338474065753386014661460930020482890002856722712359153).isSome = true := by
  decide +kernel

theorem k4037_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4037) 2).2 3).1
      18605938971545831785805326926237034466692772699723349383075488449204682683778316446776983147224145946571724).isSome = true := by
  decide +kernel

theorem k4037_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4037) 2).2 3).2
      4637904276150189310081233857975347972942942731546469263142387982502013921875744560329975280337513673513777).isSome = true := by
  decide +kernel

theorem k4038_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4038) 2).1 3).1
      15673465478934123067183447756915777003376280824153686107028396214159422978817036632892).isSome = true := by
  decide +kernel

theorem k4038_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4038) 2).1 3).2
      62589905399097821796806215851060217186745313496343424120916736983396532812041477366588).isSome = true := by
  decide +kernel

theorem k4038_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4038) 2).2 3).1
      980207375216589660226882221432882659856003259826390013439231957135282455309950221372).isSome = true := by
  decide +kernel

theorem k4038_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4038) 2).2 3).2
      3914026936351740915750572530221427777275402621365257915689436096152362333829443482172).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4034 4039 :=
  (Cover.one (box := dirCellBox) (n := 4034)
      (.split 3 (.leaf _ k4034_0) (.split 2 (.leaf _ k4034_1) (.leaf _ k4034_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4035)
      (.split 3 (.split 2 (.leaf _ k4035_0) (.leaf _ k4035_1)) (.split 2 (.leaf _ k4035_2) (.leaf _ k4035_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4036)
      (.split 2 (.split 3 (.leaf _ k4036_0) (.leaf _ k4036_1)) (.split 3 (.leaf _ k4036_2) (.leaf _ k4036_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4037)
      (.split 2 (.split 3 (.leaf _ k4037_0) (.leaf _ k4037_1)) (.split 3 (.leaf _ k4037_2) (.leaf _ k4037_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4038)
      (.split 2 (.split 3 (.leaf _ k4038_0) (.leaf _ k4038_1)) (.split 3 (.leaf _ k4038_2) (.leaf _ k4038_3))))

end C4.Cert.Dir136
