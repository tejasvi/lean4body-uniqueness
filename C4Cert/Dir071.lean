module

public import C4Check

public section

/-! Cells `2833 ≤ n < 2837` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir071

theorem k2833_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 1).1
      4031816078830132909190183998794685950366497511508176891754370194874442438024351537951292).isSome = true := by
  decide +kernel

theorem k2833_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 1).2
      16123222078329471916058236424595132270472752215482088347298407480438245594260475676181308).isSome = true := by
  decide +kernel

theorem k2833_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 1).1
      13672610640198689180380334285929765355093727815094079222384197880380).isSome = true := by
  decide +kernel

theorem k2833_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 1).2
      1008765042322645829682891189281399102692617925380060487739564344604010487600226726572604).isSome = true := by
  decide +kernel

theorem k2833_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 1).1
      1005264486281220235013292892181544377571774942048436998499909974425646316038419109493820).isSome = true := by
  decide +kernel

theorem k2833_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 1).2
      62813586043717518161312050981734917608158201448965919812392793728056168330253091847228).isSome = true := by
  decide +kernel

theorem k2833_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 1).1
      13315126692695976401006866509600669255864761607881760781545077820).isSome = true := by
  decide +kernel

theorem k2833_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 1).2
      62864401344229290552478679945553010660735894679221132173050985360455959614834131975228).isSome = true := by
  decide +kernel

theorem k2834_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 1).1
      13591070630407200268371727701647026510031665597381857855361753857084).isSome = true := by
  decide +kernel

theorem k2834_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 1).2
      13273553601138490618895722891835723141744979148440062629330385980).isSome = true := by
  decide +kernel

theorem k2834_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2834) 3).1 2).2
      1213427981318903376457661130286762107503115966530247515220338975747220480103034929625472068559486197354282021105).isSome = true := by
  decide +kernel

theorem k2834_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2834) 3).2 2).1
      1395629489905029268940134978802121639646109145734737070288851771690777708879161041456700584890720693222756151107169007178685072188).isSome = true := by
  decide +kernel

theorem k2834_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2834) 3).2 2).2
      1182940281097063754627569304453456909638812086375041804300818279878884853253311664945088377296538993123720252).isSome = true := by
  decide +kernel

theorem k2835_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2835) 2).1 3).1
      348446669079293033124793467522853607818369067493779465452775185139243066796186681789116474209322649906409807072561625471233540924).isSome = true := by
  decide +kernel

theorem k2835_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2835) 2).1 3).2
      18428849438344109233037540352953722731531605239195948493652254801146870782616636678910609684926407229555516).isSome = true := by
  decide +kernel

theorem k2835_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2835) 2).2 3).1
      4725205951463217936646152709491040223119213636172024620066677832174858589142990830221391402843376504580850492).isSome = true := by
  decide +kernel

theorem k2835_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2835) 2).2 3).2
      21766054032137110298593178456008679469118331732863416408000670862210139540902361409007355192613689685286216356623370601767879484).isSome = true := by
  decide +kernel

theorem k2836_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2836) 2).1 3).1
      3899242709134579540774168024367548318941549948633328872426038135829383885019371926076).isSome = true := by
  decide +kernel

theorem k2836_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2836) 2).1 3).2
      3896681654080443506322771840438107176786330791409759874562932639843016277691066610236).isSome = true := by
  decide +kernel

theorem k2836_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2836) 2).2 3).1
      15603002280026384395074780366759250037728911222609489713171008230522318724872663450428).isSome = true := by
  decide +kernel

theorem k2836_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2836) 2).2 3).2
      15591604017952215294324696264106907618208706928535819982017255759404400467790431503164).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2833 2837 :=
  (Cover.one (box := dirCellBox) (n := 2833)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2833_0) (.leaf _ k2833_1)) (.split 1 (.leaf _ k2833_2) (.leaf _ k2833_3))) (.split 2 (.split 1 (.leaf _ k2833_4) (.leaf _ k2833_5)) (.split 1 (.leaf _ k2833_6) (.leaf _ k2833_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2834)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2834_0) (.leaf _ k2834_1)) (.leaf _ k2834_2)) (.split 2 (.leaf _ k2834_3) (.leaf _ k2834_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2835)
      (.split 2 (.split 3 (.leaf _ k2835_0) (.leaf _ k2835_1)) (.split 3 (.leaf _ k2835_2) (.leaf _ k2835_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2836)
      (.split 2 (.split 3 (.leaf _ k2836_0) (.leaf _ k2836_1)) (.split 3 (.leaf _ k2836_2) (.leaf _ k2836_3))))

end C4.Cert.Dir071
