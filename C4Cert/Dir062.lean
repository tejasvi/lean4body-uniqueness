module

public import C4Check

public section

/-! Cells `2774 ≤ n < 2775` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir062

theorem k2774_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).1
      107276844625970930642322262805217810812013501361784749223969923638196450936567337115989965487036754347229958026054930548819311142395743645618935246).isSome = true := by
  decide +kernel

theorem k2774_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).1
      66546508004057793226354392824249114171603259762849874385313322858232703635950249862386).isSome = true := by
  decide +kernel

theorem k2774_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).2
      16276132865277432377728978999703047057876388754423950609626382541822393410740133244).isSome = true := by
  decide +kernel

theorem k2774_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).1
      1424361455937123534707050733779478199854102982260272675291821080855604917753729602787843938490733118095704795177029092079090).isSome = true := by
  decide +kernel

theorem k2774_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).2
      123883434386129194742955989949465153475614886265929512602876708379627219151833557078812479118624626132298184748635733661345787376820017622861274016297652241173149170).isSome = true := by
  decide +kernel

theorem k2774_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).1
      6776582952868842340268238216284436936224837470817250072972067784980737691540123224927734367536799553988980407631356349884424616799306303139484366278).isSome = true := by
  decide +kernel

theorem k2774_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).1
      4102934196222890644529461155152026244379983656667404125749614316152087890968924641084).isSome = true := by
  decide +kernel

theorem k2774_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).2
      755396139927506245152321534808463594886915260).isSome = true := by
  decide +kernel

theorem k2774_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 2).1
      311374731809703776137522245869392000930343772020635683461082578019654461665374520489825101589505135261283825).isSome = true := by
  decide +kernel

theorem k2774_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 2).2
      6632723960501790426155208806565746563246831169908874053859188906764803095333374341906092008249440795947289854233723310211800336272648223862584817).isSome = true := by
  decide +kernel

theorem k2774_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).1
      16261160122402341742537359797223924335185433155670422597702140159488723304885463768252).isSome = true := by
  decide +kernel

theorem k2774_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).2
      187089174748961293381181236994192818732954812).isSome = true := by
  decide +kernel

theorem k2774_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).1
      220101087291882703577584354568465459665899912170288207957210385212).isSome = true := by
  decide +kernel

theorem k2774_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).2
      55178314183716407936151423476904308785188032562515173638620550972).isSome = true := by
  decide +kernel

theorem k2774_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).1
      54644577519320978763634934077527065102649873592407194448364435004).isSome = true := by
  decide +kernel

theorem k2774_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).2
      54597281887138733640378405506653184489420284260268128017897092668).isSome = true := by
  decide +kernel

theorem k2774_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).2
      1058475311558758320073786072725591692882419711840872410033738181292766209630759702738662641).isSome = true := by
  decide +kernel

theorem k2774_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 2).1
      77052955999075602145388481724952304405614563970893216368697824925082598815688448078647475651233232240539121).isSome = true := by
  decide +kernel

theorem k2774_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 2).2
      4823751313433499488308139706434995859519610026587076686794382011598091385636632125158511468875747570705905).isSome = true := by
  decide +kernel

theorem k2774_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).1
      1035755397885617670000491716134221676189532636387540234842853015468156971292436802938097).isSome = true := by
  decide +kernel

theorem k2774_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).2
      259366701009764045557653872605280415697148226722534318733776210709423833216911185646321).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2774 2775 :=
  (Cover.one (box := dirCellBox) (n := 2774)
      (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2774_0) (.split 2 (.leaf _ k2774_1) (.leaf _ k2774_2))) (.split 1 (.leaf _ k2774_3) (.leaf _ k2774_4))) (.split 2 (.split 1 (.leaf _ k2774_5) (.split 2 (.leaf _ k2774_6) (.leaf _ k2774_7))) (.split 2 (.leaf _ k2774_8) (.leaf _ k2774_9)))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k2774_10) (.leaf _ k2774_11)) (.split 2 (.leaf _ k2774_12) (.leaf _ k2774_13))) (.split 2 (.split 1 (.leaf _ k2774_14) (.leaf _ k2774_15)) (.leaf _ k2774_16))) (.split 3 (.split 2 (.leaf _ k2774_17) (.leaf _ k2774_18)) (.split 2 (.leaf _ k2774_19) (.leaf _ k2774_20))))))

end C4.Cert.Dir062
