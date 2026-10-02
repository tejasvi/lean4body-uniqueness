module

public import C4Check

public section

/-! Cells `2803 ≤ n < 2804` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir067

theorem k2803_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).1
      64499750649958877950695043396730015054488873385698780452289090214580571038997866243313).isSome = true := by
  decide +kernel

theorem k2803_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).2
      64577712276804701836880527162608528379619754289348716047754138644591307459339801432817).isSome = true := by
  decide +kernel

theorem k2803_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).1
      16044154471926435048167710316239440551123008132904446467614716161280041173155273727164).isSome = true := by
  decide +kernel

theorem k2803_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).2
      16061386129592420890923447002153422605192584812862423930968379178695754550199185267900).isSome = true := by
  decide +kernel

theorem k2803_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).1 2).1
      64634739301824235202112954372600077638788461837707292043186326040102356330904110076657).isSome = true := by
  decide +kernel

theorem k2803_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).1 2).2
      15792191743902140055568450179252084923403938105711467512799124507707240223222321521).isSome = true := by
  decide +kernel

theorem k2803_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).2 1).1
      1005536762210548229736379150411105448426851405315285916419023941460212350312177687996).isSome = true := by
  decide +kernel

theorem k2803_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).2 1).2
      4019431668262900899662659607826826780869878318622598984608636706183687604516012152636).isSome = true := by
  decide +kernel

theorem k2803_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).1
      3462047388915173774597321885662101409392261513739490988576600967996).isSome = true := by
  decide +kernel

theorem k2803_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).2
      3997141075933674517014202126178728982410369109340914363927333570793217402984069584700).isSome = true := by
  decide +kernel

theorem k2803_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).1
      862302698189617878429282664901365611652669365084651140189508850492).isSome = true := by
  decide +kernel

theorem k2803_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).2
      863128306942513145708489534311280307084493458325362217277169027900).isSome = true := by
  decide +kernel

theorem k2803_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 2).1 1).1
      865704059146476355077914939143838057169085767721233800697779014460).isSome = true := by
  decide +kernel

theorem k2803_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 2).1 1).2
      216353122825413709431624069132357856567835470796417794583605793596).isSome = true := by
  decide +kernel

theorem k2803_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 2).2 1).1
      999124379042360634619198760398185850040137073507589754002824134514977413723898500924).isSome = true := by
  decide +kernel

theorem k2803_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 2).2 1).2
      54133582157281932835383177881511209043259404347229909895306671676).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2803 2804 :=
  (Cover.one (box := dirCellBox) (n := 2803)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2803_0) (.leaf _ k2803_1)) (.split 2 (.leaf _ k2803_2) (.leaf _ k2803_3))) (.split 3 (.split 2 (.leaf _ k2803_4) (.leaf _ k2803_5)) (.split 1 (.leaf _ k2803_6) (.leaf _ k2803_7)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2803_8) (.leaf _ k2803_9)) (.split 2 (.leaf _ k2803_10) (.leaf _ k2803_11))) (.split 2 (.split 1 (.leaf _ k2803_12) (.leaf _ k2803_13)) (.split 1 (.leaf _ k2803_14) (.leaf _ k2803_15))))))

end C4.Cert.Dir067
