module

public import C4Check

public section

/-! Cells `3166 ≤ n < 3167` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir088

theorem k3166_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).1
      66407344063170248028593186463661980776249917321643669776462864625613595303836607385404).isSome = true := by
  decide +kernel

theorem k3166_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).2
      4144157569503280296537204547940344737591729528985025559902306786668730043356977426668).isSome = true := by
  decide +kernel

theorem k3166_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).2 1).1
      64786741344290287297832413426572041424920219277867686987465305278194252196356024691).isSome = true := by
  decide +kernel

theorem k3166_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).2 1).2
      259652478471506759305699488196232048804803111466600954085895157621591060525084147116).isSome = true := by
  decide +kernel

theorem k3166_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).1
      4097788558609493549126082804589383969918309672239449533215205509570160259909203514172).isSome = true := by
  decide +kernel

theorem k3166_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).2
      1027060989567681531513988791359970644914146799964188989502792009751616668424414295612).isSome = true := by
  decide +kernel

theorem k3166_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).2
      1463895531959904338064230766861194782671589669403016360819118702354760668666327311297687422449226987738727347931227188508095249586).isSome = true := by
  decide +kernel

theorem k3166_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).1
      363555708896329395508170096892643294457729644579259090756772192810679797640219434748014910880670984611404046143199199418479858).isSome = true := by
  decide +kernel

theorem k3166_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).2
      90749868718124262143646677275987399666960470098447784676668248355341604559341080414380263472817682116731780608548283079030002).isSome = true := by
  decide +kernel

theorem k3166_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 2).1
      19413176019530283546345984114748341091463080982202989604392251805960238110386178483479922227184586186650865).isSome = true := by
  decide +kernel

theorem k3166_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 2).2
      311013164911205077947683820212575673101604310434204157477559587715318451542579152090412864220215803192898801).isSome = true := by
  decide +kernel

theorem k3166_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).1
      5016357281172517420177936146845740463309974060464628595304645361704181432421056296721359291297736665012834871537).isSome = true := by
  decide +kernel

theorem k3166_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).2
      4976910482414439273750622867870203650621766202135669661791769206380479744743287947393468370275901053941908490481).isSome = true := by
  decide +kernel

theorem k3166_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).1
      220472387079241814147954281238116738677211841578959179540884485692).isSome = true := by
  decide +kernel

theorem k3166_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).2
      13763711486622970615716838036219895645778375869231386193546542140).isSome = true := by
  decide +kernel

theorem k3166_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).2
      311832836580402767105555192744314889074924376677813654165786949148783186811101830356660060694278387810220624113).isSome = true := by
  decide +kernel

theorem k3166_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 2).1
      4805423545019458661012309206301194291392605554924152916220494838125346775058138730655382565891311488300273).isSome = true := by
  decide +kernel

theorem k3166_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 2).2
      1203415139559339437384539034720488727288809583941443838866351797473897769193838360630774707433340356615601).isSome = true := by
  decide +kernel

theorem k3166_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).1
      16539702538756941850466188895230020395713224554807634636521854279137777674392866048351665).isSome = true := by
  decide +kernel

theorem k3166_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).2
      1193863612153757040228667689387667071265638378270466106123686155458536334210659417740098852811788982705585).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3166 3167 :=
  (Cover.one (box := dirCellBox) (n := 3166)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3166_0) (.leaf _ k3166_1)) (.split 1 (.leaf _ k3166_2) (.leaf _ k3166_3))) (.split 1 (.split 2 (.leaf _ k3166_4) (.leaf _ k3166_5)) (.leaf _ k3166_6))) (.split 3 (.split 1 (.leaf _ k3166_7) (.leaf _ k3166_8)) (.split 2 (.leaf _ k3166_9) (.leaf _ k3166_10)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3166_11) (.leaf _ k3166_12)) (.split 3 (.split 1 (.leaf _ k3166_13) (.leaf _ k3166_14)) (.leaf _ k3166_15))) (.split 3 (.split 2 (.leaf _ k3166_16) (.leaf _ k3166_17)) (.split 2 (.leaf _ k3166_18) (.leaf _ k3166_19))))))

end C4.Cert.Dir088
