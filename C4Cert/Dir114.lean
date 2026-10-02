module

public import C4Check

public section

/-! Cells `3559 ≤ n < 3560` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir114

theorem k3559_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).1
      18398373699319646884502856487759452979478109539525134193133054112676965993838356557353712300990703492529).isSome = true := by
  decide +kernel

theorem k3559_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).2
      18313960084047421364387079329744912233702601237672472200191501871483408608958556616847222861746846522801).isSome = true := by
  decide +kernel

theorem k3559_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).1
      3998338413170423684629933270642032531663390010959878356383256254590970992339690549937).isSome = true := by
  decide +kernel

theorem k3559_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).2
      3978920315004901164907703383692409442170373066087587687343788521445714970011272573617).isSome = true := by
  decide +kernel

theorem k3559_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).1
      18247759304331104201158590284101861151769563295039480201695812421190984032085858600761702040475280825777).isSome = true := by
  decide +kernel

theorem k3559_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).2
      4548887389190691753282684970519273837410733729041424469956486271447265993690578840426936208582093510513).isSome = true := by
  decide +kernel

theorem k3559_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).1
      18278238045461467676878534602155772959605186532919633226383582188593398941323630250978913369334915292593).isSome = true := by
  decide +kernel

theorem k3559_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).2
      18221273190253942860110323500686013238398799028577116514368190439100373896972070484171237828253544177073).isSome = true := by
  decide +kernel

theorem k3559_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).1
      256246021644624855119231660811839463568725392975213283394405641174523357272771875986609).isSome = true := by
  decide +kernel

theorem k3559_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).2
      996546141978015612697679058042969793518420742192621934320445348832797780930951404721).isSome = true := by
  decide +kernel

theorem k3559_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).1
      4011757239971672526882422361670124682658328069030079516375331593949404206245406496561).isSome = true := by
  decide +kernel

theorem k3559_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).2
      3993353210929083520763500703892698766317823455896513276280704811787776199569186353724).isSome = true := by
  decide +kernel

theorem k3559_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).1
      3969888810670449825123846586356355766883463600232917716217702437759688306532840993457).isSome = true := by
  decide +kernel

theorem k3559_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).2
      3956698928355534059131955974836821454129717646485228295376034578190976262538035294897).isSome = true := by
  decide +kernel

theorem k3559_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 1).1
      860809697780343786119801900949914997073147213877322938762497870396).isSome = true := by
  decide +kernel

theorem k3559_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 1).2
      15476991754181222976176171026601521516260368236398820670397998639202538419409960307).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3559 3560 :=
  (Cover.one (box := dirCellBox) (n := 3559)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3559_0) (.leaf _ k3559_1)) (.split 3 (.leaf _ k3559_2) (.leaf _ k3559_3))) (.split 2 (.split 3 (.leaf _ k3559_4) (.leaf _ k3559_5)) (.split 3 (.leaf _ k3559_6) (.leaf _ k3559_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3559_8) (.leaf _ k3559_9)) (.split 3 (.leaf _ k3559_10) (.leaf _ k3559_11))) (.split 2 (.split 3 (.leaf _ k3559_12) (.leaf _ k3559_13)) (.split 1 (.leaf _ k3559_14) (.leaf _ k3559_15))))))

end C4.Cert.Dir114
