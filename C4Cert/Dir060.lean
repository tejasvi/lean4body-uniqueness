module

public import C4Check

public section

/-! Cells `2748 ≤ n < 2750` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir060

theorem k2748_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).1 3).1
      5348880883827327616292579726505388087128295891065944341540432133971465672386172534736638995433553517337299598695017112755633).isSome = true := by
  decide +kernel

theorem k2748_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).1 3).2
      15330943221486107312927729927847993679018748410808141579338438308419637896561172849).isSome = true := by
  decide +kernel

theorem k2748_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).1
      4642020288929636201641339743887440002367365125110227544388374412740277124164872901312240890696461657666225).isSome = true := by
  decide +kernel

theorem k2748_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).2
      18109594009028986553232072814389727057141042466041015221912539992248047108089532145729523236219559828913).isSome = true := by
  decide +kernel

theorem k2748_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).1
      6294323448301281039239864728033267851823897410243317236912102630485470747555118520488407979803459011881058838236868943560631885591091452162950599).isSome = true := by
  decide +kernel

theorem k2748_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).2
      1858304137086276162593440684599915874506994286003336612726352087040203025275755352437900138302275007415393343440984766386445253917899361714579613759336202537111537095).isSome = true := by
  decide +kernel

theorem k2748_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).1
      1161617196847589321901959561811078680652390027882577828347549236953798119225593095915048718166967269809329).isSome = true := by
  decide +kernel

theorem k2748_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).2
      290016597406350306581187291472437306695067857923235366993451504943370518856289599941232863139284865504060).isSome = true := by
  decide +kernel

theorem k2748_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).1
      252014044722983036222805737885674062962512712208503377466477907741824015573986500631729).isSome = true := by
  decide +kernel

theorem k2748_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).2
      15730479028481906879502684049399556856022081374035102384988468748826926408966109383228).isSome = true := by
  decide +kernel

theorem k2748_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).1 3).1
      15697963393972034512345411911062424375700933266985348778936014503322228893093909357773).isSome = true := by
  decide +kernel

theorem k2748_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).1 3).2
      15312035526792468242203541821546045105211860356042174370522564763727901793517710705).isSome = true := by
  decide +kernel

theorem k2748_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).2 3).1
      72454509146502326730955068570703479032713589018352237770853138082412885768169433172273708724140518012476).isSome = true := by
  decide +kernel

theorem k2748_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).2 3).2
      980596491356982044531205393990650569499332017108419866412645120599587601999068945585).isSome = true := by
  decide +kernel

theorem k2749_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2749) 2).1 2).1
      288450320697366269211240255581921183103618974505798384279895759577967622419226452299999923012183944275223).isSome = true := by
  decide +kernel

theorem k2749_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).1 2).2 3).1
      72159875833641725816114660491311305862205094708244644648001564668164673438234417896342182210875489674695).isSome = true := by
  decide +kernel

theorem k2749_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).1 2).2 3).2
      15268382283681540711842391118107444374089276948538552386853166865375058296386062705).isSome = true := by
  decide +kernel

theorem k2749_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).1
      340956216358349457702390440260875199023019732399040319967285181565861288344652818276774998804513102883248994542357876269741297).isSome = true := by
  decide +kernel

theorem k2749_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).2
      341084088477771555149343265275763035904606053380370130371868132373685469840580243962176528284374211168051005195840733368644849).isSome = true := by
  decide +kernel

theorem k2749_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).2 2).1
      15269606899552115651489679523495280608883586600887176629343530310593671904159999345).isSome = true := by
  decide +kernel

theorem k2749_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).2 2).2
      21287585994892328055121601913712321156665629208261284862757554564244870583873000608672287383026075598250901039027092136490225).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2748 2750 :=
  (Cover.one (box := dirCellBox) (n := 2748)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2748_0) (.leaf _ k2748_1)) (.split 3 (.leaf _ k2748_2) (.leaf _ k2748_3))) (.split 2 (.leaf _ k2748_4) (.leaf _ k2748_5))) (.split 3 (.split 2 (.split 3 (.leaf _ k2748_6) (.leaf _ k2748_7)) (.split 3 (.leaf _ k2748_8) (.leaf _ k2748_9))) (.split 2 (.split 3 (.leaf _ k2748_10) (.leaf _ k2748_11)) (.split 3 (.leaf _ k2748_12) (.leaf _ k2748_13)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2749)
      (.split 2 (.split 2 (.leaf _ k2749_0) (.split 3 (.leaf _ k2749_1) (.leaf _ k2749_2))) (.split 3 (.split 2 (.leaf _ k2749_3) (.leaf _ k2749_4)) (.split 2 (.leaf _ k2749_5) (.leaf _ k2749_6)))))

end C4.Cert.Dir060
