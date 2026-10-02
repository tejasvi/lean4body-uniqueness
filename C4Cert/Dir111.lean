module

public import C4Check

public section

/-! Cells `3531 ≤ n < 3557` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir111

theorem k3531_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).1
      15780886567029605515438660111103431162612840149150025088334423303252774882292805937447).isSome = true := by
  decide +kernel

theorem k3531_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).2
      25379308696901453697795644216811531581174549602712367286179678017733369715809386838841650664412081838359965556352873038124527876272718928928888599).isSome = true := by
  decide +kernel

theorem k3531_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).2 2).1
      3930127880579232190918219113213395756974346836226257779955589134726421829247170618823).isSome = true := by
  decide +kernel

theorem k3531_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).2 2).2
      21403947378975688017040846189541775876514553982119267653446739128879588571346515634230140679879506453560329309946136235795911).isSome = true := by
  decide +kernel

theorem k3531_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).1 3).1
      3969507284766198689064718163297414166258148512776064302870994677874944763394397664497).isSome = true := by
  decide +kernel

theorem k3531_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).1 3).2
      61798984610167033426361048012789088173118455874201793812684665523440240003901441477).isSome = true := by
  decide +kernel

theorem k3531_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).1
      18355194496080741719097502279132365680500806181895785478607350666094075700301759297632171903281501330865).isSome = true := by
  decide +kernel

theorem k3531_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).2
      18277612034347034763888196225858864465402516865766894237766997737288186622091804163617422897760622042545).isSome = true := by
  decide +kernel

theorem k3531_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).1
      21424275859076162428888890101443730679986478481254727482117860603255752393275799762491301694865434116428204546114030814488007).isSome = true := by
  decide +kernel

theorem k3531_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).2
      7473948629666528197531963398662470575578133818293247126109861335991632664001558299561984753012477640703678456595319714852047049197626718775617282243451694554222261959).isSome = true := by
  decide +kernel

theorem k3532_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3532) 2).1 2).1
      349303195871742994704196763091247677339811087837673362984829945065243745778844252223259761270276262661866148988886675742817605407).isSome = true := by
  decide +kernel

theorem k3532_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).1 2).2 3).1
      21347672783575964274089201015550904934751611635392497948973710135866195783118768667774550767144724885335448531868250388374983).isSome = true := by
  decide +kernel

theorem k3532_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).1 2).2 3).2
      61182875002679395432900020740159766505813691709341310229941475547799396337669502405).isSome = true := by
  decide +kernel

theorem k3532_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).1
      21357802655251522102470967846530808188493453220788316785691730485077172405497327882172117814215923880598373228409635374806471).isSome = true := by
  decide +kernel

theorem k3532_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).2
      21372169720158611172488507168881071376973252017269613516891663591959511455134051390219382111709149461338950249696794449536455).isSome = true := by
  decide +kernel

theorem k3532_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).2 2).1
      72245418810601998765813560344067255632943411756463034306976799235758505363547577630961124010972575790577).isSome = true := by
  decide +kernel

theorem k3532_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).2 2).2
      1333458741691660750711634357964646698452716534716703043110794013472474308116296777835100121881686564253341436458268371809777).isSome = true := by
  decide +kernel

theorem k3533_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3533) 2).1
      4723882023854374527271396966005643849481153465911721894786093274949896493196251003811421736946722703001144606).isSome = true := by
  decide +kernel

theorem k3533_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3533) 2).2 2).1
      85082790461323203614610000338486558958235875939687459427772164130655754322191038507953825062670589386962348588332319752548663).isSome = true := by
  decide +kernel

theorem k3533_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3533) 2).2 2).2 3).1
      1331145037417562302751034669104551034413919147912969620524884254330881537506449519633571052363233558715844253172339215005169).isSome = true := by
  decide +kernel

theorem k3533_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3533) 2).2 2).2 3).2
      51708418503397957773470853456656019101697663665102541669851505).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3534 3557 [
    1425415349811361854293928995446740439000636107366951864076374137365834336626343317077821866607990910094475429416815398259288284143110,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3531 3557 :=
  (Cover.one (box := dirCellBox) (n := 3531)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3531_0) (.leaf _ k3531_1)) (.split 2 (.leaf _ k3531_2) (.leaf _ k3531_3))) (.split 3 (.split 2 (.split 3 (.leaf _ k3531_4) (.leaf _ k3531_5)) (.split 3 (.leaf _ k3531_6) (.leaf _ k3531_7))) (.split 2 (.leaf _ k3531_8) (.leaf _ k3531_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3532)
      (.split 2 (.split 2 (.leaf _ k3532_0) (.split 3 (.leaf _ k3532_1) (.leaf _ k3532_2))) (.split 3 (.split 2 (.leaf _ k3532_3) (.leaf _ k3532_4)) (.split 2 (.leaf _ k3532_5) (.leaf _ k3532_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3533)
      (.split 2 (.leaf _ k3533_0) (.split 2 (.leaf _ k3533_1) (.split 3 (.leaf _ k3533_2) (.leaf _ k3533_3))))).trans <|
  (Cover.dir c3)

end C4.Cert.Dir111
