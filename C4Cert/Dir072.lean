module

public import C4Check

public section

/-! Cells `2868 ≤ n < 2891` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir072

theorem k2868_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2868) 2).1
      25589766909501293772175487560876530800783697671293188567265514530295686960133003246159688573053255125294309864202037405923631929618626309800739598579).isSome = true := by
  decide +kernel

theorem k2868_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2868) 2).2
      346984222513147433478173536628889752805503892821716139550020198350483390187926396467149042590218143133651775484722277370182299891).isSome = true := by
  decide +kernel

theorem k2869_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2869) 2).1
      62186422190292557970053476806801592268311845616746637493205307339227233234883052723379).isSome = true := by
  decide +kernel

theorem k2869_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2869) 2).2
      18354862316291422852469659951029091999292437084489607780605260024637386836516847308220241118206924395240243).isSome = true := by
  decide +kernel

theorem k2870_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2870) 2).1
      248716717233086619446857252171316895547864876352283912168637244865510778487597024765133).isSome = true := by
  decide +kernel

theorem k2870_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2870) 2).2
      3886208869333424391114321169767226025848684955808941659197890521377960120678856447793).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2871 2872 [
    7371592471485196899059235606588401393006915046816167266428104666518634673737434898607698093120427289209064460277277116211861204313697758451839846512036402885581088198] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2872 2887 [
    2360931922208720544577, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k2887_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2887) 3).1
      6616908275518398056963760012248783694910487594025595557984131726501225617446639952282521541665252929487108877350803289944734650077327629695126208795).isSome = true := by
  decide +kernel

theorem k2887_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2887) 3).2 2).1 1).1
      4611592590682743909982122888599783575808504408019269740373859392712291542815014701679864338153663152499).isSome = true := by
  decide +kernel

theorem k2887_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2887) 3).2 2).1 1).2
      73759424545074957611746646683789280903569121161714634814157701928800429803117525944153044033572194787699).isSome = true := by
  decide +kernel

theorem k2887_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2887) 3).2 2).2
      21768807129551552006875095616722782432190729179729077423454425375184709645195858298969739852153300681724476898313517536290893).isSome = true := by
  decide +kernel

theorem k2888_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).1 2).1 1).1
      1018013662646273068304532269744942734308092868027240401459642330178471113936846239720691).isSome = true := by
  decide +kernel

theorem k2888_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).1 2).1 1).2
      18757101039669935187815713501205965240362521828424777516942113496097719855531095976585814759886932290139379).isSome = true := by
  decide +kernel

theorem k2888_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).1 2).2 1).1
      994260578923508219463888816685243100494299280382087130268785188330198120401712833907).isSome = true := by
  decide +kernel

theorem k2888_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).1 2).2 1).2
      15909465475608606444928372800066490043558733399809878950753813278664526295052784192316).isSome = true := by
  decide +kernel

theorem k2888_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).2 2).1 1).1
      5523545151224675955806272986471669031735234050881762561203863405512794599078541578940477485681547675592986361789871055169221436).isSome = true := by
  decide +kernel

theorem k2888_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).2 2).1 1).2
      1380595734890732048167826135859012606307272625496557569779078354405768685355919597462109973115434679151575431167087820106852924).isSome = true := by
  decide +kernel

theorem k2888_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).2 2).2 1).1
      3961668600003793853597868768308831647805347818802544588350120929491603659405634556732).isSome = true := by
  decide +kernel

theorem k2888_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2888) 3).2 2).2 1).2
      3962921265964604404580955957645736097219117508537813056726231441066094330107030657596).isSome = true := by
  decide +kernel

theorem k2889_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).1 2).1 1).1
      298294116439658307198638401217672791164270183885318924469057008550947183898687143826537949611021534343543356).isSome = true := by
  decide +kernel

theorem k2889_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).1 2).1 1).2
      4771856151124006556784274437611149104313394446725655251574641927466139494667061694881516760118480439193104956).isSome = true := by
  decide +kernel

theorem k2889_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).1 2).2 1).1
      63184177525456861387128449179407978333816445165001236231236225052908423571797404801596).isSome = true := by
  decide +kernel

theorem k2889_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).1 2).2 1).2
      4661435847252005942427776899018482197819434754745914917695346348281013057943016457067967385589468687233596).isSome = true := by
  decide +kernel

theorem k2889_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).2 2).1 1).1
      66036727178564517027164232950635117900268505662263851982034548507466602751556990197946632434).isSome = true := by
  decide +kernel

theorem k2889_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).2 2).1 1).2
      16494789152723517939146231222887754470710745237815768196893394554999039915951383264140587251).isSome = true := by
  decide +kernel

theorem k2889_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).2 2).2 1).1
      1007912422559285169736579175460699010076419107141274193971830238445865955373321574926908).isSome = true := by
  decide +kernel

theorem k2889_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2889) 3).2 2).2 1).2
      251945282982625557006090091881022503981359445003749788512186004115561495182707405290556).isSome = true := by
  decide +kernel

theorem k2890_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).1 2).1 1).1
      296682650855710093611471147350869136757204893302738553046306094170804713106615592414625861949467479341003324).isSome = true := by
  decide +kernel

theorem k2890_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).1 2).1 1).2
      4750865615544061640681314770064377162722498172772787995153635648990131472393517566886618666296616467964542012).isSome = true := by
  decide +kernel

theorem k2890_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).1 2).2 1).1
      251389784097851144242062507486790523643228684257572423522208194297198678107752125428284).isSome = true := by
  decide +kernel

theorem k2890_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).1 2).2 1).2
      62839474318080823702194367653176173269450872801031838214261883455361407868351343868988).isSome = true := by
  decide +kernel

theorem k2890_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).2 2).1 1).1
      74024742058950054342708121298361732937488610948379823964990389693491562813286890058152009923108864045530172).isSome = true := by
  decide +kernel

theorem k2890_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).2 2).1 1).2
      4736939976362746885972449049972071948914902988255640357663152951840838862788795220253886590503089780160117820).isSome = true := by
  decide +kernel

theorem k2890_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).2 2).2 1).1
      13613482821316492149365869438722058634952875006957996069074106645564).isSome = true := by
  decide +kernel

theorem k2890_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2890) 3).2 2).2 1).2
      13598658321964612663164758493902103409741078176677908941561687882812).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2868 2891 :=
  (Cover.one (box := dirCellBox) (n := 2868)
      (.split 2 (.leaf _ k2868_0) (.leaf _ k2868_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2869)
      (.split 2 (.leaf _ k2869_0) (.leaf _ k2869_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2870)
      (.split 2 (.leaf _ k2870_0) (.leaf _ k2870_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 2887)
      (.split 3 (.leaf _ k2887_0) (.split 2 (.split 1 (.leaf _ k2887_1) (.leaf _ k2887_2)) (.leaf _ k2887_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2888)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2888_0) (.leaf _ k2888_1)) (.split 1 (.leaf _ k2888_2) (.leaf _ k2888_3))) (.split 2 (.split 1 (.leaf _ k2888_4) (.leaf _ k2888_5)) (.split 1 (.leaf _ k2888_6) (.leaf _ k2888_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2889)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2889_0) (.leaf _ k2889_1)) (.split 1 (.leaf _ k2889_2) (.leaf _ k2889_3))) (.split 2 (.split 1 (.leaf _ k2889_4) (.leaf _ k2889_5)) (.split 1 (.leaf _ k2889_6) (.leaf _ k2889_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2890)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2890_0) (.leaf _ k2890_1)) (.split 1 (.leaf _ k2890_2) (.leaf _ k2890_3))) (.split 2 (.split 1 (.leaf _ k2890_4) (.leaf _ k2890_5)) (.split 1 (.leaf _ k2890_6) (.leaf _ k2890_7)))))

end C4.Cert.Dir072
