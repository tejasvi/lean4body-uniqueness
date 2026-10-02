module

public import C4Check

public section

/-! Cells `2411 ≤ n < 2413` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir043

theorem k2411_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).1
      22000981313487696478632817606476594270638472383554339833885559947764626181286921253071376510961322983705460078215330050065478).isSome = true := by
  decide +kernel

theorem k2411_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).2
      476694570780817374101639946079298005330423219688370523975060674981886221919512466365842970333625448936011711748528746649790947600983966026085566548460673928399717830).isSome = true := by
  decide +kernel

theorem k2411_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).1
      1376908426112487917556002055277212922355867900150693542434694154693472344367276306671522177462604610233585766715480331216241).isSome = true := by
  decide +kernel

theorem k2411_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).2
      5477186035644106019829595726092304022884729070899981879225630154589592317198931966906275993407712663132230525084807942537545).isSome = true := by
  decide +kernel

theorem k2411_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 1).1
      3905942567535707283796021157730882825937439358974064165438312861034957259436416380).isSome = true := by
  decide +kernel

theorem k2411_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 1).2
      999968819538893741726063944672556812792244325383136846197386542329104649180053461426).isSome = true := by
  decide +kernel

theorem k2411_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).2
      6550666550745385160609472765220724157881722817504930843324548900196797056959527717717776895766334929354436859201335588270549646877308091054053750001).isSome = true := by
  decide +kernel

theorem k2411_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 2).1
      25630841471584010926410064286921061341428276973348452024973980107040453313605258922557273586456861592903622314182394538853957782920583036088186355).isSome = true := by
  decide +kernel

theorem k2411_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 2).2
      6423719929879103232410696783035602717927762672309812051932086543051472049995906045493087034436476170617754050634355764405940090795671431093515761).isSome = true := by
  decide +kernel

theorem k2412_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).1
      1632426498624115376372563030929025219134752797865606002586714654869000882199014778236484872814553431386021087793275709878474748642937035131239101681).isSome = true := by
  decide +kernel

theorem k2412_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).2
      88223354529526470040182555787558982387678330096771666940706058227797384979379142230685980270047513014187484189669247016264637873).isSome = true := by
  decide +kernel

theorem k2412_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).1
      346453364403578152559800943273955018401681447672728749770551587407044016600245182850183160001151413262417932614866280894788850).isSome = true := by
  decide +kernel

theorem k2412_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).2
      345478858067755448871315991463248022397034750536095842224150468714196091052326040235746148245657021960893625565687811013702898).isSome = true := by
  decide +kernel

theorem k2412_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).1
      4771828106178506967935941683226141954364017868314949910485952143432467570732783125536903464239814842605007537).isSome = true := by
  decide +kernel

theorem k2412_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).2
      1190706228530449763451732015858773580651267331068619669689991741429479146199122069506643603086865975485242545).isSome = true := by
  decide +kernel

theorem k2412_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 1).1
      4657043820016168315884151023145113660934731436906685541301346615248721824884912464134405209380014418058675).isSome = true := by
  decide +kernel

theorem k2412_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 1).2
      76385481909651876295006223345131556172766467154731294992185288966290716220971560657342364368684485741236921148).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2411 2413 :=
  (Cover.one (box := dirCellBox) (n := 2411)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2411_0) (.leaf _ k2411_1)) (.split 3 (.leaf _ k2411_2) (.leaf _ k2411_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k2411_4) (.leaf _ k2411_5)) (.leaf _ k2411_6)) (.split 2 (.leaf _ k2411_7) (.leaf _ k2411_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2412)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2412_0) (.leaf _ k2412_1)) (.split 3 (.leaf _ k2412_2) (.leaf _ k2412_3))) (.split 2 (.split 3 (.leaf _ k2412_4) (.leaf _ k2412_5)) (.split 1 (.leaf _ k2412_6) (.leaf _ k2412_7)))))

end C4.Cert.Dir043
