module

public import C4Check

public section

/-! Cells `2805 ≤ n < 2808` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir066

theorem k2805_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 3).1 2).1
      1401710575392490248181502627253096363884981716793992350979726631816439683668615062203652448161630553090129581103967748864951810865).isSome = true := by
  decide +kernel

theorem k2805_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 3).1 2).2
      1402684288240874750863893494610302849932655228117868173057982111501009108184371542226800442362208533727108221948631034056354134833).isSome = true := by
  decide +kernel

theorem k2805_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 3).2 1).1
      1005100026312146000651787687396409077358437479546438677264892118010360648653631791405874).isSome = true := by
  decide +kernel

theorem k2805_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 3).2 1).2
      1400855945581180102562088606861993397896443906302703964565586075111740764800700290624232446350545657543491143327603630472119578866).isSome = true := by
  decide +kernel

theorem k2805_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).1 3).1
      1003834546147855321075486936403674636260368571499162234257362753437459292383377935932210).isSome = true := by
  decide +kernel

theorem k2805_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).1 3).2
      1003576115804510119338597567023237622394019884500383800530870344651280653146341535854284).isSome = true := by
  decide +kernel

theorem k2805_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).2 3).1
      18954824069045860647599227573643146713618461480122173585478880276062843994286649408472212591760407959844928572).isSome = true := by
  decide +kernel

theorem k2805_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).2 3).2
      250861071280436928992107827049273347234215860074211110340253348801424620420251350531132).isSome = true := by
  decide +kernel

theorem k2805_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 3).1 1).1
      304545858697956703081692665962576306016615361770639493843198804345207928777690477573461634436055994977742322482).isSome = true := by
  decide +kernel

theorem k2805_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 3).1 1).2 2).1
      213243680643458508656861787412563856179145642386479121262615915580).isSome = true := by
  decide +kernel

theorem k2805_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 3).1 1).2 2).2
      740185366938495221467752277545553515604677409852).isSome = true := by
  decide +kernel

theorem k2805_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 3).2 1).1
      4024649899102127158848550229406096060063362962098090569323238174611298908725339428330290).isSome = true := by
  decide +kernel

theorem k2805_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 3).2 1).2
      4865589237885940247209919769349141231666360730470689585911021316604297022681354839622956635504027981069140291826).isSome = true := by
  decide +kernel

theorem k2805_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 3).1 1).1
      1004868681592728070890068367160134955184924777341027076913481482695940571256745824459570).isSome = true := by
  decide +kernel

theorem k2805_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 3).1 1).2
      1185858209719164456380041535329171026075946391392097919814729415649395263450605356142642650993005694335237180).isSome = true := by
  decide +kernel

theorem k2805_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 3).2 1).1
      1003527157984162293336231554813571257422630839377707728162953254151232107902157073100492).isSome = true := by
  decide +kernel

theorem k2805_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 3).2 1).2
      18510117875366052491713575379476138319390761095981326221022851635073360109623094377713812075505931469569084).isSome = true := by
  decide +kernel

theorem k2806_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).1 3).1
      250435398949284672238654344801895331194283036894272057466339566824097099316929792621628).isSome = true := by
  decide +kernel

theorem k2806_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).1 3).2
      3910234419748045191115758386982254199788951062828068269512453904684709274898283458252).isSome = true := by
  decide +kernel

theorem k2806_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).2 3).1
      15650053881626679684428493666390039790659115866526434373615784337458309380619754126396).isSome = true := by
  decide +kernel

theorem k2806_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).2 3).2
      52984416812076089710552584536854211768144498937476184765500865596).isSome = true := by
  decide +kernel

theorem k2806_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).2 1).1
      1393591875257115909800937756763110171566287455116504315184510795625726133731249059797665208828380178471772747055180888042431655731).isSome = true := by
  decide +kernel

theorem k2806_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).2 1).2
      87081907243283156166386853980437056185571474093069521533287445054322131007997547335359440977102187621484338193137263157851028659).isSome = true := by
  decide +kernel

theorem k2806_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 3).1 1).1
      15665165805893360420839593251150944434845688943877700252337987216602090572011746472908).isSome = true := by
  decide +kernel

theorem k2806_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 3).1 1).2
      62652397550028456660285612673249075460690631716848144178748161804873654350940766846012).isSome = true := by
  decide +kernel

theorem k2806_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 3).2 1).1
      3913019713424843635288662793847996509665379073611749367629576938713985478747420718028).isSome = true := by
  decide +kernel

theorem k2806_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 3).2 1).2
      15649618206671511583238264709953479168598610683997579769161838058146534806317212482620).isSome = true := by
  decide +kernel

theorem k2806_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).2 1).1 3).1
      977555172335935118114021151324992918654514815886148158028194413725856992061097402060).isSome = true := by
  decide +kernel

theorem k2806_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).2 1).1 3).2
      52957259716105003494023438998690852386659729828060060880734740172).isSome = true := by
  decide +kernel

theorem k2806_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).2 1).2 2).1
      53008382001906898648935023537682345299176177746023064275754807868).isSome = true := by
  decide +kernel

theorem k2806_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).2 1).2 2).2
      52972291020870110876328331482289833637012304391366990575752821820).isSome = true := by
  decide +kernel

theorem k2807_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).1 3).1 1).1
      73765801339938461280397736278602902298330857451949454344769821070439492828426834723715013307312682791493427).isSome = true := by
  decide +kernel

theorem k2807_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).1 3).1 1).2
      73758253684501616845095374484277974700708830141018092362248439058803598176775144469882772055516034635496627).isSome = true := by
  decide +kernel

theorem k2807_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).1 3).2 1).1
      3898453010696469824553476199755869755785506560066968215165037851239210349179865847603).isSome = true := by
  decide +kernel

theorem k2807_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).1 3).2 1).2
      62370590723842524183577143264752217941409371330737531989657342580098875251076204551347).isSome = true := by
  decide +kernel

theorem k2807_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).2 3).1 1).1
      63945035232067092500793359774296018176855809607099858076664321135715775428766302388834099).isSome = true := by
  decide +kernel

theorem k2807_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).2 3).1 1).2
      348266141730632826030827326992972826039646140807269787725311502640208124289375551831150358494904667742006487575372019144261729458).isSome = true := by
  decide +kernel

theorem k2807_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).2 3).2 1).1
      998290636288448873956563425524900633697132250542517328331784491970420961580052693752627).isSome = true := by
  decide +kernel

theorem k2807_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2807) 2).2 3).2 1).2
      73728964175950774788437644427236822234129192115667992863428932551238604953495057267098555400987598086831283).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2805 2808 :=
  (Cover.one (box := dirCellBox) (n := 2805)
      (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2805_0) (.leaf _ k2805_1)) (.split 1 (.leaf _ k2805_2) (.leaf _ k2805_3))) (.split 1 (.split 3 (.leaf _ k2805_4) (.leaf _ k2805_5)) (.split 3 (.leaf _ k2805_6) (.leaf _ k2805_7)))) (.split 3 (.split 3 (.split 1 (.leaf _ k2805_8) (.split 2 (.leaf _ k2805_9) (.leaf _ k2805_10))) (.split 1 (.leaf _ k2805_11) (.leaf _ k2805_12))) (.split 3 (.split 1 (.leaf _ k2805_13) (.leaf _ k2805_14)) (.split 1 (.leaf _ k2805_15) (.leaf _ k2805_16)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2806)
      (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ k2806_0) (.leaf _ k2806_1)) (.split 3 (.leaf _ k2806_2) (.leaf _ k2806_3))) (.split 1 (.leaf _ k2806_4) (.leaf _ k2806_5))) (.split 3 (.split 3 (.split 1 (.leaf _ k2806_6) (.leaf _ k2806_7)) (.split 1 (.leaf _ k2806_8) (.leaf _ k2806_9))) (.split 1 (.split 3 (.leaf _ k2806_10) (.leaf _ k2806_11)) (.split 2 (.leaf _ k2806_12) (.leaf _ k2806_13)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2807)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2807_0) (.leaf _ k2807_1)) (.split 1 (.leaf _ k2807_2) (.leaf _ k2807_3))) (.split 3 (.split 1 (.leaf _ k2807_4) (.leaf _ k2807_5)) (.split 1 (.leaf _ k2807_6) (.leaf _ k2807_7)))))

end C4.Cert.Dir066
