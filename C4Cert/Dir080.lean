module

public import C4Check

public section

/-! Cells `3138 ≤ n < 3139` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir080

theorem k3138_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 3).1 1).1
      1045138381025277009325630538043765295975143341380959668078471095508674967067492830509233).isSome = true := by
  decide +kernel

theorem k3138_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 3).1 1).2
      1043389300758714224073118875095524425658691500299478186176101714517104946232312646170801).isSome = true := by
  decide +kernel

theorem k3138_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 3).2 1).1
      16613639266927219470403634868556885651008550971214854640731419779772813346358367179104945).isSome = true := by
  decide +kernel

theorem k3138_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 3).2 1).2
      64874351895290943274944929561130636887097835679927379340674955610467675413906365701298).isSome = true := by
  decide +kernel

theorem k3138_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 3).1 1).1
      1048503226423042175792466075592888504486998937696081860347489477810899089409333346007217).isSome = true := by
  decide +kernel

theorem k3138_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 3).1 1).2
      261674749869794912500642404836835524209424780042343622564479413202091602071233404696753).isSome = true := by
  decide +kernel

theorem k3138_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 3).2 1).1
      1041989996435181687958053398724211813270431184667723676271843839280550408978653331255868).isSome = true := by
  decide +kernel

theorem k3138_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 3).2 1).2
      14091794922798235138587003198210140914061124305971846101156335492273).isSome = true := by
  decide +kernel

theorem k3138_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).1 3).1 1).1
      16149456195771504081496010248054039782835542645960674610888097273681356639899320974764).isSome = true := by
  decide +kernel

theorem k3138_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).1 3).1 1).2
      54629113658159829743840663630561331796432564395804151151747003052).isSome = true := by
  decide +kernel

theorem k3138_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).1 3).2 1).1
      1004692463275906378815913135706413259671862311809775333565950166846359052645642402220).isSome = true := by
  decide +kernel

theorem k3138_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).1 3).2 1).2
      250845479727919427299333060371722174682962729999195540009864756001183682812661930417).isSome = true := by
  decide +kernel

theorem k3138_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).2 3).1 1).1
      259007572074518532123534588614199375459636300037748991838096862267903178546192387142204).isSome = true := by
  decide +kernel

theorem k3138_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).2 3).1 1).2
      13692488308772533918175241744275615940248665217393931619418078380).isSome = true := by
  decide +kernel

theorem k3138_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).2 3).2 1).1
      218295605695069044793574088028318262810565002427805580162225398444).isSome = true := by
  decide +kernel

theorem k3138_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).2 3).2 1).2
      13627437508130456565923799911380442236801260943602833740187401388).isSome = true := by
  decide +kernel

theorem k3138_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).1 3).1
      65761523295848476847629024362162398276991014920773317628106727978897431553451962530988).isSome = true := by
  decide +kernel

theorem k3138_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).1 3).2
      16327325003089175508111405026935766961124698955480306634800878266995554680712904671020).isSome = true := by
  decide +kernel

theorem k3138_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).2 3).1
      774629305841195874275422031294165199008024453809).isSome = true := by
  decide +kernel

theorem k3138_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).2 3).2
      16368228305340576817470739685247002753636494300018688542594900702268233978356208336684).isSome = true := by
  decide +kernel

theorem k3138_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).2 2).1 3).1
      4103245146818323807660181961666522439985011588647789917925209352116746376303171039020).isSome = true := by
  decide +kernel

theorem k3138_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).2 2).1 3).2
      14130771575433332587042934794055201366054076167627742264125548960945).isSome = true := by
  decide +kernel

theorem k3138_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).2 2).2 3).1
      4112342558569551050360495121228751267329163144997664760835898243118173941805150689073).isSome = true := by
  decide +kernel

theorem k3138_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).2 2).2 3).2
      4083587304754367261349168035147929729079252834585360391471295431924940911066403723057).isSome = true := by
  decide +kernel

theorem k3138_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).1 3).1 1).1
      14074474183296615625373861919555466699594274839212781958137764373052).isSome = true := by
  decide +kernel

theorem k3138_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).1 3).1 1).2
      11898380779756549081660181960692309622559447217).isSome = true := by
  decide +kernel

theorem k3138_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).1 3).2 1).1
      218809751329027985744206443620286539330564200481741105761609048636).isSome = true := by
  decide +kernel

theorem k3138_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).1 3).2 1).2
      11839646666133132688516758581699275161857611953).isSome = true := by
  decide +kernel

theorem k3138_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).2 3).1 1).1
      220441471763826616283437611643932433790770858354027789866449202988).isSome = true := by
  decide +kernel

theorem k3138_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).2 3).1 1).2
      3443341498479978044159795809781817749225156574504841086663810860).isSome = true := by
  decide +kernel

theorem k3138_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).2 3).2 1).1
      190195390128604111081940224744829401024735994428).isSome = true := by
  decide +kernel

theorem k3138_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 2).2 3).2 1).2
      3422244087518120786483777984254701866124239548352189493151162156).isSome = true := by
  decide +kernel

theorem k3138_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 2).1 3).1
      102833952003381343538266554155886266536766771016603504562158934538951974226618437626576285307224642848534835021304188786648685666146424364906964657).isSome = true := by
  decide +kernel

theorem k3138_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 2).1 3).2
      347317062364458184990140635619551703322108724572626817052877141829158427259628093114736536700206528144898473091440884526212785).isSome = true := by
  decide +kernel

theorem k3138_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 2).2 1).1
      22285291041961322394657568362096548950520294788999345056643315513700008755447330203027242165272829255794743045503655433623434931).isSome = true := by
  decide +kernel

theorem k3138_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 2).2 1).2
      25671731615404152056813834589284221847213872942953170004954313951140661270453396487748275731999363512070257950835154822110796374859337232656465331).isSome = true := by
  decide +kernel

theorem k3138_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 2).1 1).1
      75007863275885418317348844476114123411080904129934611145255669278708254353037791708534668945361928998741683).isSome = true := by
  decide +kernel

theorem k3138_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 2).1 1).2
      1171880376389727000382459008156337504421406823371043833855879320199660765349121908387571844340986225779953).isSome = true := by
  decide +kernel

theorem k3138_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 2).2 1).1
      1385468490827654812899001118691612819551229662327706444506504526832837530132385450841990991671216767984150139590183836562351795).isSome = true := by
  decide +kernel

theorem k3138_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 2).2 1).2
      21628237645059310435599331528910307872350562246891973681026861896589804356015234642397697504635391777350924460769296702397875).isSome = true := by
  decide +kernel

theorem k3138_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 2).1 3).1 1).1
      54462407959623559087293550682093725069060312998791983787747440812).isSome = true := by
  decide +kernel

theorem k3138_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 2).1 3).1 1).2
      13600233168347701609562542290011853365992516640010617879541677228).isSome = true := by
  decide +kernel

theorem k3138_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 2).1 3).2
      1394149832727741565376629586764642181514893516348579806938801193477636115617294887261389037547351351969557488389785755266180785).isSome = true := by
  decide +kernel

theorem k3138_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 2).2 3).1
      1244812742154375433452831442784058526398961568377317133081724528030013587679951167106764445002800741397977473733).isSome = true := by
  decide +kernel

theorem k3138_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 2).2 3).2
      1050341957819399478709353938153240640933014130836789607738321553340920140175018492816646833).isSome = true := by
  decide +kernel

theorem k3138_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 2).1 1).1
      1388728851756874916689766177416583512945092082454228938909627374234265302611410555783418812916023438649387025049832100382238387).isSome = true := by
  decide +kernel

theorem k3138_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 2).1 1).2
      21657852882489018359601153796913734693101920256595957861421980306229261419201824551560281175500006566844126274746825019317683).isSome = true := by
  decide +kernel

theorem k3138_47 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 2).2 1).1
      5562465595508319231166166579596683854676522155757205508866103067960188025462106235174082741547513804991110386874327601385957041).isSome = true := by
  decide +kernel

theorem k3138_48 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 2).2 1).2
      18811989746129633816719309014610926726042765360609453915688106134611489754929209470640783852971314735577523).isSome = true := by
  decide +kernel

theorem k3138_49 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).1 2).1
      68809662218859238123865986575939204756675430602327437730998752804726447274216434590514803379).isSome = true := by
  decide +kernel

theorem k3138_50 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).1 2).2
      17239291212171336596063411226542104284323127538376369681259373590864949942578492028556397235).isSome = true := by
  decide +kernel

theorem k3138_51 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).2 2).1
      19805995409573132344374002917193786685501393888320291218821760304762533643030339139873177923347043260070932275).isSome = true := by
  decide +kernel

theorem k3138_52 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).2 2).2
      1240363720215376191600018067506363882883098710882372745959407007234416420565324387622925261741043205788819251).isSome = true := by
  decide +kernel

theorem k3138_53 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).1 2).1
      77645281198335959038427004854116182403007489607922375932653561087389876710159224244932942447108977111169459).isSome = true := by
  decide +kernel

theorem k3138_54 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).1 2).2
      19487619995033989409515627240480295701278838975063869545758321767535728551090578405084800705060928305798579).isSome = true := by
  decide +kernel

theorem k3138_55 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).2 2).1
      1244451414587336857248221313959510141706061538780687240632176316225300693645274008502574153783189069283031857).isSome = true := by
  decide +kernel

theorem k3138_56 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).2 2).2
      19419972755875235590540150206239312626007668409253836390271484581410614212390238086490170416631936148397875).isSome = true := by
  decide +kernel

theorem k3138_57 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 2).1 1).1 3).1
      2994519034581324683283973396710545943557668396).isSome = true := by
  decide +kernel

theorem k3138_58 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 2).1 1).1 3).2
      47649656077075063266034177584508607712873347132).isSome = true := by
  decide +kernel

theorem k3138_59 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 2).1 1).2
      90294503723878854670354145899725361146665206664141892453765033116874023703831188361556265795105676706849711411679580707062643891).isSome = true := by
  decide +kernel

theorem k3138_60 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 2).2 1).1
      266195268716788410664792962338336655338152040116728671033413537791600908130426362511588531).isSome = true := by
  decide +kernel

theorem k3138_61 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 2).2 1).2
      78426244509218200115387984517484563221902478645479809294308811712161550367257036549246754121780443660174122803).isSome = true := by
  decide +kernel

theorem k3138_62 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).1 2).1
      1066724154016668043376656783004157114624978444865920197340502530750598436942248694321115827).isSome = true := by
  decide +kernel

theorem k3138_63 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).1 2).2
      4173699193800721782748300525562824129834381881839067646396250103470883863125453324018355).isSome = true := by
  decide +kernel

theorem k3138_64 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).2 2).1
      307134872865508278106129746005279407926672758889068542347408653275313562713356244253847609137136667358292787).isSome = true := by
  decide +kernel

theorem k3138_65 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).2 2).2
      1042182569337794411510358337528695697793889241384723396965258362333700775874125422762803).isSome = true := by
  decide +kernel

theorem k3138_66 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 2).1 3).1
      311819124162085752689337436333881287020578070235834841360348061970584925406763662889466174614604235483282917617).isSome = true := by
  decide +kernel

theorem k3138_67 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 2).1 3).2
      16835828228097361168747318248903452224172546156533230803029948122323695225951627802565921009).isSome = true := by
  decide +kernel

theorem k3138_68 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 2).2 3).1
      67703902461355986872049522339699108142059424960633759927040826035622791120683871679681065201).isSome = true := by
  decide +kernel

theorem k3138_69 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 2).2 3).2
      1053927006708525135592198982581266661794445852197294603943942957926321010549860298842829041).isSome = true := by
  decide +kernel

theorem k3138_70 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 2).1 1).1
      65389144072488158124028638064729236090214430211365844157880396186659632200980610843796147).isSome = true := by
  decide +kernel

theorem k3138_71 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 2).1 1).2
      885346567974286818309403186064098475715282457172442214764953791226547).isSome = true := by
  decide +kernel

theorem k3138_72 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 2).2 1).1
      261958078782709983351723983125946933202652629987938084104652960665686420996049388487543027).isSome = true := by
  decide +kernel

theorem k3138_73 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 2).2 1).2
      4089345271859706245150204066848438868840413347995452038559343749283214332558228161657011).isSome = true := by
  decide +kernel

theorem k3138_74 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 2).1 1).1
      1057010374160645252673406326175825958029823259331428040222654623663564263959622036023246003).isSome = true := by
  decide +kernel

theorem k3138_75 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 2).1 1).2
      4221202505345046313115346267377507013992928672181061625194858344730268280914176317963234481).isSome = true := by
  decide +kernel

theorem k3138_76 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 2).2 1).1
      264655070687281550114654878117485165181047659532545262100615652615740766051223733638102195).isSome = true := by
  decide +kernel

theorem k3138_77 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 2).2 1).2
      305308811601852232324170112521912776331163456913550700719153930446300982263212698314284411264655888878034737).isSome = true := by
  decide +kernel

theorem k3138_78 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 2).1 1).1
      1049378993072159110886043349641013372309966908819584197477670076819299803266961081717092595).isSome = true := by
  decide +kernel

theorem k3138_79 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 2).1 1).2
      1025153325513718864343500465369980811342109810101060710182987673001997507220546609576113).isSome = true := by
  decide +kernel

theorem k3138_80 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 2).2 1).1
      4203798053159920497903111550280931679799363059631911882122822087135156030182306117532905715).isSome = true := by
  decide +kernel

theorem k3138_81 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 2).2 1).2
      4106574871667989253800926805235865332670590103540017781185297340470084426078165990226097).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3138 3139 :=
  (Cover.one (box := dirCellBox) (n := 3138)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3138_0) (.leaf _ k3138_1)) (.split 1 (.leaf _ k3138_2) (.leaf _ k3138_3))) (.split 3 (.split 1 (.leaf _ k3138_4) (.leaf _ k3138_5)) (.split 1 (.leaf _ k3138_6) (.leaf _ k3138_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3138_8) (.leaf _ k3138_9)) (.split 1 (.leaf _ k3138_10) (.leaf _ k3138_11))) (.split 3 (.split 1 (.leaf _ k3138_12) (.leaf _ k3138_13)) (.split 1 (.leaf _ k3138_14) (.leaf _ k3138_15))))) (.split 3 (.split 1 (.split 2 (.split 3 (.leaf _ k3138_16) (.leaf _ k3138_17)) (.split 3 (.leaf _ k3138_18) (.leaf _ k3138_19))) (.split 2 (.split 3 (.leaf _ k3138_20) (.leaf _ k3138_21)) (.split 3 (.leaf _ k3138_22) (.leaf _ k3138_23)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3138_24) (.leaf _ k3138_25)) (.split 1 (.leaf _ k3138_26) (.leaf _ k3138_27))) (.split 3 (.split 1 (.leaf _ k3138_28) (.leaf _ k3138_29)) (.split 1 (.leaf _ k3138_30) (.leaf _ k3138_31)))))) (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3138_32) (.leaf _ k3138_33)) (.split 1 (.leaf _ k3138_34) (.leaf _ k3138_35))) (.split 2 (.split 1 (.leaf _ k3138_36) (.leaf _ k3138_37)) (.split 1 (.leaf _ k3138_38) (.leaf _ k3138_39)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3138_40) (.leaf _ k3138_41)) (.leaf _ k3138_42)) (.split 3 (.leaf _ k3138_43) (.leaf _ k3138_44))) (.split 2 (.split 1 (.leaf _ k3138_45) (.leaf _ k3138_46)) (.split 1 (.leaf _ k3138_47) (.leaf _ k3138_48)))))) (.split 3 (.split 3 (.split 2 (.split 1 (.split 2 (.leaf _ k3138_49) (.leaf _ k3138_50)) (.split 2 (.leaf _ k3138_51) (.leaf _ k3138_52))) (.split 1 (.split 2 (.leaf _ k3138_53) (.leaf _ k3138_54)) (.split 2 (.leaf _ k3138_55) (.leaf _ k3138_56)))) (.split 2 (.split 2 (.split 1 (.split 3 (.leaf _ k3138_57) (.leaf _ k3138_58)) (.leaf _ k3138_59)) (.split 1 (.leaf _ k3138_60) (.leaf _ k3138_61))) (.split 1 (.split 2 (.leaf _ k3138_62) (.leaf _ k3138_63)) (.split 2 (.leaf _ k3138_64) (.leaf _ k3138_65))))) (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3138_66) (.leaf _ k3138_67)) (.split 3 (.leaf _ k3138_68) (.leaf _ k3138_69))) (.split 2 (.split 1 (.leaf _ k3138_70) (.leaf _ k3138_71)) (.split 1 (.leaf _ k3138_72) (.leaf _ k3138_73)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3138_74) (.leaf _ k3138_75)) (.split 1 (.leaf _ k3138_76) (.leaf _ k3138_77))) (.split 2 (.split 1 (.leaf _ k3138_78) (.leaf _ k3138_79)) (.split 1 (.leaf _ k3138_80) (.leaf _ k3138_81))))))))

end C4.Cert.Dir080
