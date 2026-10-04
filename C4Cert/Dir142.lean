module

public import C4Check

public section

/-! Cells `4461 ≤ n < 4488` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir142

theorem k4461_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4461) 2).1 3).1
      71881512168517965215062723799662441774686701925634202561853177560646704183158590967846031109064664413756).isSome = true := by
  decide +kernel

theorem k4461_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4461) 2).1 3).2
      71847953175572300890053629620121538079967516513193164224552699016366095372108446363565529508934577419836).isSome = true := by
  decide +kernel

theorem k4461_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4461) 2).2 3).1
      73613560590146319759131417613444966398039821045795178183147877357539531725374899279840571994148842302206193).isSome = true := by
  decide +kernel

theorem k4461_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4461) 2).2 3).2
      15581621024719254490647189776200868560542740964495323389581832703668579870375635569212).isSome = true := by
  decide +kernel

theorem k4462_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4462) 2).1 3).1
      287353293780558361265258100309481776460564351942774262278170929272211612840180345050722386293994911423036).isSome = true := by
  decide +kernel

theorem k4462_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4462) 2).1 3).2
      3892127129664042508274270193207442061219897436771560442959528950468294890327407283004).isSome = true := by
  decide +kernel

theorem k4462_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4462) 2).2 3).1
      15575206656802499047890431166365768908953883986823740823029043365207205809137678535228).isSome = true := by
  decide +kernel

theorem k4462_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4462) 2).2 3).2
      71806286609975760514487025353538753169016976718394389753932299853217362179754855699168890243354723743292).isSome = true := by
  decide +kernel

theorem k4463_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4463) 2).1
      100022528096461671881580741684189905453715590088943429835796456189428692827138625917526488419830629226446509462726531830835088354441363501585226995).isSome = true := by
  decide +kernel

theorem k4463_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4463) 2).2
      1600504949826948655310659558578168237282397939967995781900050529323715260434806173312168395734449614835999914282883628118061229804472820771155597555).isSome = true := by
  decide +kernel

theorem k4464_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4464) 2).1
      24997801179993744426657595200425958952911976744941143575934969414872183600266411082110658012145005831944909625757772637824967877433942309169648371).isSome = true := by
  decide +kernel

theorem k4464_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4464) 2).2
      338790378548728916924959837706484551615065148789248198232811766421223756211627606166202219735086709059095314814811508020180211).isSome = true := by
  decide +kernel

theorem k4465_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4465) 2).1
      1323246284705343521456632652679844693419287310353227044632601345858333580640050896383983335734761832173020232030746859107827).isSome = true := by
  decide +kernel

theorem k4465_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4465) 2).2
      1354903112686138958695761289447173068349994184672115293429594961185889239766200949694256518107139710168749979326490550694671601).isSome = true := by
  decide +kernel

theorem k4466_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4466) 2).1
      3796286943110628338115463794122980927097653148053446212479652229688246434386369916).isSome = true := by
  decide +kernel

theorem k4466_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4466) 2).2
      4481956602567206484419844713434722345160748469601490690050749651852518698793390252688000435254981940721).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4467 4468 [
    1322625115771832027820111085775628761373354214301851103725306347284645387907235919373277153840232411786771001862874220266866] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4468 4483 [
    51434822122849372890881293066996778222552377118065792960474322, 590371054748943419089, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 157256215005310496346675] = true := by
  decide +kernel

theorem k4483_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4483) 3).1
      1647595840602202330415510813771298390366273432639007265472582738803015986556285583054400925619000481404633506609014821607324202342134620289443060938).isSome = true := by
  decide +kernel

theorem k4483_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4483) 3).2 2).1
      4076949602755300281545097067717328453510813971248393584185673267780170952921751319287603).isSome = true := by
  decide +kernel

theorem k4483_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4483) 3).2 2).2
      3982301892723435168109413965500120405323644645926149588746599149990716512633356293937).isSome = true := by
  decide +kernel

theorem k4484_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4484) 3).1 2).1
      1039543550739203607801469156804207665884249528735921882700143777149456729798133354515418310).isSome = true := by
  decide +kernel

theorem k4484_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4484) 3).1 2).2
      16250111103409330300573988122326600219862767248652997193448357334676061869870027626629938).isSome = true := by
  decide +kernel

theorem k4484_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4484) 3).2 2).1 1).1
      987996414152938852370549870961344155446664743747840227390125295396153925037098630348).isSome = true := by
  decide +kernel

theorem k4484_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4484) 3).2 2).1 1).2
      987916957259147691623922767409687649995056438571428108629625661494823982759017282764).isSome = true := by
  decide +kernel

theorem k4484_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4484) 3).2 2).2
      4046037844801122789796227196984265387032491340726587559953205661543955674087323360654129).isSome = true := by
  decide +kernel

theorem k4485_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4485) 2).1 3).1 1).1
      3942853371544696189712484124949931486467473865261618370825382483033332251860477000908).isSome = true := by
  decide +kernel

theorem k4485_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4485) 2).1 3).1 1).2
      3939821017357133779658089481848841890314557282522322683821915150681688563112125775052).isSome = true := by
  decide +kernel

theorem k4485_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4485) 2).1 3).2 1).1
      213176518205628286747998582010039563684913000477018705463231312588).isSome = true := by
  decide +kernel

theorem k4485_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4485) 2).1 3).2 1).2
      53280800616259097507583369874736946002082813099567411666708984524).isSome = true := by
  decide +kernel

theorem k4485_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4485) 2).2 3).1
      5626994825207986908919091765474662669151665945982707766590315566684444354938633693089351586690822572117392889196744305677592556337).isSome = true := by
  decide +kernel

theorem k4485_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4485) 2).2 3).2
      1403181030490843459294169216210405976129953702955061575659101720915801761366462619061539269823243905425538888930646506794568250161).isSome = true := by
  decide +kernel

theorem k4486_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).1 3).1 1).1
      212718268005217613990572866541029987700454699309617999887958788812).isSome = true := by
  decide +kernel

theorem k4486_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).1 3).1 1).2
      13612418212314562278593301211971239704330856062066216087011721055026).isSome = true := by
  decide +kernel

theorem k4486_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).1 3).2 2).1
      2946036324526374160606141602914545303925287127857).isSome = true := by
  decide +kernel

theorem k4486_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).1 3).2 2).2
      212346182011065566492663093145287414324433492802433300426755918540).isSome = true := by
  decide +kernel

theorem k4486_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4486) 2).2 3).1
      1400244319045199228847827410593518048263627680864634688327679923833075175455789807705742325362495946519443331882276325013110256433).isSome = true := by
  decide +kernel

theorem k4486_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).2 3).2 1).1
      53102647739918009817256862101385512532493138361308766203011265228).isSome = true := by
  decide +kernel

theorem k4486_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4486) 2).2 3).2 1).2
      53093359664504539258746107570995158275465589095764920283762651852).isSome = true := by
  decide +kernel

theorem k4487_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4487) 2).1 3).1
      87221402924021793412390646004546244459332666448665095344635902138769401488804902314741471526866484422594985977978391431303031601).isSome = true := by
  decide +kernel

theorem k4487_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4487) 2).1 3).2
      5445180408785744457816464164106308157368763312465900948845945379102231846139956490717296624484911275034898481311828872274500401).isSome = true := by
  decide +kernel

theorem k4487_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4487) 2).2 3).1
      348985902892195987600849986480612445304559867764730232002031531233980637775995645173965698860675724670652134065371004849648249649).isSome = true := by
  decide +kernel

theorem k4487_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4487) 2).2 3).2
      5446627391670850688890763105386517772443167103803596384450144402873631352345656002499528214454012759293537568533590745601661745).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4461 4488 :=
  (Cover.one (box := dirCellBox) (n := 4461)
      (.split 2 (.split 3 (.leaf _ k4461_0) (.leaf _ k4461_1)) (.split 3 (.leaf _ k4461_2) (.leaf _ k4461_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4462)
      (.split 2 (.split 3 (.leaf _ k4462_0) (.leaf _ k4462_1)) (.split 3 (.leaf _ k4462_2) (.leaf _ k4462_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4463)
      (.split 2 (.leaf _ k4463_0) (.leaf _ k4463_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4464)
      (.split 2 (.leaf _ k4464_0) (.leaf _ k4464_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4465)
      (.split 2 (.leaf _ k4465_0) (.leaf _ k4465_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4466)
      (.split 2 (.leaf _ k4466_0) (.leaf _ k4466_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 4483)
      (.split 3 (.leaf _ k4483_0) (.split 2 (.leaf _ k4483_1) (.leaf _ k4483_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4484)
      (.split 3 (.split 2 (.leaf _ k4484_0) (.leaf _ k4484_1)) (.split 2 (.split 1 (.leaf _ k4484_2) (.leaf _ k4484_3)) (.leaf _ k4484_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4485)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4485_0) (.leaf _ k4485_1)) (.split 1 (.leaf _ k4485_2) (.leaf _ k4485_3))) (.split 3 (.leaf _ k4485_4) (.leaf _ k4485_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4486)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4486_0) (.leaf _ k4486_1)) (.split 2 (.leaf _ k4486_2) (.leaf _ k4486_3))) (.split 3 (.leaf _ k4486_4) (.split 1 (.leaf _ k4486_5) (.leaf _ k4486_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4487)
      (.split 2 (.split 3 (.leaf _ k4487_0) (.leaf _ k4487_1)) (.split 3 (.leaf _ k4487_2) (.leaf _ k4487_3))))

end C4.Cert.Dir142
