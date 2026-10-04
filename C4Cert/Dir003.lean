module

public import C4Check

public section

/-! Cells `904 ≤ n < 989` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir003

theorem k904_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 904) 3).1 2).1 1).1
      243436348646707934690643973938828719549307779872543986505995470951593906847701879155).isSome = true := by
  decide +kernel

theorem k904_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 904) 3).1 2).1 1).2
      3897335065225724692353630632697416903546113188046489698695988853284398722382069765939).isSome = true := by
  decide +kernel

theorem k904_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 904) 3).1 2).2
      1390757351836183559449263733738443755848264198661721297609297698847971870047753890091953574637081989692164010801333890079877473741).isSome = true := by
  decide +kernel

theorem k904_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 904) 3).2 2).1 1).1
      2858863128241263675540859142222261447312888547).isSome = true := by
  decide +kernel

theorem k904_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 904) 3).2 2).1 1).2
      13510968497503629166410022747542130963508691330868333735543951665971).isSome = true := by
  decide +kernel

theorem k904_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 904) 3).2 2).2
      5556488379898892329200500251493123598330166792967855257109995148224185400156849822928557046944692737762543681574212290077659713329).isSome = true := by
  decide +kernel

theorem k905_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 905) 3).1 2).1 1).1
      210890457875920407353699002627154622719381937069057094525291885795).isSome = true := by
  decide +kernel

theorem k905_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 905) 3).1 2).1 1).2
      973992070635645734017449839717987391042222148304005860840598338409892193121119075532).isSome = true := by
  decide +kernel

theorem k905_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 905) 3).1 2).2
      16729644504802396559167175889926756871454139358986022062688042360824027888458230408984248619917).isSome = true := by
  decide +kernel

theorem k905_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 905) 3).2 2).1
      86742432731632155719558593858893726585321271318706689022314685240742840370576956104858229406993567369848595879943742002814209841).isSome = true := by
  decide +kernel

theorem k905_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 905) 3).2 2).2
      63723721415561970624399219553464735372646628394997531350610860718525897231143470858949513).isSome = true := by
  decide +kernel

theorem k906_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 906) 3).1 1).1
      3886437652789545844820840436908369331251097085192704104809616151536687992132408860998).isSome = true := by
  decide +kernel

theorem k906_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 906) 3).1 1).2
      248820744846061963212568988890145644176853069050223521009219002264207959282216056329870).isSome = true := by
  decide +kernel

theorem k906_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 906) 3).2
      1147091631153515527137304283425094016469059627962867628783007753034445181035646241667771096658132068087045).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 907 931 [
    44571799026209342591220173856867961780721926, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k931_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 931) 3).1
      3908059240039153948490764375969030922793092690359398731901884526551906685606893623046).isSome = true := by
  decide +kernel

theorem k931_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 931) 3).2 2).1
      15613306183849969817431882002492008618336831605929576175468943095952393426813895803149).isSome = true := by
  decide +kernel

theorem k931_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 931) 3).2 2).2
      60983626953220174596410702700239537817049816845311286051451283582006030021587804241).isSome = true := by
  decide +kernel

theorem k932_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 932) 3).1 2).1
      15961823031168078684400663851029493682872712183662373383307681287817949458091087017610829).isSome = true := by
  decide +kernel

theorem k932_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 932) 3).1 2).2
      73619008040586452937022512463837889515407872743792408121152367666792076164110485122018608809336723540098381).isSome = true := by
  decide +kernel

theorem k932_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 932) 3).2 1).1
      3991401779162230877126543828149170776517865966823013268935847502120067429350863441892558).isSome = true := by
  decide +kernel

theorem k932_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 932) 3).2 1).2
      5430059671405040894720268954939358127674999721487014859461331197018759989188414153235880700407382414177960095618811987868638002).isSome = true := by
  decide +kernel

theorem k933_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 933) 3).1 1).1
      15935006835711735781133026400005297960901474250018355749236677764744748783108719751557938).isSome = true := by
  decide +kernel

theorem k933_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 933) 3).1 1).2
      996438838251982857413357316651762035107449770586854960589278739862220677285107797947186).isSome = true := by
  decide +kernel

theorem k933_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 933) 3).2 1).1
      3888403154756061026169453177587199467991873793306645148890289617831947213228100540210).isSome = true := by
  decide +kernel

theorem k933_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 933) 3).2 1).2
      4078485619551495430634384225604131140791582737087510855255342966268308226503203000660994866).isSome = true := by
  decide +kernel

theorem k934_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 934) 3).1 2).1
      242997578723460507723640974145288419836876946616772515684664180449042043977384257905).isSome = true := by
  decide +kernel

theorem k934_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 934) 3).1 2).2
      242992401889918312964821218775389430264010012522237946516164908079239028574725986673).isSome = true := by
  decide +kernel

theorem k934_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 934) 3).2
      17921994923687468715364493728129169421078761755142671966945905416778239823597489879114540592743782054481).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 935 959 [
    44570456568276446524247601067892158560292102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem c9 : allCells dirCell 959 960 [
    30370083685399884034012036837944046810120843145277121605890053351759590936360645931006938224467850350163711692559771105727448094722085341557207838639058585317255411651611] = true := by
  decide +kernel

theorem k960_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 960) 3).1 2).1
      974848297050480106750716258028085608146496389308800043651286579190110186890787874225).isSome = true := by
  decide +kernel

theorem k960_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 960) 3).1 2).2
      243719466976948851743617981104315157433869999282363442959674514030363781238472527217).isSome = true := by
  decide +kernel

theorem k960_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 960) 3).2 2).1
      15583954546509430046398249655098580567887768326771400979510480336838365946628194572081).isSome = true := by
  decide +kernel

theorem k960_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 960) 3).2 2).2
      3900270231862148835949236045938612171565946006017466874937538490869216682914502170417).isSome = true := by
  decide +kernel

theorem k961_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 961) 3).1 2).1
      249114340436092259509990045627294861529845566920525782748734594164558444512927032695601).isSome = true := by
  decide +kernel

theorem k961_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 961) 3).1 2).2
      249115474156496157027616859258027353035083535981944238754248209294742534725668543534897).isSome = true := by
  decide +kernel

theorem k961_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 961) 3).2
      409721734870433443237538828696513180440728437946196177934083552860368433399968373304236585550694165400208809631167531243220096394747080423829180931270).isSome = true := by
  decide +kernel

theorem k962_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 962) 3).1
      5418123024650940386754547344260304083554324985625261900762672048531378024809303825871491909790820950839967308709772218416448969).isSome = true := by
  decide +kernel

theorem k962_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 962) 3).2
      60727455500616432581951693809146813897063992195170165188930362826614815413366794641).isSome = true := by
  decide +kernel

theorem c13 : allCells dirCell 963 987 [
    2787465294046253966079610712369005443395846, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem c14 : allCells dirCell 987 988 [
    6424810752517269840088625607329703063428021748075506576610561558603321951365272582920876474996190119216674767561968874254688400849825314127991936135] = true := by
  decide +kernel

theorem k988_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 988) 3).1 2).1
      243723620000489489337997279908027726235198142279499443920264497219263327461847409009).isSome = true := by
  decide +kernel

theorem k988_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 988) 3).1 2).2
      974806264070283984481441169649955844151485113949106416477414057313759641058898596668).isSome = true := by
  decide +kernel

theorem k988_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 988) 3).2 2).1
      3896447368701456051764517291564427005886561978242231513703411232284846516140575987505).isSome = true := by
  decide +kernel

theorem k988_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 988) 3).2 2).2
      974870710509530686488483820270717991198906950521776530644288756061090046802195741756).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 904 989 :=
  (Cover.one (box := dirCellBox) (n := 904)
      (.split 3 (.split 2 (.split 1 (.leaf _ k904_0) (.leaf _ k904_1)) (.leaf _ k904_2)) (.split 2 (.split 1 (.leaf _ k904_3) (.leaf _ k904_4)) (.leaf _ k904_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 905)
      (.split 3 (.split 2 (.split 1 (.leaf _ k905_0) (.leaf _ k905_1)) (.leaf _ k905_2)) (.split 2 (.leaf _ k905_3) (.leaf _ k905_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 906)
      (.split 3 (.split 1 (.leaf _ k906_0) (.leaf _ k906_1)) (.leaf _ k906_2))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 931)
      (.split 3 (.leaf _ k931_0) (.split 2 (.leaf _ k931_1) (.leaf _ k931_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 932)
      (.split 3 (.split 2 (.leaf _ k932_0) (.leaf _ k932_1)) (.split 1 (.leaf _ k932_2) (.leaf _ k932_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 933)
      (.split 3 (.split 1 (.leaf _ k933_0) (.leaf _ k933_1)) (.split 1 (.leaf _ k933_2) (.leaf _ k933_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 934)
      (.split 3 (.split 2 (.leaf _ k934_0) (.leaf _ k934_1)) (.leaf _ k934_2))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 960)
      (.split 3 (.split 2 (.leaf _ k960_0) (.leaf _ k960_1)) (.split 2 (.leaf _ k960_2) (.leaf _ k960_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 961)
      (.split 3 (.split 2 (.leaf _ k961_0) (.leaf _ k961_1)) (.leaf _ k961_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 962)
      (.split 3 (.leaf _ k962_0) (.leaf _ k962_1))).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.one (box := dirCellBox) (n := 988)
      (.split 3 (.split 2 (.leaf _ k988_0) (.leaf _ k988_1)) (.split 2 (.leaf _ k988_2) (.leaf _ k988_3))))

end C4.Cert.Dir003
