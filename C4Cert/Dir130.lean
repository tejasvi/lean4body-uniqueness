module

public import C4Check

public section

/-! Cells `4034 ≤ n < 4039` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir130

theorem k4034_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4034) 3).1
      6253792144403765522037928858955806364990850567).isSome = true := by
  decide +kernel

theorem k4034_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4034) 3).2 2).1 3).1
      15888201867109006417743526492947619078489853578998826394100246011353084151707923825).isSome = true := by
  decide +kernel

theorem k4034_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4034) 3).2 2).1 3).2
      64743818952659061487056511407558490678860816654261503013040540015364816441647636102537).isSome = true := by
  decide +kernel

theorem k4034_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4034) 3).2 2).2
      22025724088972645572028379467184656662400486034977279702919754069322109348122380358337507731472123237283683800978342201349703).isSome = true := by
  decide +kernel

theorem k4035_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).1 2).1 3).1
      257469079524943082152946410546997192739481946067329376024475157837168432679531077444806).isSome = true := by
  decide +kernel

theorem k4035_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).1 2).1 3).2
      65719707314613369160071078871430147507123763844751744638615667003253921747889014118830985).isSome = true := by
  decide +kernel

theorem k4035_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).1 2).2 3).1
      4033005365172381201364546728662120720349760684959312390294850807276664569907029350194).isSome = true := by
  decide +kernel

theorem k4035_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).1 2).2 3).2
      4008003797793129174145238985471592753349257359892838580257256530364957740100912518961).isSome = true := by
  decide +kernel

theorem k4035_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).2 2).1 2).1
      19711045279974488416037182106318779407794987390550060923216686749381328462178453077982513520954603628693577780017).isSome = true := by
  decide +kernel

theorem k4035_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).2 2).1 2).2
      4175416844480651111735616889507168494928700455110235017058691003839991661260751185756236593).isSome = true := by
  decide +kernel

theorem k4035_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).2 2).2 3).1
      16387103408792795006988563207923303169361091675951659199427272596685118579533475670763145).isSome = true := by
  decide +kernel

theorem k4035_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4035) 3).2 2).2 3).2
      19264792895315531838067444804410156068757242760684427527400762881996678268305063938586708381253696187012697905).isSome = true := by
  decide +kernel

theorem k4036_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).1 2).1 1).1
      3969202639428142475132870869856038886579317567535056933881480491841160299873293556428).isSome = true := by
  decide +kernel

theorem k4036_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).1 2).1 1).2
      15849265711175652350889076629309166290544601077347375211419754267899384348848600045363).isSome = true := by
  decide +kernel

theorem k4036_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).1 2).2
      19626546026920969883069260542201441553635068638702710547183094269613873713553388602531655237642673592732361411377).isSome = true := by
  decide +kernel

theorem k4036_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).2 2).1 1).1
      3950707326417426443181909618877249873439250802390755319681855745429924077433494428364).isSome = true := by
  decide +kernel

theorem k4036_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).2 2).1 1).2
      15782259079832069798894156921810803213189344427149305215213725574450604331353126034995).isSome = true := by
  decide +kernel

theorem k4036_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).2 2).2 1).1
      11880686209527786315748000753569858156223748213555).isSome = true := by
  decide +kernel

theorem k4036_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).1 3).2 2).2 1).2
      3346468861656093856371768202363831826985505851336580116230039244).isSome = true := by
  decide +kernel

theorem k4036_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4036) 2).2 3).1 2).1
      17029193394422497222950325729959280327636343182823822395266649008033325160996440348442167684301).isSome = true := by
  decide +kernel

theorem k4036_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4036) 2).2 3).1 2).2
      4062463932723877696444180980881577054332446307244680780306240407027145541917485739395889).isSome = true := by
  decide +kernel

theorem k4036_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).2 3).2 2).1 1).1
      742808299494454958590621680231298159547939775283).isSome = true := by
  decide +kernel

theorem k4036_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4036) 2).2 3).2 2).1 1).2
      185633502787377301863213974125115550784226741043).isSome = true := by
  decide +kernel

theorem k4036_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4036) 2).2 3).2 2).2
      66316095562261368158691584704720714121873844457207802492011072512679685765254606552347282637).isSome = true := by
  decide +kernel

theorem k4037_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).1 3).1 2).1
      351041931560951991228781787026574189414572617267160984798563692036202355940941759281590526287892992723465960479703481222801812273).isSome = true := by
  decide +kernel

theorem k4037_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).1 3).1 2).2
      87796372007749923752899877274959643102266460339006747717547245323783380251080249500129792426376923719103479725873187547160406833).isSome = true := by
  decide +kernel

theorem k4037_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).1 3).2 2).1
      296550563194442655702048037545899166171037127154593736323426003056696289830266314422390033579997540417895217).isSome = true := by
  decide +kernel

theorem k4037_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).1 3).2 2).2
      4020453975446877310320424933831928693015345856715848893005764945152139402702774928304945).isSome = true := by
  decide +kernel

theorem k4037_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).2 3).1 2).1
      21957007123732202227614059727839884750876037099204963338027020951383874775365773783827118959416923116330181375319125158402693937).isSome = true := by
  decide +kernel

theorem k4037_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).2 3).1 2).2
      4762702548397730664435915210388973287768122766811196074262570300891685704578429957082181623658670040545110833).isSome = true := by
  decide +kernel

theorem k4037_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).2 3).2 1).1
      257545512946472289273090347211618041488462798657484999139200784258965663252468779138538290).isSome = true := by
  decide +kernel

theorem k4037_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4037) 2).2 3).2 1).2
      257475676584653832540671534305667644055342550736401965869745881080662758730550150836116274).isSome = true := by
  decide +kernel

theorem k4038_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).1 3).1 1).1
      296383024300041156048571136788737465570471734320097720807581764888462734949838316243965594311358804848639154).isSome = true := by
  decide +kernel

theorem k4038_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).1 3).1 1).2
      4012011514934110306713191102372161565487656487651047052929892848328295590067957096934578).isSome = true := by
  decide +kernel

theorem k4038_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).1 3).2 1).1
      5458014649627636479207486601580036569194827656691832852990680605429927621590784935383401804714629148815332075691699929928888892).isSome = true := by
  decide +kernel

theorem k4038_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).1 3).2 1).2
      250343221731256153168861529958164808688743344104248816245960709967601560097564380060850).isSome = true := by
  decide +kernel

theorem k4038_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).2 3).1 1).1
      1003803189653651142945551190043940390850089935573879561454588973267641851543504037452594).isSome = true := by
  decide +kernel

theorem k4038_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).2 3).1 1).2
      1003584418564634345301432919792604166117040965392687722831503194648370592499998999026482).isSome = true := by
  decide +kernel

theorem k4038_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).2 3).2 1).1
      1002039586279732647602504975133824908973704187612842620256950035801757946378212421770034).isSome = true := by
  decide +kernel

theorem k4038_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4038) 2).2 3).2 1).2
      1001869749853967079946234026789152904792010873291638918723645568073413493710662489971506).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4034 4039 :=
  (Cover.one (box := dirCellBox) (n := 4034)
      (.split 3 (.leaf _ k4034_0) (.split 2 (.split 3 (.leaf _ k4034_1) (.leaf _ k4034_2)) (.leaf _ k4034_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4035)
      (.split 3 (.split 2 (.split 3 (.leaf _ k4035_0) (.leaf _ k4035_1)) (.split 3 (.leaf _ k4035_2) (.leaf _ k4035_3))) (.split 2 (.split 2 (.leaf _ k4035_4) (.leaf _ k4035_5)) (.split 3 (.leaf _ k4035_6) (.leaf _ k4035_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4036)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k4036_0) (.leaf _ k4036_1)) (.leaf _ k4036_2)) (.split 2 (.split 1 (.leaf _ k4036_3) (.leaf _ k4036_4)) (.split 1 (.leaf _ k4036_5) (.leaf _ k4036_6)))) (.split 3 (.split 2 (.leaf _ k4036_7) (.leaf _ k4036_8)) (.split 2 (.split 1 (.leaf _ k4036_9) (.leaf _ k4036_10)) (.leaf _ k4036_11))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4037)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4037_0) (.leaf _ k4037_1)) (.split 2 (.leaf _ k4037_2) (.leaf _ k4037_3))) (.split 3 (.split 2 (.leaf _ k4037_4) (.leaf _ k4037_5)) (.split 1 (.leaf _ k4037_6) (.leaf _ k4037_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4038)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4038_0) (.leaf _ k4038_1)) (.split 1 (.leaf _ k4038_2) (.leaf _ k4038_3))) (.split 3 (.split 1 (.leaf _ k4038_4) (.leaf _ k4038_5)) (.split 1 (.leaf _ k4038_6) (.leaf _ k4038_7)))))

end C4.Cert.Dir130
