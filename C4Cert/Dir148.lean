module

public import C4Check

public section

/-! Cells `4692 ≤ n < 4851` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir148

theorem c0 : allCells dirCell 4692 4696 [
    43573072419362349228085405151359593739868, 43565959175490349269538573653797786857052,
    43560446801925938493987299216882926551900, 43556171128004687208029616143967156931676] = true := by
  decide +kernel

theorem c1 : allCells dirCell 4696 4818 [
    147562728878055386980, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1] = true := by
  decide +kernel

theorem k4818_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4818) 3).1
      1072435502862206092271911433429083676807461833481746891996951409834538297745878460156474651).isSome = true := by
  decide +kernel

theorem k4818_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4818) 3).2
      6967422015576659074277598288585334419780846008535941424659773113271467440365933755962737108555185983203663195107447406935899814154732239850209220294754462).isSome = true := by
  decide +kernel

theorem k4819_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4819) 3).1 2).1
      47106368055960890898609791859582648430081544459).isSome = true := by
  decide +kernel

theorem k4819_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4819) 3).1 2).2
      5584388879376862725074357126212420786749770160976615755284017494361838214379773209653741124259728071132011976056014224834283815).isSome = true := by
  decide +kernel

theorem k4819_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4819) 3).2
      1510401873097986196792668010097934657813837873349173764927571912016052526520418485155267910858690050585912558858).isSome = true := by
  decide +kernel

theorem k4820_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4820) 2).1
      2968858642286934157325701494484223759855792309515).isSome = true := by
  decide +kernel

theorem k4820_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4820) 2).2 3).1
      1248207974141626169277527339407453969972359985409174713311363048010771088526607823644182).isSome = true := by
  decide +kernel

theorem k4820_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4820) 2).2 3).2
      1247366408352952236937709772411892300209558553345276658953955684961840359839484568929814).isSome = true := by
  decide +kernel

theorem k4821_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4821) 2).1
      2951541098235986444529612417516679670472821720331).isSome = true := by
  decide +kernel

theorem k4821_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4821) 2).2 3).1
      77908362732132923158302179481842504905947005897484399580090789306769454410522236735798).isSome = true := by
  decide +kernel

theorem k4821_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4821) 2).2 3).2
      19466966195456101114426741211770509846743606343284746582798135392323705847098226152902).isSome = true := by
  decide +kernel

theorem k4822_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4822) 2).1
      45957960707875236294456722746929560887479537931).isSome = true := by
  decide +kernel

theorem k4822_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4822) 2).2
      22325116015551323693761828737669877284554573794711355229255776742348613077594885535342889397853328828059414043040749732835068438055).isSome = true := by
  decide +kernel

theorem k4823_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4823) 2).1
      45863356701539055321774081880447078566629412903).isSome = true := by
  decide +kernel

theorem k4823_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4823) 2).2
      5438869367384772535774445921530361535391098186438172639828142508242654757335638734341920555977058316167872135913880127486538023).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 4824 4825 [
    7570673549239425700016218393036843797873403643407737438064315397466138580571572807868404667239662786822625405660551239476888615096671473664030294924514997603444301125918] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4825 4826 [
    25628374897503618777971354189772816355857388937536549079499557702451086076491669158719871620899247502511824793890468211783793755850390269235492212774] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4826 4827 [
    18377572455134942491339072521634351282626864894428909230841511872268986438054466998367434023093142294892582] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4827 4829 [
    972552102378347416554791043777337509444350363355429048948900756084380812430523758406,
    972246734214119759659556925115577523185231652695880850498084397965773878485737372230] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4829 4846 [
    714130038470923269935873509512152600588390422, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k4846_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4846) 3).1
      9913592578863124103459).isSome = true := by
  decide +kernel

theorem k4846_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4846) 3).2
      106138898083822939473546871015914267616579085266543622310583012529496542451853230276281865614072094841564110589640100432782813242099022994174372983070).isSome = true := by
  decide +kernel

theorem k4847_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4847) 3).1 2).1
      4194464071737472696914263753889778387873446745762947339941594542381721789064119752497763211).isSome = true := by
  decide +kernel

theorem k4847_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4847) 3).1 2).2
      255831653980058822812227565882471402744001668664827630827986431540712700905040412497715).isSome = true := by
  decide +kernel

theorem k4847_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4847) 3).2 2).1 3).1
      216104827947347411658536284622191896190887672011625990670830737202).isSome = true := by
  decide +kernel

theorem k4847_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4847) 3).2 2).1 3).2
      3978195925139948602928249882508057776527802488287044536165848793001214622369294243634).isSome = true := by
  decide +kernel

theorem k4847_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4847) 3).2 2).2
      1018788715142950461521740881484033405718229639422035476753237313089463677459227533817481).isSome = true := by
  decide +kernel

theorem k4848_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4848) 2).1 3).1
      88353409665984831439055805190789425935946610574003508952657891588384508089139491882932602864536907615696432952162381134884558726).isSome = true := by
  decide +kernel

theorem k4848_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4848) 2).1 3).2
      352120521519016781892037308375037124472382634707072258097702875900146992941223361187847205879178293362368449934880442963773119686).isSome = true := by
  decide +kernel

theorem k4848_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4848) 2).2 3).1
      259725650108281632421183508853678746144199692101715181775311470841979978162179052869274822).isSome = true := by
  decide +kernel

theorem k4848_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4848) 2).2 3).2
      16555379014873851544646644903904881736010829040139098645931201767237142777316544892701584582).isSome = true := by
  decide +kernel

theorem k4849_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4849) 2).1 3).1
      87787065458177523118602036003322060100723455943396794727605255414932607833944797906630754596367043410145650224869527078512957318).isSome = true := by
  decide +kernel

theorem k4849_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4849) 2).1 3).2
      87563737923219217988177283742033493253936877963212459129673098681603768296181646033761327059458555189783406876423035613893334918).isSome = true := by
  decide +kernel

theorem k4849_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4849) 2).2 3).1
      304708625148645150866211726837459376267753457053374227999419187412905673238981297068049404955920735862851098502).isSome = true := by
  decide +kernel

theorem k4849_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4849) 2).2 3).2
      87602836858025070276325828069414924016804552915610372224336366773123074167795636383811652823896386885783580852503290149795469193).isSome = true := by
  decide +kernel

theorem k4850_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4850) 2).1 3).1
      1365456211267187889708189218640058132264876004177369677246002453986791748206796759272903139815342371313663236581871498169718662).isSome = true := by
  decide +kernel

theorem k4850_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4850) 2).1 3).2
      18476160688303818965793462343488636534741130353186896319687894906415642360176637605778803814416215936431305).isSome = true := by
  decide +kernel

theorem k4850_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4850) 2).2 3).1
      87425285592897992556079309133286329237067661555902301818948862191176239600718319877047178054631526429792098863347870060147824521).isSome = true := by
  decide +kernel

theorem k4850_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4850) 2).2 3).2
      5455289296712814740491153034356860683905578333341895129913426239693143943351807944769627821340606090394003411253842379129322289).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4692 4851 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 4818)
      (.split 3 (.leaf _ k4818_0) (.leaf _ k4818_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4819)
      (.split 3 (.split 2 (.leaf _ k4819_0) (.leaf _ k4819_1)) (.leaf _ k4819_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4820)
      (.split 2 (.leaf _ k4820_0) (.split 3 (.leaf _ k4820_1) (.leaf _ k4820_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4821)
      (.split 2 (.leaf _ k4821_0) (.split 3 (.leaf _ k4821_1) (.leaf _ k4821_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4822)
      (.split 2 (.leaf _ k4822_0) (.leaf _ k4822_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4823)
      (.split 2 (.leaf _ k4823_0) (.leaf _ k4823_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.one (box := dirCellBox) (n := 4846)
      (.split 3 (.leaf _ k4846_0) (.leaf _ k4846_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4847)
      (.split 3 (.split 2 (.leaf _ k4847_0) (.leaf _ k4847_1)) (.split 2 (.split 3 (.leaf _ k4847_2) (.leaf _ k4847_3)) (.leaf _ k4847_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4848)
      (.split 2 (.split 3 (.leaf _ k4848_0) (.leaf _ k4848_1)) (.split 3 (.leaf _ k4848_2) (.leaf _ k4848_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4849)
      (.split 2 (.split 3 (.leaf _ k4849_0) (.leaf _ k4849_1)) (.split 3 (.leaf _ k4849_2) (.leaf _ k4849_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4850)
      (.split 2 (.split 3 (.leaf _ k4850_0) (.leaf _ k4850_1)) (.split 3 (.leaf _ k4850_2) (.leaf _ k4850_3))))

end C4.Cert.Dir148
