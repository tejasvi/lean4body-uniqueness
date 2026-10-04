module

public import C4Check

public section

/-! Cells `3980 ≤ n < 4006` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir127

theorem k3980_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).1 2).1
      89986840581530475817497130216683707805169333970073448623323217078240469272431349276255733156460407051412333600890039866029180832455).isSome = true := by
  decide +kernel

theorem k3980_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).1 2).2 3).1
      1167126729245587827054513216262872225786806265548725651634556186530765564955856801665975725925335778557105).isSome = true := by
  decide +kernel

theorem k3980_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).1 2).2 3).2
      986056197832146829410715145176271016081950992956421274934406500788498373547984968881).isSome = true := by
  decide +kernel

theorem k3980_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).2 2).1
      100954603143052500942052710311937326661883235798492436280408817535811578007150600596035451826029943599368688785856854208323558207391655587521992471).isSome = true := by
  decide +kernel

theorem k3980_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).2 2).2 3).1
      984063152277679114064529499473596623030958628570229661316890283431446697972165401777).isSome = true := by
  decide +kernel

theorem k3980_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).2 2).2 3).2
      3929586033358192158502532402695127138762424522355120838330162944754886865477105185457).isSome = true := by
  decide +kernel

theorem k3980_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).1 3).1
      63303881968763450884734506776532451737357184829661690602913738226958559315350359481137).isSome = true := by
  decide +kernel

theorem k3980_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).1 3).2
      63146621287533958727877678455274133830173513543459809753915990108711827314918514322609).isSome = true := by
  decide +kernel

theorem k3980_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).2 3).1
      63368601612276815601243101977562617907548651791048133621930730163246859266921420397361).isSome = true := by
  decide +kernel

theorem k3980_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).2 3).2
      252824204456767462055630483466919688636611120436097391951624943981296559340341555206961).isSome = true := by
  decide +kernel

theorem k3980_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).1 3).1
      854058475174271052849521502593703111070849420861070468798209875121).isSome = true := by
  decide +kernel

theorem k3980_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).1 3).2
      983113328767034109521222656623777420830545654079155849158184507944103256147968613553).isSome = true := by
  decide +kernel

theorem k3980_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).2 3).1
      15765573656865872681194110008524079080296121594398570474207106511238281825103091555121).isSome = true := by
  decide +kernel

theorem k3980_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).2 3).2
      3934951460643686279219954366754681666178363323660713080710471889793710927966222310577).isSome = true := by
  decide +kernel

theorem k3981_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).1 3).1 2).1
      72295080009101034678586791714683625263119414934856804857696268423581451564682238218998203117506878232013).isSome = true := by
  decide +kernel

theorem k3981_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).1 3).1 2).2
      100761966412832933562718704108357905111550557685558885666674535552675284084570003262635390595897908437006550960407155351225135316780611496857663181).isSome = true := by
  decide +kernel

theorem k3981_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).1 3).2 2).1
      977924200819458713931496062361013069175172377963901835891180379628887311315775878385).isSome = true := by
  decide +kernel

theorem k3981_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).1 3).2 2).2
      5326826583669977059771583358469831465355942289137563669080746344317372185425916059299039738809036739075977038726664600028621).isSome = true := by
  decide +kernel

theorem k3981_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).1 2).1 3).1
      981632890720887456599040411023868433516744452061741579649774214554743880919590853809).isSome = true := by
  decide +kernel

theorem k3981_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).1 2).1 3).2
      3921514535905068764420622810283936804188541752962918378745909469982271631557367526065).isSome = true := by
  decide +kernel

theorem k3981_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).1 2).2 1).1
      62786521756068083792482177461528881812862434018912693554139121031498110399556695973043).isSome = true := by
  decide +kernel

theorem k3981_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).1 2).2 1).2
      3323548712753339385522613753258628323335511934333184350492439731).isSome = true := by
  decide +kernel

theorem k3981_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).2 2).1
      25162537897574278279216184673847935177800861424648099833140704338986030797804281390701267324223548649788081425898007376974691248831143133576746701).isSome = true := by
  decide +kernel

theorem k3981_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3981) 2).2 3).2 2).2
      100709818560386170569831302885000721981718537900583214825170314355148082453339616377347765807706460621977917257792154874406558589411755383360714417).isSome = true := by
  decide +kernel

theorem k3982_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).1 3).1 2).1
      61036870790360186189834509307174476031293938487800665922059444633297584044477511109).isSome = true := by
  decide +kernel

theorem k3982_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).1 3).1 2).2
      72084991499830245639703938906682771017662332973249912266574752324587649660520284130726994982327400363249).isSome = true := by
  decide +kernel

theorem k3982_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3982) 2).1 3).2
      340024856168067688086188326001386354959967950002595322128795566229286258020740807606273970366603576277977608390879286824928710).isSome = true := by
  decide +kernel

theorem k3982_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).2 3).1 2).1
      18027572182145063045733444523091211749215990911226706013174583342318182775936772344488942589485240704433).isSome = true := by
  decide +kernel

theorem k3982_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).2 3).1 2).2
      21287501320152619000261485013915224658823033214984538389745541502198540317929045984014133758218121741456916222764253133364657).isSome = true := by
  decide +kernel

theorem k3982_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).2 3).2 1).1
      21266422862312334283330130715371324335169650813748761560170056604087128197383489323338877119786351990400275462794882975489458).isSome = true := by
  decide +kernel

theorem k3982_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3982) 2).2 3).2 1).2
      15256123962535868896438551798649773249583156104897679808439111221893363639864745330).isSome = true := by
  decide +kernel

theorem k3983_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3983) 2).1 3).1
      21234197438997831899988101527166742181379494171569177235616585757659140531068006289328152116742572798924759438853763696186822).isSome = true := by
  decide +kernel

theorem k3983_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3983) 2).1 3).2
      1326299144752992056874837692713536308385904578744706382807009716000836038902712157281466215085296191094002364166050213623281).isSome = true := by
  decide +kernel

theorem k3983_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3983) 2).2 3).1 1).1
      287930490476234701288647402610014852988897318386372242700582504380390861535012873904204499141750482048242).isSome = true := by
  decide +kernel

theorem k3983_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3983) 2).2 3).1 1).2
      15241382076161890083131159333546844791500866998295982944897592755341271768205247858).isSome = true := by
  decide +kernel

theorem k3983_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3983) 2).2 3).2
      25061131091536467898508064826896757687428348448469260509005911401630543063856484233265990120776737599723211874920157218666760318257693054627419590).isSome = true := by
  decide +kernel

theorem k3984_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3984) 2).1 3).1
      17966134219636265076287158106406853437083894188667543838623032393694268985527666698515753744166986814281).isSome = true := by
  decide +kernel

theorem k3984_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3984) 2).1 3).2
      15212143746723165652212096625631185552997042242510352780307357657559358147750754673).isSome = true := by
  decide +kernel

theorem k3984_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3984) 2).2 3).1
      5303581308550541935060935700863065461472227442396829873786230211075462322147180440209424238062660740493618951266894098036209).isSome = true := by
  decide +kernel

theorem k3984_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3984) 2).2 3).2
      1325318993992513876443904688105283292458071411264236797270613729486391637334996179778515321456106431560637771066216896624113).isSome = true := by
  decide +kernel

theorem k3985_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3985) 2).1
      364479197622058615240224385342474665686309447).isSome = true := by
  decide +kernel

theorem k3985_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3985) 2).2
      6254522036049490508799353426417028701578328213316388203648783514780259937284089627111151454326418343589772572877608823660255866793891630016275911).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3986 4006 [
    15562527155222490391063431321155394565788713251293775503335262870112204634972949071622, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30483644071452044591290717747] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3980 4006 :=
  (Cover.one (box := dirCellBox) (n := 3980)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3980_0) (.split 3 (.leaf _ k3980_1) (.leaf _ k3980_2))) (.split 2 (.leaf _ k3980_3) (.split 3 (.leaf _ k3980_4) (.leaf _ k3980_5)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3980_6) (.leaf _ k3980_7)) (.split 3 (.leaf _ k3980_8) (.leaf _ k3980_9))) (.split 2 (.split 3 (.leaf _ k3980_10) (.leaf _ k3980_11)) (.split 3 (.leaf _ k3980_12) (.leaf _ k3980_13)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3981)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3981_0) (.leaf _ k3981_1)) (.split 2 (.leaf _ k3981_2) (.leaf _ k3981_3))) (.split 3 (.split 2 (.split 3 (.leaf _ k3981_4) (.leaf _ k3981_5)) (.split 1 (.leaf _ k3981_6) (.leaf _ k3981_7))) (.split 2 (.leaf _ k3981_8) (.leaf _ k3981_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3982)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3982_0) (.leaf _ k3982_1)) (.leaf _ k3982_2)) (.split 3 (.split 2 (.leaf _ k3982_3) (.leaf _ k3982_4)) (.split 1 (.leaf _ k3982_5) (.leaf _ k3982_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3983)
      (.split 2 (.split 3 (.leaf _ k3983_0) (.leaf _ k3983_1)) (.split 3 (.split 1 (.leaf _ k3983_2) (.leaf _ k3983_3)) (.leaf _ k3983_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3984)
      (.split 2 (.split 3 (.leaf _ k3984_0) (.leaf _ k3984_1)) (.split 3 (.leaf _ k3984_2) (.leaf _ k3984_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3985)
      (.split 2 (.leaf _ k3985_0) (.leaf _ k3985_1))).trans <|
  (Cover.dir c6)

end C4.Cert.Dir127
