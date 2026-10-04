module

public import C4Check

public section

/-! Cells `4910 ≤ n < 4940` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir151

theorem k4910_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4910) 2).1 3).1
      211149369295500936515749818944412464276065953005653071906334882876).isSome = true := by
  decide +kernel

theorem k4910_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4910) 2).1 3).2
      211070358729395406515431825995393101310323285316895179023446228028).isSome = true := by
  decide +kernel

theorem k4910_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4910) 2).2
      5427434378149647353486133547249695820877409224137306745114408732204882528544981166874948787383396838705862329571176338691578675).isSome = true := by
  decide +kernel

theorem k4911_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4911) 2).1
      86790985323764259121791391834190699864640222219094048873666543719717346614177382012258205689583169614196892670787405907191263473).isSome = true := by
  decide +kernel

theorem k4911_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4911) 2).2
      1388588077955442887856512121831886148744504167680187360380181949757388433790641514037833838595031245744532187022607958446853435635).isSome = true := by
  decide +kernel

theorem k4912_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4912) 2).1
      15932259298797961230325909144683961052259314498813948757534314031241900135380726704359667).isSome = true := by
  decide +kernel

theorem k4912_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4912) 2).2
      18810936453869499837296682542647590533344036712125681153513117704675289809697796155130055730946451551022149875).isSome = true := by
  decide +kernel

theorem k4913_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4913) 2).1
      286949659514580626780651980856246583031855998492410569143392586431500441233353225628788519038958274335548).isSome = true := by
  decide +kernel

theorem k4913_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4913) 2).2
      15556057641372255680375980112904054288490112323425262520711915108517964252604054096444).isSome = true := by
  decide +kernel

theorem k4914_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4914) 1).1
      248828510442943495602632121463666171816891646888037780522651166383402625459076344918844).isSome = true := by
  decide +kernel

theorem k4914_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4914) 1).2
      286883522814508976510507857879790425978668951046950933645885224252123456471576513139775206030171549717308).isSome = true := by
  decide +kernel

theorem k4915_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4915) 2).1
      971801308281894270943858430372142996020925452783738367606874426228167587068485923068).isSome = true := by
  decide +kernel

theorem k4915_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4915) 2).2
      15549069545364707211518232074523859732232220254517951437410805433317902059471975732028).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4916 4917 [
    5417914745017946548003896132873934902978099824008500265487704749462736331977503859067199912005380160721340367614317707713268977] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4917 4918 [
    338539921587853523325834926158911060313670009557488440843573917937806268414293157505813737983445041122406940671228480984020209] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4918 4919 [
    17922772798453339666384122772936757966532175384046550249023856284000878384371647722743942406279980482633] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4919 4931 [
    15178200423784466936189369471071416340449067946628764659028406086268503828902794609,
    174226569721312322130557619702664029190673, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4931 4932 [
    4692477687610954074543284204031014249835144073212535383901334252890798700035112660664653092898277276973387] = true := by
  decide +kernel

theorem k4932_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4932) 3).1
      253448953611371701960323952164544242255383683802342799302484855517544295427680436758150).isSome = true := by
  decide +kernel

theorem k4932_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4932) 3).2
      1035165749710651198587067696926943827572397405477296484783341367029148144955651079325174982).isSome = true := by
  decide +kernel

theorem k4933_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4933) 2).1 3).1
      13663193386959140813143018679680527436209290388651856873729277391666).isSome = true := by
  decide +kernel

theorem k4933_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4933) 2).1 3).2
      1006221530596617478402106319063194955227340629909257383711101623362187057985674074223409).isSome = true := by
  decide +kernel

theorem k4933_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4933) 2).2
      19456137619442182663561114983978407675996742590839401697458310445834569279639031792751133405191374702994676534471).isSome = true := by
  decide +kernel

theorem k4934_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4934) 2).1 3).1
      4018113344894994707272665288777839712941322817308376267082495130521895564029195509424945).isSome = true := by
  decide +kernel

theorem k4934_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4934) 2).1 3).2
      4012643050550823468506961197702939200318408840225646971217372044986970031342122077369137).isSome = true := by
  decide +kernel

theorem k4934_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4934) 2).2 3).1
      62808229212347267919341960955048544576997903203226266711869118855182800595312031624396).isSome = true := by
  decide +kernel

theorem k4934_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4934) 2).2 3).2
      250835744541116640833492241256695942303052902060419829999140997302643513928148845915340).isSome = true := by
  decide +kernel

theorem k4935_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4935) 2).1 3).1
      1001818464612303929078194895666939063729033686174362095299091170695525487488943604200241).isSome = true := by
  decide +kernel

theorem k4935_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4935) 2).1 3).2
      1000698009408274147252447358675397427965143396734961011788290370518006940187890763264817).isSome = true := by
  decide +kernel

theorem k4935_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4935) 2).2 3).1
      250501727438311145754606265649039893092485605101332520605043236192439250600976612256972).isSome = true := by
  decide +kernel

theorem k4935_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4935) 2).2 3).2
      3909783890841860952766003968913343250592481132420245657455546842322856146596053511372).isSome = true := by
  decide +kernel

theorem k4936_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4936) 2).1 3).1
      15622228456462112172744095481420074892350114584450045478270991787856635155364305105612).isSome = true := by
  decide +kernel

theorem k4936_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4936) 2).1 3).2
      3902481933138909070378378910054026264223636102937211484276197335144041339559326642892).isSome = true := by
  decide +kernel

theorem k4936_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4936) 2).2 3).1
      211745802534699238914151339852502807976489322677717564290516696268).isSome = true := by
  decide +kernel

theorem k4936_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4936) 2).2 3).2
      3903015606213678692367580145338369738828488710834320551217600898453869618806849401548).isSome = true := by
  decide +kernel

theorem k4937_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4937) 2).1 3).1
      211412799345211090653819354724884913531319932335656738721147374284).isSome = true := by
  decide +kernel

theorem k4937_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4937) 2).1 3).2
      52823513583200107347022478347471612408102773074796116177390652108).isSome = true := by
  decide +kernel

theorem k4937_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4937) 2).2 1).1
      52845613542013537109058065863243387156674581307942833572771394252).isSome = true := by
  decide +kernel

theorem k4937_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4937) 2).2 1).2
      52842419355434461522722719103599790378493131609149136768034271948).isSome = true := by
  decide +kernel

theorem k4938_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4938) 2).1
      5427994572548251403380716522935461418911344808972035784454918036962187476697719434457797941788615285453453501276553882605312819).isSome = true := by
  decide +kernel

theorem k4938_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4938) 2).2
      75332781338353993131206610499473868544440386130261544872717459598191938843920835630085764736066694888600578867).isSome = true := by
  decide +kernel

theorem k4939_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4939) 2).1
      5425248087543128022703033118349539927959566864685566078159849779191967560850614445552877763672467574280404463820919782533094193).isSome = true := by
  decide +kernel

theorem k4939_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4939) 2).2
      1176354206697269091719840406074335065353487953150903923166113924515403223051287953651640924258619230472579891).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4910 4940 :=
  (Cover.one (box := dirCellBox) (n := 4910)
      (.split 2 (.split 3 (.leaf _ k4910_0) (.leaf _ k4910_1)) (.leaf _ k4910_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4911)
      (.split 2 (.leaf _ k4911_0) (.leaf _ k4911_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4912)
      (.split 2 (.leaf _ k4912_0) (.leaf _ k4912_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4913)
      (.split 2 (.leaf _ k4913_0) (.leaf _ k4913_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4914)
      (.split 1 (.leaf _ k4914_0) (.leaf _ k4914_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4915)
      (.split 2 (.leaf _ k4915_0) (.leaf _ k4915_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 4932)
      (.split 3 (.leaf _ k4932_0) (.leaf _ k4932_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4933)
      (.split 2 (.split 3 (.leaf _ k4933_0) (.leaf _ k4933_1)) (.leaf _ k4933_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4934)
      (.split 2 (.split 3 (.leaf _ k4934_0) (.leaf _ k4934_1)) (.split 3 (.leaf _ k4934_2) (.leaf _ k4934_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4935)
      (.split 2 (.split 3 (.leaf _ k4935_0) (.leaf _ k4935_1)) (.split 3 (.leaf _ k4935_2) (.leaf _ k4935_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4936)
      (.split 2 (.split 3 (.leaf _ k4936_0) (.leaf _ k4936_1)) (.split 3 (.leaf _ k4936_2) (.leaf _ k4936_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4937)
      (.split 2 (.split 3 (.leaf _ k4937_0) (.leaf _ k4937_1)) (.split 1 (.leaf _ k4937_2) (.leaf _ k4937_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4938)
      (.split 2 (.leaf _ k4938_0) (.leaf _ k4938_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4939)
      (.split 2 (.leaf _ k4939_0) (.leaf _ k4939_1)))

end C4.Cert.Dir151
