module

public import C4Check

public section

/-! Cells `4851 ≤ n < 4881` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir149

theorem k4851_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4851) 2).1 3).1
      62522667277703822151365786980783575985231925507086968439795397199952755918661904254153).isSome = true := by
  decide +kernel

theorem k4851_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4851) 2).1 3).2
      3905514611177709739797976727973293091448995611060070490496392623535821590028338192777).isSome = true := by
  decide +kernel

theorem k4851_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4851) 2).2 3).1
      1361975960667533221023694267002413482971650396100140135559998373520855300064468644364929991727499721300450752969063786056474417).isSome = true := by
  decide +kernel

theorem k4851_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4851) 2).2 3).2
      62474314990786620266159659284817488045804592589195900089131002834510391384957603633969).isSome = true := by
  decide +kernel

theorem k4852_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4852) 2).1 3).1
      3900532084815430242131956473928756517155596770327847162062211601364187409167156336009).isSome = true := by
  decide +kernel

theorem k4852_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4852) 2).1 3).2
      3898046348896771750483891017704100408623320781870434432676333720796182569298329050505).isSome = true := by
  decide +kernel

theorem k4852_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4852) 2).2 3).1
      15607571298395961387394952192222330845421096443428504831576801990101390939559443651762).isSome = true := by
  decide +kernel

theorem k4852_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4852) 2).2 3).2
      3898900044168067820985737508471762677242162422048611649224459007055626978175678635185).isSome = true := by
  decide +kernel

theorem k4853_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4853) 2).1
      21202574186782841055409786466094661955160044322345188736740677196763699499855932001259721693194533755759541512926420972729799).isSome = true := by
  decide +kernel

theorem k4853_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4853) 2).2 3).1
      3896843886044949011133620891914160033211313791752304211130660801322515001845197927089).isSome = true := by
  decide +kernel

theorem k4853_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4853) 2).2 3).2
      206207105551136046863165171621487223716352974646202806627032492).isSome = true := by
  decide +kernel

theorem k4854_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4854) 2).1
      287212737823705727039638442116926470133025325905660801419202025435335366866234086867653002744096572142833).isSome = true := by
  decide +kernel

theorem k4854_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4854) 2).2
      21192512155566238891273040247707806439423272402741231157900465204279794897979688330260562921560570795606717270382772770397619).isSome = true := by
  decide +kernel

theorem k4855_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4855) 2).1
      243140996950825852270565727360093588295034018447390892373992349792875778932305155315).isSome = true := by
  decide +kernel

theorem k4855_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4855) 2).2
      1148376933585947081498204728764056887937820069085063546863377007026967252236227780198117363823799371396337).isSome = true := by
  decide +kernel

theorem k4856_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4856) 2).1
      51472518376317878336871273393182364690097671149297831540372849).isSome = true := by
  decide +kernel

theorem k4856_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4856) 2).2
      286989180214086814271267718921393169725179618920050782179322327000802274412888564212075786183308105601777).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4857 4858 [
    6248038817808133065982228975950770214940382664942692566953095542623627140249181895680175243343177196000977598551839520217675944305633981994403270] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4858 4859 [
    5291524693612356048305189298568584729107792679177852629780994623204714773534142129347262174899057071466127619960102969013830] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4859 4875 [
    51455963186184270859114549644825046271342800578769717834559314, 37789901971899255202822, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 741235961153238736289945046609287571515187315] = true := by
  decide +kernel

theorem k4875_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4875) 3).1
      1646546485137410456500671110730725051913182341703705288865556915998661936507661747904828489738925489303693194625311206111086501579571067118295008718).isSome = true := by
  decide +kernel

theorem k4875_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4875) 3).2 2).1
      1018970214148233473293456393688680182600325738876773515771461006672015093743060304098098).isSome = true := by
  decide +kernel

theorem k4875_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4875) 3).2 2).2
      3974625611760756017917823294333840015595163051901608060185260126203533700117610649395).isSome = true := by
  decide +kernel

theorem k4876_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4876) 3).1 2).1
      16230675884773536217497626452626864431607384098074805388105170717546187245356253945255558).isSome = true := by
  decide +kernel

theorem k4876_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4876) 3).1 2).2
      1014740864550533199600161119498338286301816691135590607468904148333599375974081515320113).isSome = true := by
  decide +kernel

theorem k4876_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4876) 3).2 2).1
      64687071728645057804354574544412359239543203781131825004798248519275405604075055674676102).isSome = true := by
  decide +kernel

theorem k4876_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4876) 3).2 2).2
      16189893473714696514903217733741661885488798984282160192556799895739152057243963870268977).isSome = true := by
  decide +kernel

theorem k4877_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4877) 2).1 3).1
      258185017041154631579644221560665490808471183204146269098457053645820172107673318292525961).isSome = true := by
  decide +kernel

theorem k4877_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4877) 2).1 3).2
      1030136389107641299444882163394114065653134184008982311911388490270983632214166477099912390).isSome = true := by
  decide +kernel

theorem k4877_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4877) 2).2 3).1
      4131944632852534141867566460258485769653596794741610560746681094102296947113021331772041417).isSome = true := by
  decide +kernel

theorem k4877_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4877) 2).2 3).2
      4751989722437729838193790600393660865497778508629521880175295222844308779529913694738924342178442806770922289).isSome = true := by
  decide +kernel

theorem k4878_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4878) 2).1 3).1
      16448706155369145775548264057704796790538170842396253701340144181759177622119337460607560902).isSome = true := by
  decide +kernel

theorem k4878_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4878) 2).1 3).2
      1183311932181077233895111051708408723904969488850180655286593271952192549403621987724856949855383964261772081).isSome = true := by
  decide +kernel

theorem k4878_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4878) 2).2 3).1
      4113375009983977856759930693074634605207255072276781328430938816210288628035970762963045577).isSome = true := by
  decide +kernel

theorem k4878_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4878) 2).2 3).2
      4106610329564519363330863986992837595485621588357430115069872243836670704666586887247776969).isSome = true := by
  decide +kernel

theorem k4879_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4879) 2).1 3).1
      73859044488035572165323563241803711814361373869377251546673763565792445634494928395279208730241848281783089).isSome = true := by
  decide +kernel

theorem k4879_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4879) 2).1 3).2
      18444379174863298300616784825052981681389136917351840161973711344331643111430896932496522081245596806929201).isSome = true := by
  decide +kernel

theorem k4879_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4879) 2).2 3).1
      1182165337074270443217801426193304833968467983018480954773063505785252054373508808421296351279664965094857522).isSome = true := by
  decide +kernel

theorem k4879_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4879) 2).2 3).2
      1180849156216480627000621354121355163138601455922245265038160396256884701228003639554574136811518881190763314).isSome = true := by
  decide +kernel

theorem k4880_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4880) 2).1 3).1
      15609559803185610480309994281986814744835144423980183257322202026216009234341415115569).isSome = true := by
  decide +kernel

theorem k4880_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4880) 2).1 3).2
      3899621323948246523773436344395662665838733796683479049882236457361000842416689272625).isSome = true := by
  decide +kernel

theorem k4880_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4880) 2).2 3).1
      18432557460631057952667056296843146945481308255678948751661632160687310141378379887653630526224090118085425).isSome = true := by
  decide +kernel

theorem k4880_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4880) 2).2 3).2
      15601757283519825676903815603464113294695029739739228255319680292606295976984444361521).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4851 4881 :=
  (Cover.one (box := dirCellBox) (n := 4851)
      (.split 2 (.split 3 (.leaf _ k4851_0) (.leaf _ k4851_1)) (.split 3 (.leaf _ k4851_2) (.leaf _ k4851_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4852)
      (.split 2 (.split 3 (.leaf _ k4852_0) (.leaf _ k4852_1)) (.split 3 (.leaf _ k4852_2) (.leaf _ k4852_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4853)
      (.split 2 (.leaf _ k4853_0) (.split 3 (.leaf _ k4853_1) (.leaf _ k4853_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4854)
      (.split 2 (.leaf _ k4854_0) (.leaf _ k4854_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4855)
      (.split 2 (.leaf _ k4855_0) (.leaf _ k4855_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4856)
      (.split 2 (.leaf _ k4856_0) (.leaf _ k4856_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4875)
      (.split 3 (.leaf _ k4875_0) (.split 2 (.leaf _ k4875_1) (.leaf _ k4875_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4876)
      (.split 3 (.split 2 (.leaf _ k4876_0) (.leaf _ k4876_1)) (.split 2 (.leaf _ k4876_2) (.leaf _ k4876_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4877)
      (.split 2 (.split 3 (.leaf _ k4877_0) (.leaf _ k4877_1)) (.split 3 (.leaf _ k4877_2) (.leaf _ k4877_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4878)
      (.split 2 (.split 3 (.leaf _ k4878_0) (.leaf _ k4878_1)) (.split 3 (.leaf _ k4878_2) (.leaf _ k4878_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4879)
      (.split 2 (.split 3 (.leaf _ k4879_0) (.leaf _ k4879_1)) (.split 3 (.leaf _ k4879_2) (.leaf _ k4879_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4880)
      (.split 2 (.split 3 (.leaf _ k4880_0) (.leaf _ k4880_1)) (.split 3 (.leaf _ k4880_2) (.leaf _ k4880_3))))

end C4.Cert.Dir149
