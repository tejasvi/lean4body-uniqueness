module

public import C4Check

public section

/-! Cells `5716 ≤ n < 5751` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir160

theorem k5716_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5716) 3).1
      1013132057599879315858237242869722414987541616587559819496240025965352264551019271254834).isSome = true := by
  decide +kernel

theorem k5716_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5716) 3).2
      258530872338147974321583783593493714029937350840942504418655311158444285517173996326671238).isSome = true := by
  decide +kernel

theorem k5717_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5717) 2).1
      5604975492450849607701487397331891979903721721070552921192876051215787547188545961073032867807782132164621096149070253870468830091).isSome = true := by
  decide +kernel

theorem k5717_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5717) 2).2
      1029179556855818883997591219844707850445670451176587824287237239422464567862918479521026951).isSome = true := by
  decide +kernel

theorem k5718_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5718) 2).1 3).1
      980229823956602937387241762103238674640128577237168494867403534501625822670906857377).isSome = true := by
  decide +kernel

theorem k5718_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5718) 2).1 3).2
      212285464684931444470264931214696383392758406515181648356115237681).isSome = true := by
  decide +kernel

theorem k5718_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5718) 2).2 3).1
      53156998025316629155143082535368160571758855666428322550287603617).isSome = true := by
  decide +kernel

theorem k5718_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5718) 2).2 3).2
      212311757796767474803557174281307780906121790869759860811057158049).isSome = true := by
  decide +kernel

theorem k5719_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5719) 2).1
      4837126503483248612212976695679103530338386825116650623699947809182180470034059509425791441775976981495195257735).isSome = true := by
  decide +kernel

theorem k5719_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5719) 2).2
      4837365414814247894407101537129277637118416657936658179491098973728504343272829157338849874484790768426623655559).isSome = true := by
  decide +kernel

theorem k5720_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5720) 2).1
      1022603850311761994419879808774515908907551856901146319633364826130786190231694640725248903).isSome = true := by
  decide +kernel

theorem k5720_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5720) 2).2
      255684017473329522171968644072930963371350494316748750593412505198529293579205677953880967).isSome = true := by
  decide +kernel

theorem k5721_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5721) 2).1
      997594811985702319227144288182250976156863813026394521346733673248848774487723417950407).isSome = true := by
  decide +kernel

theorem k5721_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5721) 2).2
      73614556814554110109451160537949943027513313289189274808711986519732829611464196616030473708008012375251761).isSome = true := by
  decide +kernel

theorem k5722_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5722) 2).1
      3893840852589019548651226783346539902991971431945003198885004194085361612021903005491).isSome = true := by
  decide +kernel

theorem k5722_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5722) 2).2
      15576769365141612770275045887236698542818223373476640980569534581690943832296447630131).isSome = true := by
  decide +kernel

theorem k5723_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5723) 2).1
      52747006158535643651384313403658566376121165423699037031418304305).isSome = true := by
  decide +kernel

theorem k5723_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5723) 2).2
      3892354422302735067814106960653259691928536182007036063939162822240134190892198057777).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 5724 5725 [
    75254585200158862152700496653430670631848641299758346515759471125142176443098657154194051860106200243013866190] = true := by
  decide +kernel

theorem c9 : allCells dirCell 5725 5726 [
    1355238884605945421270855084498762322774038896988397448960013271335634456520000380459524287936681898121044918862677966305457394] = true := by
  decide +kernel

theorem c10 : allCells dirCell 5726 5727 [
    84681711570353777604081373878012810044445890468563403502766576361982356473050938551084646035965583466652945312908737519633862] = true := by
  decide +kernel

theorem c11 : allCells dirCell 5727 5728 [
    1147425042178217063118314578068186207282227814900215629571186995153094249083637992134997626768108025550066] = true := by
  decide +kernel

theorem c12 : allCells dirCell 5728 5729 [
    71703143801049462341360830327794051909349336091225845680490367187319724897230093790759446180918165180786] = true := by
  decide +kernel

theorem c13 : allCells dirCell 5729 5730 [
    242910754897907311945129885693189934877615545257605704135357022534826472502300350834] = true := by
  decide +kernel

theorem c14 : allCells dirCell 5730 5732 [
    60722085585984600909091264577071574464522475868533560064420750862896416466600842492,
    3794848853283078086811244146422252738980090256909786769931148391363169870516739452] = true := by
  decide +kernel

theorem c15 : allCells dirCell 5732 5743 [
    51426892823346789661093720440921182248256037270013907873775985,
    43557878947438866611843170698556867613020, 147573781924788220372, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c16 : allCells dirCell 5743 5744 [
    215235687396386124358158843926168147979959463222536537063264694791] = true := by
  decide +kernel

theorem c17 : allCells dirCell 5744 5745 [
    312470675959732361476602700168601112601401826979276206057706555308430857698795523622384719801212890217503427480779] = true := by
  decide +kernel

theorem k5745_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5745) 3).1
      4028642799412480524497069989404516868548205025544249507688025224520298229937971104435762).isSome = true := by
  decide +kernel

theorem k5745_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5745) 3).2
      64341570129282258112752955819163981661204193192096484838392819716350052756818591370132018).isSome = true := by
  decide +kernel

theorem k5746_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5746) 2).1
      262858583521343018359898525858608234077510247841226518347371810106596097251547771126439504071).isSome = true := by
  decide +kernel

theorem k5746_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5746) 2).2
      18934865861218031514673990589412340350399866721671820927598736219985190184191980128608056920183294861237500467).isSome = true := by
  decide +kernel

theorem k5747_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5747) 2).1
      1049064937573096474753479770565167559330617683902242969464223137847330175768871735458291354823).isSome = true := by
  decide +kernel

theorem k5747_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5747) 2).2
      1394684425833536959494676792991619178987278811832463500624140254350999521220556648619909173354679821214454812369947581179748004659).isSome = true := by
  decide +kernel

theorem k5748_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5748) 2).1
      255726205900496097258164386421835391647710885891378122384126318328875136632691951736678599).isSome = true := by
  decide +kernel

theorem k5748_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5748) 2).2
      1023007283734708322002088658568868780361976930632878110594984580706036329311228209697482951).isSome = true := by
  decide +kernel

theorem k5749_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5749) 2).1
      15964640525065911439071734434681856113951140026419861035524159534476587197653141861813043).isSome = true := by
  decide +kernel

theorem k5749_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5749) 2).2
      997881363132296377099550095865152858919853751492503313156475805480253444792476131750707).isSome = true := by
  decide +kernel

theorem k5750_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5750) 2).1
      63819084000938460853564900455232031950340084939000343341729181424132158779638523180297010).isSome = true := by
  decide +kernel

theorem k5750_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5750) 2).2
      997207485131540631816683924290105714582487423859129658935381040205415461995225117717297).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 5716 5751 :=
  (Cover.one (box := dirCellBox) (n := 5716)
      (.split 3 (.leaf _ k5716_0) (.leaf _ k5716_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5717)
      (.split 2 (.leaf _ k5717_0) (.leaf _ k5717_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5718)
      (.split 2 (.split 3 (.leaf _ k5718_0) (.leaf _ k5718_1)) (.split 3 (.leaf _ k5718_2) (.leaf _ k5718_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5719)
      (.split 2 (.leaf _ k5719_0) (.leaf _ k5719_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5720)
      (.split 2 (.leaf _ k5720_0) (.leaf _ k5720_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5721)
      (.split 2 (.leaf _ k5721_0) (.leaf _ k5721_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5722)
      (.split 2 (.leaf _ k5722_0) (.leaf _ k5722_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5723)
      (.split 2 (.leaf _ k5723_0) (.leaf _ k5723_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16).trans <|
  (Cover.dir c17).trans <|
  (Cover.one (box := dirCellBox) (n := 5745)
      (.split 3 (.leaf _ k5745_0) (.leaf _ k5745_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5746)
      (.split 2 (.leaf _ k5746_0) (.leaf _ k5746_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5747)
      (.split 2 (.leaf _ k5747_0) (.leaf _ k5747_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5748)
      (.split 2 (.leaf _ k5748_0) (.leaf _ k5748_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5749)
      (.split 2 (.leaf _ k5749_0) (.leaf _ k5749_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5750)
      (.split 2 (.leaf _ k5750_0) (.leaf _ k5750_1)))

end C4.Cert.Dir160
