module

public import C4Check

public section

/-! Cells `989 ≤ n < 1183` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir004

theorem k989_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 989) 3).1 2).1
      3897468077777151845509941101868657909662847845497995539946528513055586356316040140593).isSome = true := by
  decide +kernel

theorem k989_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 989) 3).1 2).2
      52747112378854733357805048864952276092520845914517409070155906108).isSome = true := by
  decide +kernel

theorem k989_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 989) 3).2
      1175717076418343724101404674563954924603544320845507970208500864318227056032972581970165020561979210281653449).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 990 991 [
    1598545384067836584633438009745351904526877924829036426822922931102466147988941488672337344872036785160542224248291756678648005934342661930756740551] = true := by
  decide +kernel

theorem c2 : allCells dirCell 991 1016 [
    2359501312448461078593, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
    21766093704025330683181380424647926034329645106401472748396052300748903364477035710648761016857906787994717358948509789933049607] = true := by
  decide +kernel

theorem k1016_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1016) 3).1
      5437333014451578515896887500517252184181041278832552882328748796102726340743496726199429375792809811694614206915739861676176838).isSome = true := by
  decide +kernel

theorem k1016_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1016) 3).2
      4709987104676546061738587492535246495726988504375360203065713670883337093895646072810283835744273573119837385).isSome = true := by
  decide +kernel

theorem k1017_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1017) 3).1
      294145827021788535525533206302744533281706665208882478476029509033486396295035490760825000054868535464251185).isSome = true := by
  decide +kernel

theorem k1017_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1017) 3).2
      4596644174990363790789806947905964425048191324082562583831942129521696580308484156040037726057581227635953).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 1018 1019 [
    7371690428726421871061970086180025526549403159466997915852357822603667968466202777430573671234717247876906413933086396279739214888649718696526467251788255485127583175] = true := by
  decide +kernel

theorem c6 : allCells dirCell 1019 1044 [
    2359512484586777198401, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
    288080517667657753829449971190673576930545655165120397018984814597137804516129345495700766124964679094535] = true := by
  decide +kernel

theorem k1044_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1044) 3).1
      287767786337223840447186200061235947948803348715612288788550518537846409128105356523488056741267667585353).isSome = true := by
  decide +kernel

theorem k1044_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1044) 3).2
      294392186366792234142515672396896871002264661397437385866727550486552962468476533149228230426202169306345713).isSome = true := by
  decide +kernel

theorem k1045_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1045) 3).1
      996311865743023196386714434288146365065902527052793109883551051846234947193928359440626).isSome = true := by
  decide +kernel

theorem k1045_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1045) 3).2
      3890011211972370628954808328244127287368514345210046254476817088864384910630266607025).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1046 1071 [
    71673009562951981327651793673893303020756477376736475745929608107952879527710275504201439027450676157513,
    147503335596324600404, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem c10 : allCells dirCell 1071 1072 [
    975929771644677043308782363797658805934944892749101392809913350048740972301218288903] = true := by
  decide +kernel

theorem k1072_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1072) 3).1
      71935174904664028898794592138976819777707435276683915483021597652973529727945472359978530701844168587633).isSome = true := by
  decide +kernel

theorem k1072_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1072) 3).2
      15957244548993797514457025355997425396665462833950827339187953335791648980151458090913009).isSome = true := by
  decide +kernel

theorem k1073_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1073) 1).1
      3888157026010899879231898445086946897482636355865494019205804098707072952952302694643).isSome = true := by
  decide +kernel

theorem k1073_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1073) 1).2
      995803349498661616467863311945704231127333954710026529235460605103305341800296924410099).isSome = true := by
  decide +kernel

theorem c13 : allCells dirCell 1074 1099 [
    17918112383465165461578157680377815834165591898568339701287161771986943508950093825296742721711215449457,
    147434555783916726756, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c14 : allCells dirCell 1099 1100 [
    975835669313544388726610664328249557628820297237928677313501900435219241007966270727] = true := by
  decide +kernel

theorem k1100_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1100) 1).1
      71827677218610267215600473686686922089077622529045191550841406809853817294776719638421249119264886323571).isSome = true := by
  decide +kernel

theorem k1100_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1100) 1).2
      4709431962946327531041644040581297085236759969588268962998573600634950468946274122369178546847661702237340659).isSome = true := by
  decide +kernel

theorem k1101_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1101) 1).1
      242995663518235314937715525567897906992832668259535426865833770966625610026323121395).isSome = true := by
  decide +kernel

theorem k1101_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1101) 1).2
      62239814993866256278784437175606944351253425950653713724672216547434637439806648731891).isSome = true := by
  decide +kernel

theorem c17 : allCells dirCell 1102 1127 [
    17918028045353768672827246862875895715344626349816997493649270990351529688598368707258964602065569622385,
    147438239147884286036, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c18 : allCells dirCell 1127 1128 [
    13223730332152142812760253951475623824208406703728213335138898183] = true := by
  decide +kernel

theorem k1128_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1128) 1).1
      4489038928579799392609722982204832114976779144469053460812869552084457347535249788601390093675373269363).isSome = true := by
  decide +kernel

theorem k1128_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1128) 1).2
      339343686107027888425815081016785871694088594054242935493138551793003056223351942555462832926739002188422823246252005042116083).isSome = true := by
  decide +kernel

theorem k1129_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1129) 3).1
      71802518495311475037685650625047996803598974577108095118097209252217855194619835073999951164065386114417).isSome = true := by
  decide +kernel

theorem k1129_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1129) 3).2
      15194487856101992847520067788227682047335751599960718512911471839174932618795085169).isSome = true := by
  decide +kernel

theorem c21 : allCells dirCell 1130 1156 [
    4480750506229027208046917536297385295283412666172806297545779631013378333882735427942049873854997284209,
    147442108329312925364, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2373020995386651231553] = true := by
  decide +kernel

theorem k1156_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1156) 3).1
      51596284009317448170628694755235696253682338104093189419153681).isSome = true := by
  decide +kernel

theorem k1156_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1156) 3).2
      1325451356418422588798854993155361831266960229423825923563984324053622555839527050421785440554227099074835940553294615680497).isSome = true := by
  decide +kernel

theorem c23 : allCells dirCell 1157 1158 [
    6252105056004786552127385990169967864209363155444592389523246607641243724402094263836914123122312029083265601856484085017383067264481548537525705] = true := by
  decide +kernel

theorem c24 : allCells dirCell 1158 1182 [
    51434700050067264379056445081303453282512681014422795799320081, 147446020735289618180, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209102] = true := by
  decide +kernel

theorem k1182_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1182) 2).1 3).1
      62469266657259840345044320077439683791349118258872726677372771565380267727063754601670).isSome = true := by
  decide +kernel

theorem k1182_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1182) 2).1 3).2 2).1
      243849312986833764144846075670372493318867226486042820953687513527647403799515851845).isSome = true := by
  decide +kernel

theorem k1182_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1182) 2).1 3).2 2).2
      3900990301187003275577624630780003770076913894306612231323268032653788784636908178765).isSome = true := by
  decide +kernel

theorem k1182_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1182) 2).2 3).1
      62542363656112554425051986076918676159544082333688010195569728568809691953712294208710).isSome = true := by
  decide +kernel

theorem k1182_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1182) 2).2 3).2 2).1
      62609978420152454725724981302731273109521540848589266950270437880841219935013715394637).isSome = true := by
  decide +kernel

theorem k1182_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1182) 2).2 3).2 2).2
      1151398087519161665278535734196181127634504456635671603919345224567857407300803440551685939303909069779533).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 989 1183 :=
  (Cover.one (box := dirCellBox) (n := 989)
      (.split 3 (.split 2 (.leaf _ k989_0) (.leaf _ k989_1)) (.leaf _ k989_2))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 1016)
      (.split 3 (.leaf _ k1016_0) (.leaf _ k1016_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1017)
      (.split 3 (.leaf _ k1017_0) (.leaf _ k1017_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 1044)
      (.split 3 (.leaf _ k1044_0) (.leaf _ k1044_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1045)
      (.split 3 (.leaf _ k1045_0) (.leaf _ k1045_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 1072)
      (.split 3 (.leaf _ k1072_0) (.leaf _ k1072_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1073)
      (.split 1 (.leaf _ k1073_0) (.leaf _ k1073_1))).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.one (box := dirCellBox) (n := 1100)
      (.split 1 (.leaf _ k1100_0) (.leaf _ k1100_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1101)
      (.split 1 (.leaf _ k1101_0) (.leaf _ k1101_1))).trans <|
  (Cover.dir c17).trans <|
  (Cover.dir c18).trans <|
  (Cover.one (box := dirCellBox) (n := 1128)
      (.split 1 (.leaf _ k1128_0) (.leaf _ k1128_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1129)
      (.split 3 (.leaf _ k1129_0) (.leaf _ k1129_1))).trans <|
  (Cover.dir c21).trans <|
  (Cover.one (box := dirCellBox) (n := 1156)
      (.split 3 (.leaf _ k1156_0) (.leaf _ k1156_1))).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24).trans <|
  (Cover.one (box := dirCellBox) (n := 1182)
      (.split 2 (.split 3 (.leaf _ k1182_0) (.split 2 (.leaf _ k1182_1) (.leaf _ k1182_2))) (.split 3 (.leaf _ k1182_3) (.split 2 (.leaf _ k1182_4) (.leaf _ k1182_5)))))

end C4.Cert.Dir004
