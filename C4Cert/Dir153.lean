module

public import C4Check

public section

/-! Cells `4977 ≤ n < 5029` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir153

theorem c0 : allCells dirCell 4977 4989 [
    147566144029841856676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    74530759370058389710592174176867674000868979004035126082105644677416612137835686640538084472416478685246923] = true := by
  decide +kernel

theorem c1 : allCells dirCell 4989 4990 [
    1244891470021886902794684380749258922553794959050288894188425109576240799476832325267164001612099331677150956702923] = true := by
  decide +kernel

theorem k4990_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4990) 2).1
      1184677088863887389922873746788859180568820877794591391708294668652263484546361998853393738503934012904272691).isSome = true := by
  decide +kernel

theorem k4990_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4990) 2).2
      4013767782652932408205459160313178872426785531920263448811291161685065955364926725649203).isSome = true := by
  decide +kernel

theorem k4991_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4991) 2).1
      16402227445465185663262114440971658928382897652310288260303440245309071559044086969138328371).isSome = true := by
  decide +kernel

theorem k4991_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4991) 2).2
      256365160892274968107893048327487201907438042205492267087111969351252211882680977433506609).isSome = true := by
  decide +kernel

theorem k4992_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4992) 2).1
      4094958728953657890695936689759243855876131407695214399060107620268537462447613609540105009).isSome = true := by
  decide +kernel

theorem k4992_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4992) 2).2
      4095178861417366121696685974963194067262949534547749922469479804456287591261706090052367153).isSome = true := by
  decide +kernel

theorem k4993_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4993) 2).1
      1391596070472751680467435668528026553284930946620494543450727481896524264728532591684617440016116218602245927142533443047724528433).isSome = true := by
  decide +kernel

theorem k4993_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4993) 2).2
      73694388629434521020795032639704234157487374575124612684185341495934915244727274812580742580663721752587468).isSome = true := by
  decide +kernel

theorem k4994_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4994) 2).1
      3988989263029812035532480797038092576262321766282460406475572722757229180549771792069427).isSome = true := by
  decide +kernel

theorem k4994_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4994) 2).2
      3989941518645682263054122241809262906180691654728191604723431548601689386188404418769713).isSome = true := by
  decide +kernel

theorem k4995_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4995) 2).1
      249179784851464722377637036397406327034626024660429688930588603544107244955345320092620).isSome = true := by
  decide +kernel

theorem k4995_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4995) 2).2
      844291884330822059702993796905297037977262056926106131354858539724).isSome = true := by
  decide +kernel

theorem k4996_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4996) 2).1
      54002399471616711038894359229936644113387772746989733326472876801084).isSome = true := by
  decide +kernel

theorem k4996_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4996) 2).2
      15565856785752368948303471147794024832224217397086019452418444042189362961932512767036).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 4997 4998 [
    88828133085977534887427818991342166128529508162578319633081462953833508371109024901513308807706383797747910095378015679989711171826] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4998 4999 [
    19255331306728965520801033111239544382961899451357064591308094574413531825566221221062083550995097304515633934577] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4999 5000 [
    21674359458673099169442958077116266749800467114361170471113820620183516941641337033903351902092297379020956140572198171797603132] = true := by
  decide +kernel

theorem c12 : allCells dirCell 5000 5001 [
    18355570071358742014641368768666927314667832791757303999571734530636337228258792089053670708099382736003900] = true := by
  decide +kernel

theorem c13 : allCells dirCell 5001 5002 [
    62182477211849423328574430172461067532739908118360063497929275628660405528729038082876] = true := by
  decide +kernel

theorem c14 : allCells dirCell 5002 5003 [
    248701806107341925700655227426140223398358063351029886407844136692779709199619339537212] = true := by
  decide +kernel

theorem c15 : allCells dirCell 5003 5016 [
    52659984956274077645471292515778538635725595786281654685615860924,
    12855576210749225546438779871437561671111348457869715392107900, 147565899869557314212, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c16 : allCells dirCell 5016 5017 [
    835095161915404155184512955769267270645478344068148294646280915] = true := by
  decide +kernel

theorem c17 : allCells dirCell 5017 5018 [
    16487677186105450345503897785241155075936793528379758012838835177388929262417815835704972171] = true := by
  decide +kernel

theorem k5018_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5018) 2).1
      54342295667332160429096069345765731007679710530253060341229142489651).isSome = true := by
  decide +kernel

theorem k5018_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5018) 2).2
      11795637793324493135598513767011516239111148319537).isSome = true := by
  decide +kernel

theorem k5019_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5019) 2).1
      13893820336194363414337771430320215246102931086529383996007508564292403).isSome = true := by
  decide +kernel

theorem k5019_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5019) 2).2
      54273281695674843547353801712509984945550665337306672158595045471027).isSome = true := by
  decide +kernel

theorem k5020_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5020) 2).1
      15992054578243973118275337077707948816743793613308295511214850088313689651621164538508083).isSome = true := by
  decide +kernel

theorem k5020_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5020) 2).2
      999745822342135380323119064658969053976199572389921340330130203888110970524287651115825).isSome = true := by
  decide +kernel

theorem k5021_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5021) 2).1
      998268434317803966800208526396581020230974856022056870492033087157347334566736291263283).isSome = true := by
  decide +kernel

theorem k5021_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5021) 2).2
      975293902552782794761060136338179961748182837664401546028307312467824471794557746380).isSome = true := by
  decide +kernel

theorem k5022_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5022) 2).1
      3896689328938791089272122088997271287223223579830781699351717917644287735110684766924).isSome = true := by
  decide +kernel

theorem k5022_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5022) 2).2
      52811698974356060026806478224091030933174426044584522864405115596).isSome = true := by
  decide +kernel

theorem k5023_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5023) 2).1
      844323862241016532617851018049470201109283042379349227567927208652).isSome = true := by
  decide +kernel

theorem k5023_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5023) 2).2
      824570215096733350625414433059504495042813180104539133725734604).isSome = true := by
  decide +kernel

theorem c24 : allCells dirCell 5024 5025 [
    22217419256096206035077958535267895559783570722346571539875155827852461943631817286262562945046866047254002971055036231058975944945] = true := by
  decide +kernel

theorem c25 : allCells dirCell 5025 5026 [
    400063789520774008761874410773266072793206663333578343175093939414675748942619030327806081138173461959455258634273527748859042075205418940219325500] = true := by
  decide +kernel

theorem c26 : allCells dirCell 5026 5027 [
    73455869142955387122380746678523787549237401271179053228563413878880029601494062632120354937152109512749628] = true := by
  decide +kernel

theorem c27 : allCells dirCell 5027 5028 [
    15550997440236662814831351563398862004095125296706839060361490626094555098817257523772] = true := by
  decide +kernel

theorem c28 : allCells dirCell 5028 5029 [
    286811491724855904056643434545390419787822476238349926810996849450118423067601689231581319447424747950908] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4977 5029 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 4990)
      (.split 2 (.leaf _ k4990_0) (.leaf _ k4990_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4991)
      (.split 2 (.leaf _ k4991_0) (.leaf _ k4991_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4992)
      (.split 2 (.leaf _ k4992_0) (.leaf _ k4992_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4993)
      (.split 2 (.leaf _ k4993_0) (.leaf _ k4993_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4994)
      (.split 2 (.leaf _ k4994_0) (.leaf _ k4994_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4995)
      (.split 2 (.leaf _ k4995_0) (.leaf _ k4995_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4996)
      (.split 2 (.leaf _ k4996_0) (.leaf _ k4996_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16).trans <|
  (Cover.dir c17).trans <|
  (Cover.one (box := dirCellBox) (n := 5018)
      (.split 2 (.leaf _ k5018_0) (.leaf _ k5018_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5019)
      (.split 2 (.leaf _ k5019_0) (.leaf _ k5019_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5020)
      (.split 2 (.leaf _ k5020_0) (.leaf _ k5020_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5021)
      (.split 2 (.leaf _ k5021_0) (.leaf _ k5021_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5022)
      (.split 2 (.leaf _ k5022_0) (.leaf _ k5022_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5023)
      (.split 2 (.leaf _ k5023_0) (.leaf _ k5023_1))).trans <|
  (Cover.dir c24).trans <|
  (Cover.dir c25).trans <|
  (Cover.dir c26).trans <|
  (Cover.dir c27).trans <|
  (Cover.dir c28)

end C4.Cert.Dir153
