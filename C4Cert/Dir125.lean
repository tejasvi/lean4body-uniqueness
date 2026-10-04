module

public import C4Check

public section

/-! Cells `3872 ≤ n < 3977` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir125

theorem c0 : allCells dirCell 3872 3873 [
    1208925593247133691999280071043826138568499706015994957119281234679501653742322065466936181443820246978267786446] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3873 3874 [
    22270714486925087990393271142498023309747594927619031766334253413799180350838273323507688894797723327870444201629320171704957595889] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3874 3875 [
    4710958285557524280425706835196733263928350640179952087347225779750816936912599421154136909984662409413062898] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3875 3876 [
    1176784128325724350014781071775048605303855730674220991898081644026176377310912575097241647139823162111684850] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3876 3877 [
    996174165327548744477490334080845065786276092198762046990471473501848034882110259819185] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3877 3878 [
    248919910002412805818294589148305137793079778460977169126321766657145673811670087977788] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3878 3879 [
    286880568611124812963778026059906074990608803547049793919606937834407588432631762676716644526028381707452] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3879 3880 [
    71699680598470141090168434274490435460671988198759798585081051115682643896215322849359869986713634823356] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3880 3897 [
    60720704194299808542015462042588316575923878550758435610798178578756436407464192369,
    51424024949523453779681992508528113081100944953291207464114769, 147555664584556416836, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3897 3899 [
    705048936823896268774415498393711836919235,
    15668495892360448156299207146695377229047318300943052960068654050610835577908626813746] = true := by
  decide +kernel

theorem c10 : allCells dirCell 3899 3900 [
    3908953755644037699669316255140093713811445003233786092546336602624349287416070526771] = true := by
  decide +kernel

theorem c11 : allCells dirCell 3900 3901 [
    243996076411994853566224481183460988793774498359530421651625538589101223697257649970] = true := by
  decide +kernel

theorem c12 : allCells dirCell 3901 3902 [
    975173601809203951425062527550316789755800509151638944429497467435321703588704443570] = true := by
  decide +kernel

theorem c13 : allCells dirCell 3902 3904 [
    974181914934947928352946110124263970413594765621575850449138121452550415287631305906,
    206127795554808565997052911340871771934816574308979087964001714] = true := by
  decide +kernel

theorem c14 : allCells dirCell 3904 3906 [
    51500309081546446401782020169339267653803694014503213072974194,
    51475738173470646499922925484719862306545812264431621552592242] = true := by
  decide +kernel

theorem c15 : allCells dirCell 3906 3909 [
    51456700963121443727606960272906785892942675218548609729981810,
    12860519352941157574118008551036981604829959433825755590272380,
    43564848328197861834386913707250743072860] = true := by
  decide +kernel

theorem c16 : allCells dirCell 3909 3949 [
    43556200760605071637254980624248730621020, 147555116271861330180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
    2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k3949_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3949) 3).1
      6014173371685780141666293077533937565197123333617973709182967917363351107399650739238971318109192554648441019).isSome = true := by
  decide +kernel

theorem k3949_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3949) 3).2 2).1
      61143364796294725184652751836212616013806190524027814527816997890421233419).isSome = true := by
  decide +kernel

theorem k3949_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).2 2).2 3).1
      5147351553174817925413457909880519009527124775640429805000730420986209766014889759298638964058812843117343846).isSome = true := by
  decide +kernel

theorem k3949_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).2 2).2 3).2
      17591733913495126481398891909106740861905807215658089347818861760346477878984894478113621094).isSome = true := by
  decide +kernel

theorem k3950_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3950) 2).1
      4746275426042566773787649620117687499176413600740301087328996845106701268320489041279210509435145889784879).isSome = true := by
  decide +kernel

theorem k3950_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).1 3).1
      4332137920009927282558717393762803707793474633017723407128255857514295736921566969523414118).isSome = true := by
  decide +kernel

theorem k3950_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).1 3).2
      23344842340196497880067895666126586459169914307206666426921817463568391441064173003772670637393251162620533135567461963566366172310).isSome = true := by
  decide +kernel

theorem k3950_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).2 2).1
      1055080690704199409300491842986807433164298083423083437365534510917455911633241465515074663).isSome = true := by
  decide +kernel

theorem k3950_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).2 2).2 3).1
      1013771110381837654577139604872284346291470160553269190118583544256349411496520539333).isSome = true := by
  decide +kernel

theorem k3950_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).2 2).2 3).2
      1007756442735639261090917223830998467853173920001982320767459807723079911414781745033).isSome = true := by
  decide +kernel

theorem k3951_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3951) 2).1
      1137980488776950795619016410283436339073359228728324758621450542522452294791243401112549733452760488715).isSome = true := by
  decide +kernel

theorem k3951_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3951) 2).2 3).1 2).1
      16709098283688870787436160725703612673177446781591380793473235481627912921922912645221573723).isSome = true := by
  decide +kernel

theorem k3951_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3951) 2).2 3).1 2).2 3).1
      1002462363282120639591637763480605759451771151085122805288825857577467746518930478985).isSome = true := by
  decide +kernel

theorem k3951_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3951) 2).2 3).1 2).2 3).2
      54067883779153691389414980494364905680840698809214827773889843913).isSome = true := by
  decide +kernel

theorem k3951_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3951) 2).2 3).2 2).1
      4048988405076874228191129284560921135279225875471819496886293690874830601278794690638951).isSome = true := by
  decide +kernel

theorem k3951_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3951) 2).2 3).2 2).2
      4151301330665369401280237257662564309917811855492113415961604388144385830226690623432776231).isSome = true := by
  decide +kernel

theorem k3952_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3952) 2).1
      4208806661858728896041240444551957657204514875916925859032389330253777180594125434826257143563).isSome = true := by
  decide +kernel

theorem k3952_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3952) 2).2 3).1 2).1
      15740081109276302091418040949004379458853088882681461182514105787336523520374792485159).isSome = true := by
  decide +kernel

theorem k3952_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3952) 2).2 3).1 2).2
      16134218510275339829580132503114753513217724766544779299499065888155742972965134453650983).isSome = true := by
  decide +kernel

theorem k3952_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3952) 2).2 3).2 2).1
      980660768636288256695356855301905636363378737504564769145831337094534223906109851079).isSome = true := by
  decide +kernel

theorem k3952_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3952) 2).2 3).2 2).2
      15702083935197073878745549693129762995350156973222147076950229686646052546285575526087).isSome = true := by
  decide +kernel

theorem k3953_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3953) 2).1
      2940145278585581514049609031831188296180114408715).isSome = true := by
  decide +kernel

theorem k3953_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3953) 2).2 3).1
      1364606112031695272514172250165324775339908454313976204875340991451195707933005558263768825854686585444736575253253369443903798).isSome = true := by
  decide +kernel

theorem k3953_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3953) 2).2 3).2
      1154166573967683766277509550660175743186212467528329883076022953475077461729883528165193130042793825240518).isSome = true := by
  decide +kernel

theorem k3954_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3954) 2).1
      45856840740555354482007988399296372543245881611).isSome = true := by
  decide +kernel

theorem k3954_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3954) 2).2
      127978030239432221774968276753902892606245871319828277957737082952764970861700933519087914753869554471185063997865452400010889720004112892303458834203).isSome = true := by
  decide +kernel

theorem c23 : allCells dirCell 3955 3956 [
    23329384001144600370241025351749702423872884450840341096667039130122391834484334240136826770309743022737307393625950574013570530589296394] = true := by
  decide +kernel

theorem c24 : allCells dirCell 3956 3977 [
    732526336338718910828422295712333511566837159430, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3872 3977 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16).trans <|
  (Cover.one (box := dirCellBox) (n := 3949)
      (.split 3 (.leaf _ k3949_0) (.split 2 (.leaf _ k3949_1) (.split 3 (.leaf _ k3949_2) (.leaf _ k3949_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3950)
      (.split 2 (.leaf _ k3950_0) (.split 3 (.split 3 (.leaf _ k3950_1) (.leaf _ k3950_2)) (.split 2 (.leaf _ k3950_3) (.split 3 (.leaf _ k3950_4) (.leaf _ k3950_5)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3951)
      (.split 2 (.leaf _ k3951_0) (.split 3 (.split 2 (.leaf _ k3951_1) (.split 3 (.leaf _ k3951_2) (.leaf _ k3951_3))) (.split 2 (.leaf _ k3951_4) (.leaf _ k3951_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3952)
      (.split 2 (.leaf _ k3952_0) (.split 3 (.split 2 (.leaf _ k3952_1) (.leaf _ k3952_2)) (.split 2 (.leaf _ k3952_3) (.leaf _ k3952_4))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3953)
      (.split 2 (.leaf _ k3953_0) (.split 3 (.leaf _ k3953_1) (.leaf _ k3953_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3954)
      (.split 2 (.leaf _ k3954_0) (.leaf _ k3954_1))).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24)

end C4.Cert.Dir125
