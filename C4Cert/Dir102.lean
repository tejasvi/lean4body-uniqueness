module

public import C4Check

public section

/-! Cells `3425 ≤ n < 3489` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir102

theorem k3425_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3425) 2).1
      5567255940995150013327132694912450493011418460728817801242951999496937456071486954782342172883833482422813666488236033013498199100).isSome = true := by
  decide +kernel

theorem k3425_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3425) 2).2
      3995172140038593650250741203412999126388997946795392723712207668753930787899092065205308).isSome = true := by
  decide +kernel

theorem k3426_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3426) 2).1
      63837258223338513142398427748041359321800699488984409226559137240024905350038584887655484).isSome = true := by
  decide +kernel

theorem k3426_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3426) 2).2
      3989925872818390447546986544831310461038341932484696080612563621987363478900672930036796).isSome = true := by
  decide +kernel

theorem k3427_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3427) 1).1
      996598062102483777918985328393268329865743215634260664950170560416292369803904894616380).isSome = true := by
  decide +kernel

theorem k3427_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3427) 1).2
      216111070801414575614907744938286686582128784918294157834040993037372).isSome = true := by
  decide +kernel

theorem k3428_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3428) 2).1
      15935540242642931681546660785657815872673993267703784384324495536861823280584055619044156).isSome = true := by
  decide +kernel

theorem k3428_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3428) 2).2
      843634781628369136531199920419517349687274841838144433754648331068).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 3429 3430 [
    1043888360227888609007222141332006635537860158816957963250461087931058815491662372559071463665] = true := by
  decide +kernel

theorem k3430_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3430) 1).1
      52679243545754954633984202524528347656521583194129728569599314492).isSome = true := by
  decide +kernel

theorem k3430_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3430) 1).2
      45695870720185772490335153326039580898393311804).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3431 3432 [
    21159540862167033172243324910746410896756701455825718777083507253505895522813882518498498496560746685690690042090453505367473] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3432 3449 [
    51425073775094187017485437829083905736238513710022023634766545, 147551379031799588164, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3449 3450 [
    4644417001018908949155028617192459003911613219796979736002143758031572014561845332931039207542922219410503] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3450 3451 [
    412944913192888949712233363277884046186163412195036377348748952920484545708825563834087240408653547329684286738989101788089668080484931716823103855822] = true := by
  decide +kernel

theorem k3451_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3451) 2).1
      4008028998875820774843076124749764704945548487541788120377059317742954346067386540870449).isSome = true := by
  decide +kernel

theorem k3451_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3451) 2).2
      13571573870857038326962821108760193350422778840121628730252794219315).isSome = true := by
  decide +kernel

theorem k3452_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3452) 2).1
      867305490627659569411190292537343634508292490102707351774666687134780).isSome = true := by
  decide +kernel

theorem k3452_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3452) 2).2
      62502610611568806579842399513065094442511283871498465562967664531533315724958806944828).isSome = true := by
  decide +kernel

theorem k3453_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3453) 2).1
      998594646570601881179058665947662670704749104626823433565558495823680067424050222414908).isSome = true := by
  decide +kernel

theorem k3453_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3453) 2).2
      998583808431089256130942089946576888593619118879703365152829255188522447474706399050812).isSome = true := by
  decide +kernel

theorem k3454_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3454) 2).1
      18400403986415274815532114938132108381906306506006189458492349590495594601802743403124829896481789991238716).isSome = true := by
  decide +kernel

theorem k3454_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3454) 2).2
      211224810348594427201337785734035813587904910652312446606471642172).isSome = true := by
  decide +kernel

theorem k3455_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3455) 1).1
      52760696296750517706269914753628146241570324414969394324417409596).isSome = true := by
  decide +kernel

theorem k3455_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3455) 1).2
      52783819643827852561703458350068787726506350104370380707866210876).isSome = true := by
  decide +kernel

theorem k3456_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3456) 1).1
      52725861741355336085809487209203797713324658580745308955417637436).isSome = true := by
  decide +kernel

theorem k3456_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3456) 1).2
      52730112074827926915061487452423197086047048278873169055967474236).isSome = true := by
  decide +kernel

theorem k3457_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3457) 1).1
      11427372699601657662646826834323835369932966460).isSome = true := by
  decide +kernel

theorem k3457_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3457) 1).2
      45713439456259966443985578603905151729418095164).isSome = true := by
  decide +kernel

theorem c17 : allCells dirCell 3458 3459 [
    63692475589237771958771095289545579333139464226587952635245488525258108504803154660062449] = true := by
  decide +kernel

theorem c18 : allCells dirCell 3459 3461 [
    15545568361681493459982337632349241951332820117576983300411038588235953482331829773745,
    51424872922403105654871682267560296882700986840211350635712209] = true := by
  decide +kernel

theorem c19 : allCells dirCell 3461 3478 [
    147550546083038259284, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2821570937503327485833531772109528541666579] = true := by
  decide +kernel

theorem c20 : allCells dirCell 3478 3479 [
    18957779027370333268013013824412425321589070875534914148378169113482911361238412368887170442014159691982476491] = true := by
  decide +kernel

theorem c21 : allCells dirCell 3479 3480 [
    4199578710732600030208853561659914620896844494864596614554864398355547334778811265968979594443] = true := by
  decide +kernel

theorem c22 : allCells dirCell 3480 3481 [
    21776838950120883272637390863000870562215833675086433166349781069916018283974205353632085080149117499618225929817948912858131250] = true := by
  decide +kernel

theorem c23 : allCells dirCell 3481 3482 [
    22268255296750158299184576135414710892830277626357332735435364197488312730203343872516821154407755411489896793767806981518981918962] = true := by
  decide +kernel

theorem c24 : allCells dirCell 3482 3483 [
    21723088087435732488832498678643848354807586869003031838307912819542273817571383545714306716856579796509941170356435712585625842] = true := by
  decide +kernel

theorem c25 : allCells dirCell 3483 3484 [
    4706746495877048054582003928738107170222342787090253644514405438600900256958551937476321057134816664472635633] = true := by
  decide +kernel

theorem c26 : allCells dirCell 3484 3485 [
    21184091690753484224662912618304537235208742206099452216773356344152410308419494254180068164187868482730466757899974102572465] = true := by
  decide +kernel

theorem c27 : allCells dirCell 3485 3486 [
    1147781809151222883992035449538642329193203859080063216090878036993768259452269249848626823912084534680764] = true := by
  decide +kernel

theorem c28 : allCells dirCell 3486 3487 [
    286835995367657206914797029875376285816584812625985267975953997400543086216227432658481787949714274999484] = true := by
  decide +kernel

theorem c29 : allCells dirCell 3487 3489 [
    3886387040800078135001960829809168360056278556565817317751132420431539637458804205937,
    51424681647807904139599608565710241538629233276206350554204113] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3425 3489 :=
  (Cover.one (box := dirCellBox) (n := 3425)
      (.split 2 (.leaf _ k3425_0) (.leaf _ k3425_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3426)
      (.split 2 (.leaf _ k3426_0) (.leaf _ k3426_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3427)
      (.split 1 (.leaf _ k3427_0) (.leaf _ k3427_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3428)
      (.split 2 (.leaf _ k3428_0) (.leaf _ k3428_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 3430)
      (.split 1 (.leaf _ k3430_0) (.leaf _ k3430_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 3451)
      (.split 2 (.leaf _ k3451_0) (.leaf _ k3451_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3452)
      (.split 2 (.leaf _ k3452_0) (.leaf _ k3452_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3453)
      (.split 2 (.leaf _ k3453_0) (.leaf _ k3453_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3454)
      (.split 2 (.leaf _ k3454_0) (.leaf _ k3454_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3455)
      (.split 1 (.leaf _ k3455_0) (.leaf _ k3455_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3456)
      (.split 1 (.leaf _ k3456_0) (.leaf _ k3456_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3457)
      (.split 1 (.leaf _ k3457_0) (.leaf _ k3457_1))).trans <|
  (Cover.dir c17).trans <|
  (Cover.dir c18).trans <|
  (Cover.dir c19).trans <|
  (Cover.dir c20).trans <|
  (Cover.dir c21).trans <|
  (Cover.dir c22).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24).trans <|
  (Cover.dir c25).trans <|
  (Cover.dir c26).trans <|
  (Cover.dir c27).trans <|
  (Cover.dir c28).trans <|
  (Cover.dir c29)

end C4.Cert.Dir102
