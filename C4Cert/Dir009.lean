module

public import C4Check

public section

/-! Cells `1353 ≤ n < 1436` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir009

theorem k1353_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1353) 3).1 2).1
      997181893689284667937358305495716488304833906308274360327378912900562223716858832712497).isSome = true := by
  decide +kernel

theorem k1353_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1353) 3).1 2).2
      3988891225107309286679954063292213608549209966347569235928182993290037014325740677722929).isSome = true := by
  decide +kernel

theorem k1353_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1353) 3).2 2).1
      15943756582494187351947900652590835036640343801657552864384465634115704492903618824227633).isSome = true := by
  decide +kernel

theorem k1353_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1353) 3).2 2).2
      996503844857679803286548245966925911086816178580967054713881239755603274111827352378161).isSome = true := by
  decide +kernel

theorem k1354_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1354) 3).1 2).1
      63735210569801995914700211572228815636154078553761779894162869162617401196181502593423153).isSome = true := by
  decide +kernel

theorem k1354_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1354) 3).1 2).2
      844363413473602127228530389153484324230927866691956070639954226236).isSome = true := by
  decide +kernel

theorem k1354_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1354) 3).2
      4701152057517425286704819401271986852546238453062273191123644423173597496537564732243300224196425116159268041).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 1355 1356 [
    102382183039113697728469120162495085053661221206384367481720004446774969854454047425018081887717448951812422641489416824686779194055147506995154118951] = true := by
  decide +kernel

theorem c3 : allCells dirCell 1356 1378 [
    2360031989535506129217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1378 1379 [
    7613123500248657456402899368470885573924640846286665937736922274916261720317896099636137092074223437487102375612438497451780468702378127129962698151692172940251792098331] = true := by
  decide +kernel

theorem k1379_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1379) 3).1 2).1
      18044437259997374761922533724616278891910761616695310484496380256909172999427491788924167490233435754865).isSome = true := by
  decide +kernel

theorem k1379_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1379) 3).1 2).2
      18042264385468696005282571299129860686146355322852754289368185691658163536099212768166007183257212802876).isSome = true := by
  decide +kernel

theorem k1379_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1379) 3).2 2).1
      250045387340747567101024349331382401206962010926605707027130556241737096195132465443505).isSome = true := by
  decide +kernel

theorem k1379_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1379) 3).2 2).2
      72109267727004434968361706128270423337457107656444115269867155677485502763235572835911606234943080232508).isSome = true := by
  decide +kernel

theorem k1380_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1380) 3).1 2).1
      15610632776107883222677339794482308787037223024641251224272752933590794447871035119409).isSome = true := by
  decide +kernel

theorem k1380_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1380) 3).1 2).2
      3903017030093545860661603010184783986143139603689511763838434706367271604393941817137).isSome = true := by
  decide +kernel

theorem k1380_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1380) 3).2 2).1
      18413409336493369170442219287375143284829718805749087363090570893173524505293946170577736980685351629839153).isSome = true := by
  decide +kernel

theorem k1380_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1380) 3).2 2).2
      15595343161662811206175020411534078206470098223239688499629989311383839097175368219708).isSome = true := by
  decide +kernel

theorem k1381_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1381) 3).1 1).1
      216355845630244944184255874048099767010040895933499099493421080234802).isSome = true := by
  decide +kernel

theorem k1381_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1381) 3).1 1).2
      62393554640237018545332553983807066917203960703063280300846381401915479909799565404876).isSome = true := by
  decide +kernel

theorem k1381_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1381) 3).2 2).1
      249126472320749276155734446998244728039509362357364821569433447445872094974012267097148).isSome = true := by
  decide +kernel

theorem k1381_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1381) 3).2 2).2
      52806983031925458069479230480982196523982406128263044222957730876).isSome = true := by
  decide +kernel

theorem k1382_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1382) 3).1
      347419415218375837451614512651351613315196738420947636572407692113819058070611642856423632997388457307896046025501586395901013809).isSome = true := by
  decide +kernel

theorem k1382_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1382) 3).2
      21682704120184213228001735237676648510496676648917829021452440194979513066403358026303050819362994645808184528216165108515435185).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1383 1384 [
    7371759907341075255366897266649735317126625235164036646076221347838414175954487141752334592168175612029818201373749804441089910372607331124851683858787846995371537863] = true := by
  decide +kernel

theorem c10 : allCells dirCell 1384 1406 [
    2359998381864052747585, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem c11 : allCells dirCell 1406 1407 [
    118947090372835642902340214244376974153083466208025922005008039324236023976781040377517298223625453363187741205896222066485699554361104179395760746842824609144347726983] = true := by
  decide +kernel

theorem k1407_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1407) 3).1
      7423205270788834421227373616483537512920196708935235247660182423813488712434798731856412759183346917697421779954102129453666356728548548232074661548625060572580136390).isSome = true := by
  decide +kernel

theorem k1407_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1407) 3).2 1).1
      61038134835428734619369304488086831562889871793051314224188227031237423701020693938).isSome = true := by
  decide +kernel

theorem k1407_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1407) 3).2 1).2
      288475740416866731416341137900281245397646832844641973755812887751258358169650169338966090296868348613436).isSome = true := by
  decide +kernel

theorem k1408_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1408) 3).1 1).1
      3901669686008577190296747848398474625697769313801344140399657525173360878267135291964).isSome = true := by
  decide +kernel

theorem k1408_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1408) 3).1 1).2
      3905120322833484366867493290611231239556779079023983604343405676857521430112121502780).isSome = true := by
  decide +kernel

theorem k1408_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1408) 3).2 2).1
      211548182894623941476740374367345177892837663146487426568894594108).isSome = true := by
  decide +kernel

theorem k1408_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1408) 3).2 2).2
      211339441407305497430041732202140139497412732431743890992752016444).isSome = true := by
  decide +kernel

theorem k1409_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1409) 3).1
      22239171736563031766536372592781714194970607584081736316285051323915059946042048822159182404090534171886771401940609964716200472818).isSome = true := by
  decide +kernel

theorem k1409_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1409) 3).2
      22227126728714968414234446618970679442351470942790849514887598896718577914485036666186311420448613967446553760983383124158637732081).isSome = true := by
  decide +kernel

theorem k1410_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1410) 3).1
      4703722438018747541927490681346848419809697863571416257296730861065353871982419335737015059455801650616622257).isSome = true := by
  decide +kernel

theorem k1410_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1410) 3).2
      1147781596086033099416051829198798957975356765522744806646212515930715088816733798001987215925765731278257).isSome = true := by
  decide +kernel

theorem c16 : allCells dirCell 1411 1434 [
    84699717735546301836189677885182134372479885758245957987762752465494725311243032696367570662894554541301203033047335438213189,
    2359982824874717173825, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem c17 : allCells dirCell 1434 1435 [
    25174901715093149620359881179560239826927159917499928434634898413279426264522072564602972348157671156834800623437794041046776523042223667635214087] = true := by
  decide +kernel

theorem k1435_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1435) 3).1
      115959061588847322625577109331500585471126151053068953986262210684439402811026463883796332911441419652048484922878335508738478189092213971379161573813064771997890034).isSome = true := by
  decide +kernel

theorem k1435_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1435) 3).2
      21780366353885490117571853519757533895967306252986078667015613720522142733752621179256833540714861170794253147501179381093313778).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1353 1436 :=
  (Cover.one (box := dirCellBox) (n := 1353)
      (.split 3 (.split 2 (.leaf _ k1353_0) (.leaf _ k1353_1)) (.split 2 (.leaf _ k1353_2) (.leaf _ k1353_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1354)
      (.split 3 (.split 2 (.leaf _ k1354_0) (.leaf _ k1354_1)) (.leaf _ k1354_2))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1379)
      (.split 3 (.split 2 (.leaf _ k1379_0) (.leaf _ k1379_1)) (.split 2 (.leaf _ k1379_2) (.leaf _ k1379_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1380)
      (.split 3 (.split 2 (.leaf _ k1380_0) (.leaf _ k1380_1)) (.split 2 (.leaf _ k1380_2) (.leaf _ k1380_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1381)
      (.split 3 (.split 1 (.leaf _ k1381_0) (.leaf _ k1381_1)) (.split 2 (.leaf _ k1381_2) (.leaf _ k1381_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1382)
      (.split 3 (.leaf _ k1382_0) (.leaf _ k1382_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 1407)
      (.split 3 (.leaf _ k1407_0) (.split 1 (.leaf _ k1407_1) (.leaf _ k1407_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1408)
      (.split 3 (.split 1 (.leaf _ k1408_0) (.leaf _ k1408_1)) (.split 2 (.leaf _ k1408_2) (.leaf _ k1408_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1409)
      (.split 3 (.leaf _ k1409_0) (.leaf _ k1409_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1410)
      (.split 3 (.leaf _ k1410_0) (.leaf _ k1410_1))).trans <|
  (Cover.dir c16).trans <|
  (Cover.dir c17).trans <|
  (Cover.one (box := dirCellBox) (n := 1435)
      (.split 3 (.leaf _ k1435_0) (.leaf _ k1435_1)))

end C4.Cert.Dir009
