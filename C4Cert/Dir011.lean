module

public import C4Check

public section

/-! Cells `1573 ≤ n < 1603` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir011

theorem k1573_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).1 2).1
      288896486069622203193436053206667833896704766395689867176741477675525560078816793354959132880820096347405).isSome = true := by
  decide +kernel

theorem k1573_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).1 2).2
      288942838457738417114232223941409301030080609713594600780441080301107931738415077988499434620388011784461).isSome = true := by
  decide +kernel

theorem k1573_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).2 2).1
      6283808664959235959356175907745384853418883135754194508746021078494516925602854519213470033372518119730140638935141563295824827248055320421976141).isSome = true := by
  decide +kernel

theorem k1573_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).2 2).2
      1362016247148056232399394813259150628120488392812155117407411605546423557119772363266009638044780193866470458301953575531531853).isSome = true := by
  decide +kernel

theorem k1573_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).1 2).1
      4622269583625801095846503666187827134407022963294771689763886256563857057323364332659780033380811286877959).isSome = true := by
  decide +kernel

theorem k1573_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).1 2).2
      18495645982048018288562688230546249408997780778900015704257995614994592978506848317593071741160088978998471).isSome = true := by
  decide +kernel

theorem k1573_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).2 2).1
      100556121917073588592033641083999246209965524544316404115951719888369239432631750500750210562260856430248246763559777668657757143423159935850644045).isSome = true := by
  decide +kernel

theorem k1573_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).2 2).2 3).1
      244602505248920375614561463527016592668653827947955490043563826763295142790075241841).isSome = true := by
  decide +kernel

theorem k1573_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).2 2).2 3).2
      61126255498114598660445754937124145175385705246930977838948343408693909383592742257).isSome = true := by
  decide +kernel

theorem k1574_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1574) 2).1 2).1
      3724528332682454091792925729277411148918645820817162265757953064305052780717916113133379813710841484328291881974286530421125399).isSome = true := by
  decide +kernel

theorem k1574_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).1 2).2 3).1
      295097204528282071903596680158324653460762434202171956897690961616131721270514337343816385620587976493970637).isSome = true := by
  decide +kernel

theorem k1574_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).1 2).2 3).2
      60976245941622464275232994513748138022019978662610022671879371105576746763442124101).isSome = true := by
  decide +kernel

theorem k1574_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).1 2).1
      1180155140450908282534007375238575726301916311294897763795586505402159564969041474590849975103181981685544141).isSome = true := by
  decide +kernel

theorem k1574_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).1 2).2
      1394149301009501747000120526190687555343578836555351921161058081758633765037190913322560417849601696952777323826933350779836363981).isSome = true := by
  decide +kernel

theorem k1574_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).2 2).1
      62424759217910855803748033877270863102442793715488806448693980804882697863981229104305).isSome = true := by
  decide +kernel

theorem k1574_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).2 2).2
      64051515458098485511725253638328720084856931427833282203423415015645435733675205843440517).isSome = true := by
  decide +kernel

theorem k1575_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1575) 2).1
      6937976766000109362711330627945531769381835601540648054461213047549974).isSome = true := by
  decide +kernel

theorem k1575_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1575) 2).2 2).1
      25046645660673441471206647273222518950777239374137823324778034297643463640329909357883033474842345558973822512406455540165494004522260776542763287).isSome = true := by
  decide +kernel

theorem k1575_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1575) 2).2 2).2 3).1
      15594960931786240832012530143565173700477598516008428746875483153812424465089376442161).isSome = true := by
  decide +kernel

theorem k1575_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1575) 2).2 2).2 3).2
      15223985777565422494254471108099802428084682267970370140831702276815934156278598001).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1576 1600 [
    22757185325898910379948610882568892762058379029162340486060793192703449029982684290795182977757773317392693945726343141483109911961094,
    1266967762231631793212387426, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1600 1601 [
    1108066641462411494376437172079915209090565622788033275714259442233424037601877450897175701200405475] = true := by
  decide +kernel

theorem k1601_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1601) 3).1 2).1 3).1
      5472825330373486055443419998118515990386097382639192172547110581564849756529091470095295659684999039989980608851809958600967238).isSome = true := by
  decide +kernel

theorem k1601_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1601) 3).1 2).1 3).2
      21854459464742120744169757738381725149390968599322564935177060099225361670505235118317766924835615346369077961052298932525910601).isSome = true := by
  decide +kernel

theorem k1601_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1601) 3).1 2).2 3).1
      342492830928642069880740278048523248695090747757005114777523324417305653274686329974983749142536948364279238369529723025982561).isSome = true := by
  decide +kernel

theorem k1601_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1601) 3).1 2).2 3).2
      1186040109141239285771844254294986812020097501294992815581089025894703327710754617848637945743266403952020749).isSome = true := by
  decide +kernel

theorem k1601_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).1 3).1 1).1
      15300054812522707167460821900210493025220878490517607455788027935754809150635156850).isSome = true := by
  decide +kernel

theorem k1601_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).1 3).1 1).2
      3916701903651268503839731977774415239984223995484274851712536795536886393012793513778).isSome = true := by
  decide +kernel

theorem k1601_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).1 3).2 1).1
      61233799238693564788053124825848240486105431008632701609189104384560437107877124466).isSome = true := by
  decide +kernel

theorem k1601_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).1 3).2 1).2
      3913558200896143323214108399196170789395479230894109945540532685908283958372447737650).isSome = true := by
  decide +kernel

theorem k1601_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).2 3).1 1).1
      15314944972740258156027297028211085463946201569994679926165123650126615399923663218).isSome = true := by
  decide +kernel

theorem k1601_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).2 3).1 1).2
      250862987175894596248479898066654325413791860090579107495647462526501091025559301741746).isSome = true := by
  decide +kernel

theorem k1601_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).2 3).2 1).1
      244824896622460345163063540802190586735797922223443219977121310556206683484766266802).isSome = true := by
  decide +kernel

theorem k1601_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1601) 3).2 2).2 3).2 1).2
      3916676930563411192841283575556866582298405985132873016134170636417761029670726047538).isSome = true := by
  decide +kernel

theorem k1602_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).1 3).1 1).1
      211943466602788065972584037786403257442258642130918509912720347826).isSome = true := by
  decide +kernel

theorem k1602_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).1 3).1 1).2
      977716725363085833493624126002498278752064675470653080421949271535390990796523558370).isSome = true := by
  decide +kernel

theorem k1602_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).1 3).2 1).1
      244292290327152689664448926319523926991665660638163656181916750486341244433096037858).isSome = true := by
  decide +kernel

theorem k1602_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).1 3).2 1).2
      244282015249242381521133495603185251276491078549916757506827700397885172981459928546).isSome = true := by
  decide +kernel

theorem k1602_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).2 2).1
      102771033555498914916776002917324172997897625050759775177831565049600853717041404244595491601021285783073201268319246580434551227943245445699002522821).isSome = true := by
  decide +kernel

theorem k1602_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1602) 2).1 3).2 2).2
      89108992835870277739406554434065750215080578191748988536500397362997583225912341478429639647833861400097960118474639035448974399373).isSome = true := by
  decide +kernel

theorem k1602_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).1 3).1 1).1
      15679141057042280869691292260415367708999195284999824682600699672088978566502704313929).isSome = true := by
  decide +kernel

theorem k1602_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).1 3).1 1).2
      3913510735195788045761395646649703680532108385455205854608803217345190679037395965746).isSome = true := by
  decide +kernel

theorem k1602_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).1 3).2 1).1
      977506180066593303973210251366127058547158267499253678993551520979014247550542898658).isSome = true := by
  decide +kernel

theorem k1602_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).1 3).2 1).2
      978645886321105276876347944655427336544739880354151519467809205699603808612388488674).isSome = true := by
  decide +kernel

theorem k1602_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).2 1).1
      22305290296172077318448472086448809037697573237063271644404139466792096603924220410128055987357166002646763221290851902028784621451).isSome = true := by
  decide +kernel

theorem k1602_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1602) 2).2 3).2 1).2
      22286064020436794201887810597094565799385393134092534038806091014520536524071097057921326827896544136146508226364624640469439387531).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1573 1603 :=
  (Cover.one (box := dirCellBox) (n := 1573)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1573_0) (.leaf _ k1573_1)) (.split 2 (.leaf _ k1573_2) (.leaf _ k1573_3))) (.split 3 (.split 2 (.leaf _ k1573_4) (.leaf _ k1573_5)) (.split 2 (.leaf _ k1573_6) (.split 3 (.leaf _ k1573_7) (.leaf _ k1573_8)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1574)
      (.split 2 (.split 2 (.leaf _ k1574_0) (.split 3 (.leaf _ k1574_1) (.leaf _ k1574_2))) (.split 3 (.split 2 (.leaf _ k1574_3) (.leaf _ k1574_4)) (.split 2 (.leaf _ k1574_5) (.leaf _ k1574_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1575)
      (.split 2 (.leaf _ k1575_0) (.split 2 (.leaf _ k1575_1) (.split 3 (.leaf _ k1575_2) (.leaf _ k1575_3))))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1601)
      (.split 3 (.split 2 (.split 3 (.leaf _ k1601_0) (.leaf _ k1601_1)) (.split 3 (.leaf _ k1601_2) (.leaf _ k1601_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k1601_4) (.leaf _ k1601_5)) (.split 1 (.leaf _ k1601_6) (.leaf _ k1601_7))) (.split 3 (.split 1 (.leaf _ k1601_8) (.leaf _ k1601_9)) (.split 1 (.leaf _ k1601_10) (.leaf _ k1601_11)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1602)
      (.split 2 (.split 3 (.split 3 (.split 1 (.leaf _ k1602_0) (.leaf _ k1602_1)) (.split 1 (.leaf _ k1602_2) (.leaf _ k1602_3))) (.split 2 (.leaf _ k1602_4) (.leaf _ k1602_5))) (.split 3 (.split 3 (.split 1 (.leaf _ k1602_6) (.leaf _ k1602_7)) (.split 1 (.leaf _ k1602_8) (.leaf _ k1602_9))) (.split 1 (.leaf _ k1602_10) (.leaf _ k1602_11)))))

end C4.Cert.Dir011
