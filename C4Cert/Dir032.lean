module

public import C4Check

public section

/-! Cells `2197 ≤ n < 2276` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir032

theorem c0 : allCells dirCell 2197 2217 [
    17918183571900614340196515972992645434870286498098724899209396445223554403295825832911408907036135966065,
    147520610779390519076, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2217_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2217) 3).1
      52248777700763918191984422137055204368604357019069449984854225).isSome = true := by
  decide +kernel

theorem k2217_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2217) 3).2
      1339656495660849858898821181963597385194019939815205672807851484101869437963389590946094209732891915947047497814421093316082).isSome = true := by
  decide +kernel

theorem k2218_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2218) 3).1
      342214087742317520306691392587473991848402843410052530772879172787817143675354564565302661448853181352356880601049745313068274).isSome = true := by
  decide +kernel

theorem k2218_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2218) 3).2 2).1
      15686820627339519654976079296733865299222075112480354210512888048465383386689843448636).isSome = true := by
  decide +kernel

theorem k2218_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2218) 3).2 2).2
      13286379185090661962593910456275519658521082349286337019783891772).isSome = true := by
  decide +kernel

theorem k2219_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2219) 3).1 1).1
      212250613137228840569914358411021484087273247466350511907149435708).isSome = true := by
  decide +kernel

theorem k2219_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2219) 3).1 1).2
      13586395545509029764103537270594484537477045882614909151899077653308).isSome = true := by
  decide +kernel

theorem k2219_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2219) 3).2 2).1
      183876646705064389887937885959957340094847722300).isSome = true := by
  decide +kernel

theorem k2219_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2219) 3).2 2).2
      52998488039288388889376279740897309937697322869549763580609819196).isSome = true := by
  decide +kernel

theorem k2220_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2220) 2).1 3).1
      847084616717313895251427415743650949177836188100858871626174546748).isSome = true := by
  decide +kernel

theorem k2220_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2220) 2).1 3).2
      54160975708323123276091135837266407338273634461040245958216760736828).isSome = true := by
  decide +kernel

theorem k2220_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2220) 2).2 3).1
      211773742502990336481028030062291953104077403603154439363859301180).isSome = true := by
  decide +kernel

theorem k2220_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2220) 2).2 3).2
      13540000249992451915670813410102264355106676117871442721358654651452).isSome = true := by
  decide +kernel

theorem k2221_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2221) 3).1
      26284843793471791848313071350661807362214079837192501879220503694481372773614161621969225884523301507014614600768987110756626882599219340718745100287036).isSome = true := by
  decide +kernel

theorem k2221_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2221) 3).2 2).1
      13520389309917428683514989619299960303292820965462729897148111699004).isSome = true := by
  decide +kernel

theorem k2221_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2221) 3).2 2).2
      45806335415237906631545743119207910756591123516).isSome = true := by
  decide +kernel

theorem k2222_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2222) 1).1
      301225964438337147525673087918167269888931028259847605192332014974515031979849938729972322432257593656646550332).isSome = true := by
  decide +kernel

theorem k2222_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2222) 1).2
      301297412015652680001291334478060564427590353229554984163503085569707094621143997632110544355380984072591569138).isSome = true := by
  decide +kernel

theorem k2223_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2223) 1).1
      4592237580336617734271146406455525476328332926896782381181935814320243683902947627600759412783187595610684).isSome = true := by
  decide +kernel

theorem k2223_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2223) 1).2
      1176139999937918117290973885911314127179522645953565731090237202523827600879514853624511290167640832898101491).isSome = true := by
  decide +kernel

theorem k2224_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2224) 1).1
      823133294789405324374394964969524868651261310040359113469818428).isSome = true := by
  decide +kernel

theorem k2224_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2224) 1).2
      15551935790375681185526975921402968589652885801339611636409050080939668372292139087420).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 2225 2245 [
    17918100201660359215521571005944158761632182612927226907258417610683327908463282477881684427091339980145,
    147518965222831191172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 2245 2246 [
    833495178719128878587509060965149299248880140779166662764800275] = true := by
  decide +kernel

theorem k2246_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2246) 3).1
      3927469388355828928058413713102075914934716010377514638181736622538206662113895465970).isSome = true := by
  decide +kernel

theorem k2246_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2246) 3).2
      341420463723577203893959500250962886349639147633472620012015844408307293546324723738557881086297370564053100156350440937452785).isSome = true := by
  decide +kernel

theorem k2247_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2247) 3).1
      402492921286350779127408298822474883499121764926648342294199637131683144177828557326924982224378774584456533908279345234006223158143446931182442738).isSome = true := by
  decide +kernel

theorem k2247_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2247) 3).2
      5580986360097371097799074228016484463829970558981931157230601549798344998428627560993666474216301364368075814364309260202742892786).isSome = true := by
  decide +kernel

theorem k2248_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2248) 2).1
      1207782600550838830462221336013280336644908060195554413882731704556994001472726577297898025965631584646812004595).isSome = true := by
  decide +kernel

theorem k2248_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2248) 2).2
      4720195655611263007654578901879430383761789977303831724995711132343499234901095925336195867851879928775359548).isSome = true := by
  decide +kernel

theorem k2249_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2249) 3).1
      261687832656471439494257594476422819619397614233092383582206831883351171166282733822684623090).isSome = true := by
  decide +kernel

theorem k2249_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2249) 3).2
      255457668446014718935692888462600702559193156701175077630535709466342901532271663192720188).isSome = true := by
  decide +kernel

theorem k2250_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2250) 1).1
      1176687291627344090917674285381220564317928977008284305893100580142906262354139861814321573516218622153835324).isSome = true := by
  decide +kernel

theorem k2250_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2250) 1).2
      255195345658620355593008347335649336801298609279698075622473898103093954826558063135146812).isSome = true := by
  decide +kernel

theorem k2251_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2251) 1).1
      972459471874583307688439050842460351833545434239530437328555606172381231369888855612).isSome = true := by
  decide +kernel

theorem k2251_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2251) 1).2
      211005462226645363603747956092785361962644375503384913849217436220).isSome = true := by
  decide +kernel

theorem c17 : allCells dirCell 2252 2253 [
    1354739884991063312103549956072828503281629353279180020885132025819469914478548853308160596017518323849073495250084767519044849] = true := by
  decide +kernel

theorem c18 : allCells dirCell 2253 2274 [
    51454764726827044369324289364351377476162355394717567023033745, 147517871689820827076, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c19 : allCells dirCell 2274 2275 [
    100783769760743702644021503992038478609308907029489723300945205459197007321870055539762232590471514200203303272328092321593265825220363460474296391] = true := by
  decide +kernel

theorem k2275_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2275) 3).1
      16033106049362446753731176020602881355925818499609105721824670227788854105386787868625138).isSome = true := by
  decide +kernel

theorem k2275_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2275) 3).2
      1000892293712873926591793211649746379832153495725906751614330223946056291322996116779250).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2197 2276 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 2217)
      (.split 3 (.leaf _ k2217_0) (.leaf _ k2217_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2218)
      (.split 3 (.leaf _ k2218_0) (.split 2 (.leaf _ k2218_1) (.leaf _ k2218_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2219)
      (.split 3 (.split 1 (.leaf _ k2219_0) (.leaf _ k2219_1)) (.split 2 (.leaf _ k2219_2) (.leaf _ k2219_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2220)
      (.split 2 (.split 3 (.leaf _ k2220_0) (.leaf _ k2220_1)) (.split 3 (.leaf _ k2220_2) (.leaf _ k2220_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2221)
      (.split 3 (.leaf _ k2221_0) (.split 2 (.leaf _ k2221_1) (.leaf _ k2221_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2222)
      (.split 1 (.leaf _ k2222_0) (.leaf _ k2222_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2223)
      (.split 1 (.leaf _ k2223_0) (.leaf _ k2223_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2224)
      (.split 1 (.leaf _ k2224_0) (.leaf _ k2224_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 2246)
      (.split 3 (.leaf _ k2246_0) (.leaf _ k2246_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2247)
      (.split 3 (.leaf _ k2247_0) (.leaf _ k2247_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2248)
      (.split 2 (.leaf _ k2248_0) (.leaf _ k2248_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2249)
      (.split 3 (.leaf _ k2249_0) (.leaf _ k2249_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2250)
      (.split 1 (.leaf _ k2250_0) (.leaf _ k2250_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2251)
      (.split 1 (.leaf _ k2251_0) (.leaf _ k2251_1))).trans <|
  (Cover.dir c17).trans <|
  (Cover.dir c18).trans <|
  (Cover.dir c19).trans <|
  (Cover.one (box := dirCellBox) (n := 2275)
      (.split 3 (.leaf _ k2275_0) (.leaf _ k2275_1)))

end C4.Cert.Dir032
