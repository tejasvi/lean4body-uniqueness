module

public import C4Check

public section

/-! Cells `1997 ≤ n < 2022` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir023

theorem k1997_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1997) 2).1
      63747493468090050442102807558324350324057236981766289770030496721235268687621831961624662).isSome = true := by
  decide +kernel

theorem k1997_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1997) 2).2 3).1
      249077305261099766076083838048237820501707141386744697155449832774949340849753121789745).isSome = true := by
  decide +kernel

theorem k1997_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1997) 2).2 3).2
      3891082352096047535037344311623942159239325494091622246867561949514440557398035696013).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 1998 2019 [
    22201553272292424210809294886466101396421067002545619157509226313240932977186190765858563829965396632512490034919684923767854732314,
    24291875648854245999883378, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k2019_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2019) 3).1
      4223097252561521913192662278791300574108925271354039939568124450906209047026151728586768782).isSome = true := by
  decide +kernel

theorem k2019_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2019) 3).2 2).1 3).1
      16005496870427811137626571556638349081391785639480683561850355019777115710075810374854).isSome = true := by
  decide +kernel

theorem k2019_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2019) 3).2 2).1 3).2
      419317990294668528170050752482289861700218528631031833552038762592182610295235147407550330157574618153068447011347465555572506052513681847140259486747).isSome = true := by
  decide +kernel

theorem k2019_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2019) 3).2 2).2
      1982461914058275485823911517652643345007283562524776467244912312853634186244904470412500599767510819839097419856887762433118984150760814231966460985192770785497954173934619).isSome = true := by
  decide +kernel

theorem k2020_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).1 3).1
      1017634548690350935651097561912969088286902878698489301020108482730284425812766364889142).isSome = true := by
  decide +kernel

theorem k2020_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).1 3).2
      1171501660027685726343402831946659359452323459174975781646619813012194539477453219969012128107255840039173).isSome = true := by
  decide +kernel

theorem k2020_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).2 2).1
      344705750042638252643387428821790434124053462961348619107891820765379295043367258442545581166128621850664161363393114578152525).isSome = true := by
  decide +kernel

theorem k2020_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).2 2).2
      18265160481549734425959204218170862699978205305717545285224179594991147963253382474082471354496391671153).isSome = true := by
  decide +kernel

theorem k2020_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).2 3).1 3).1
      3981160128438260122904393763337582954423277926619763374833871981070910324351196557837).isSome = true := by
  decide +kernel

theorem k2020_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).2 3).1 3).2
      18331383205211048856045616240347824955427449633678405366444708632627319064896284503515256109711321175761).isSome = true := by
  decide +kernel

theorem k2020_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).2 3).2 3).1
      292885429315420108225723409853197837102989200787866692566797197575299671283360257243575041947555571655941).isSome = true := by
  decide +kernel

theorem k2020_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).2 3).2 3).2
      86331929884285576644804754931899388817901340806798196257103043611663373432854825818460788333664350049214045418313498020007241).isSome = true := by
  decide +kernel

theorem k2020_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).1 2).1
      5501507857526627453264066292122363563548044313090874118160629888365188720640085186920270479107266928932422541611781722004340549).isSome = true := by
  decide +kernel

theorem k2020_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).1 2).2
      6349389796794254639515556136170056216464516178479174795189598952734479569817146031227438666631243690475828186677369346979982173725757154143844677).isSome = true := by
  decide +kernel

theorem k2020_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).2 1).1
      21469524423738410128624740428242286527872051640270086884399582003132588758510743953066440744415626221100558700531862630718898).isSome = true := by
  decide +kernel

theorem k2020_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).2 1).2
      87914262285493695528208328675499290327442443106345313400639267366407901657577753762181117059136571802258030268532762853429050546).isSome = true := by
  decide +kernel

theorem k2020_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).1 3).1
      16205664771229392330681612937111777155513586997096488416590071495459261826319892455669577).isSome = true := by
  decide +kernel

theorem k2020_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).1 3).2
      1195500231547849150626118157086253231933785583735640772177556251081071588419925780376340008806725386342722885).isSome = true := by
  decide +kernel

theorem k2020_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).2 3).1
      1625537037690369985977672439948740716126858983849228115529306421390603231912615321508798270341985496950956920086048663347302171581977198854711727561).isSome = true := by
  decide +kernel

theorem k2020_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).2 3).2 1).1
      15416451163558854576578173733810684221757306877971948861401057140956549165023665522).isSome = true := by
  decide +kernel

theorem k2020_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).2 3).2 1).2
      53448760312913153509825208239731245080482048305949925766534118572).isSome = true := by
  decide +kernel

theorem k2021_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).1 1).1
      1371690600311999229965754522632427370360204978029582756514836106809841475129988605372507986579527144202799325322307295377748658).isSome = true := by
  decide +kernel

theorem k2021_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).1 1).2
      21941502871733789426898354630972037394691372290236987775392792768146329342545279369465972371973626439116981413696338084453834546).isSome = true := by
  decide +kernel

theorem k2021_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).2 1).1
      1369368022893439275629149111114956395810865251817455863991785557937005773579389503442672388749886165207435173530835833649454898).isSome = true := by
  decide +kernel

theorem k2021_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).2 1).2
      74212146350132997147279911625039891632028463839657695436163454067815998467065455457069419781883635624696626).isSome = true := by
  decide +kernel

theorem k2021_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 3).1 1).1
      21455695610000182747645758657748049590197709281322721305627307794377061335316052929357678468230834455037749858178010207575474).isSome = true := by
  decide +kernel

theorem k2021_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 3).1 1).2
      21965275033879639247729535853581218797130350351665511586531349363797430873707655291672551698875561825143378618874918844101131442).isSome = true := by
  decide +kernel

theorem k2021_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 3).2 1).1
      62931959717548028985069278530379211161540915641883648729399938131179779540822025067698).isSome = true := by
  decide +kernel

theorem k2021_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 3).2 1).2
      1006810338462159206375645362063052696861351509874049604734116247938302519456791642610482).isSome = true := by
  decide +kernel

theorem k2021_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).1 1).1
      18531172222662047693957178799605827320097437989155979522467349935506966816904565243388937017955482255874866).isSome = true := by
  decide +kernel

theorem k2021_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).1 1).2
      74115248374767427920668875048854625107117259193255441823983533212541433609765047279502761556685585188772658).isSome = true := by
  decide +kernel

theorem k2021_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).2 1).1
      5462008608433718079395211581199741442946744868378658975936643283456677933369099103943235116004352068127734932388835260795050801).isSome = true := by
  decide +kernel

theorem k2021_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).2 1).2
      5461611683341116393473069489362168793896432643378923883761944387472662844305315679058989465917027148463749732980343444205853489).isSome = true := by
  decide +kernel

theorem k2021_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 3).1 1).1
      15711679451961615012181829300258951770008198021771360676777283180353953033512598854450).isSome = true := by
  decide +kernel

theorem k2021_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 3).1 1).2
      1005389128127524769726004623523523932845130559441337960909274857068834669804205168499506).isSome = true := by
  decide +kernel

theorem k2021_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 3).2 1).1
      62765919101143999370965107035975228845646624052089241472721979151029589325372490210098).isSome = true := by
  decide +kernel

theorem k2021_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 3).2 1).2
      1004168485902372395159185684221475827076271372252636990799593817924596364991467144977202).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1997 2022 :=
  (Cover.one (box := dirCellBox) (n := 1997)
      (.split 2 (.leaf _ k1997_0) (.split 3 (.leaf _ k1997_1) (.leaf _ k1997_2)))).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 2019)
      (.split 3 (.leaf _ k2019_0) (.split 2 (.split 3 (.leaf _ k2019_1) (.leaf _ k2019_2)) (.leaf _ k2019_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2020)
      (.split 3 (.split 2 (.split 3 (.split 3 (.leaf _ k2020_0) (.leaf _ k2020_1)) (.split 2 (.leaf _ k2020_2) (.leaf _ k2020_3))) (.split 3 (.split 3 (.leaf _ k2020_4) (.leaf _ k2020_5)) (.split 3 (.leaf _ k2020_6) (.leaf _ k2020_7)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2020_8) (.leaf _ k2020_9)) (.split 1 (.leaf _ k2020_10) (.leaf _ k2020_11))) (.split 3 (.split 3 (.leaf _ k2020_12) (.leaf _ k2020_13)) (.split 3 (.leaf _ k2020_14) (.split 1 (.leaf _ k2020_15) (.leaf _ k2020_16))))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2021)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2021_0) (.leaf _ k2021_1)) (.split 1 (.leaf _ k2021_2) (.leaf _ k2021_3))) (.split 3 (.split 1 (.leaf _ k2021_4) (.leaf _ k2021_5)) (.split 1 (.leaf _ k2021_6) (.leaf _ k2021_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2021_8) (.leaf _ k2021_9)) (.split 1 (.leaf _ k2021_10) (.leaf _ k2021_11))) (.split 3 (.split 1 (.leaf _ k2021_12) (.leaf _ k2021_13)) (.split 1 (.leaf _ k2021_14) (.leaf _ k2021_15))))))

end C4.Cert.Dir023
