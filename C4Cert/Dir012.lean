module

public import C4Check

public section

/-! Cells `1603 ≤ n < 1631` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir012

theorem k1603_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).1 3).1 2).1
      62400926108749043253075502166462500737523217097037656188420332956404467797785466103437).isSome = true := by
  decide +kernel

theorem k1603_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).1 3).1 2).2
      4089186103479840928217520751093371955096240613575879531005497105723574455328460023901342925).isSome = true := by
  decide +kernel

theorem k1603_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).1 3).2 2).1
      15588280437489862578444080198264855522960619734409437515098998296284849437328238696241).isSome = true := by
  decide +kernel

theorem k1603_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).1 3).2 2).2
      15590770553626240888373034281158792385861714334166997750027352079588025701429208374065).isSome = true := by
  decide +kernel

theorem k1603_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).2 3).1 1).1
      4089086346300227165682873263064389781607140744053406325741859004765308710632698812401177479).isSome = true := by
  decide +kernel

theorem k1603_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).2 3).1 1).2
      1023442971334699538549514916309823803979255878739906501757957488197833051584215580579548363).isSome = true := by
  decide +kernel

theorem k1603_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).2 3).2 1).1
      997685463288778789742428299820649652793459494177541936786606181748809145026907560571699).isSome = true := by
  decide +kernel

theorem k1603_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1603) 2).2 3).2 1).2
      997681970536142477897876105599366759678533506959366869327725281671225548481849303331635).isSome = true := by
  decide +kernel

theorem k1604_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1604) 2).1 3).1 1).1
      243440109626276276937507633753874027011414090841717327882379593115649332450005738866).isSome = true := by
  decide +kernel

theorem k1604_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1604) 2).1 3).1 1).2
      243444741196822980481510531540130736342837106359246810649431043993567670269644254578).isSome = true := by
  decide +kernel

theorem k1604_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).1 3).2
      294107299554424506952486399096530281070883678040414219767187663894659228646643700497956063781645298390947273).isSome = true := by
  decide +kernel

theorem k1604_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1604) 2).2 3).1 1).1
      211306467594194847086180300489425069338938556282760292012677619251).isSome = true := by
  decide +kernel

theorem k1604_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1604) 2).2 3).1 1).2
      211185594742422146149243166597204186873775917519926317939493849907).isSome = true := by
  decide +kernel

theorem k1604_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).2 3).2
      1206189719838258550853164299370260453655711149271875932067053394946207440139998348114281893480875029301527006413).isSome = true := by
  decide +kernel

theorem k1605_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1605) 2).1 2).1
      60780951445297063257950144118438338161988389448128850868867139924506849599907400007).isSome = true := by
  decide +kernel

theorem k1605_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1605) 2).1 2).2
      71759619064024034155327818044882047521127199741258027416020773495728671723983562741150739498905250854343).isSome = true := by
  decide +kernel

theorem k1605_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1605) 2).2 3).1
      63760838556495689756075260564456298900233804844940710011389732350209548913846770654418121).isSome = true := by
  decide +kernel

theorem k1605_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1605) 2).2 3).2
      248987323228549044540609963429346907837709247028852836365088231606202579853074777351369).isSome = true := by
  decide +kernel

theorem k1606_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1606) 2).1
      210786747011336577832170602613270342042896909458556202687248404502).isSome = true := by
  decide +kernel

theorem k1606_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1606) 2).2 3).1
      15557105523489530358257553118570907629913185935918923989752145607556071194637527062321).isSome = true := by
  decide +kernel

theorem k1606_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1606) 2).2 3).2
      60756018632576347648950273665944093722659381768686428277976501861942844659740803913).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 1607 1628 [
    18353215803407257069053576211399166643767671093381761710550249279993697372822034623715537646964115931252486,
    24291852389873232852300914, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c5 : allCells dirCell 1628 1629 [
    271233480665227085339154617216626483513171837078282291937314301606366316205749993727177362867171] = true := by
  decide +kernel

theorem k1629_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1629) 3).1 2).1 3).1
      984084234125767241841672887975664001229567311101184943472996636041864546828152145121).isSome = true := by
  decide +kernel

theorem k1629_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1629) 3).1 2).1 3).2
      1187471248071562527770381359629079199528060092467852446288486607036027987846078365030676943390777853879993605).isSome = true := by
  decide +kernel

theorem k1629_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1629) 3).1 2).2 3).1
      246285677266065373379037395905938549643091171599482347355270793847925237692692125473).isSome = true := by
  decide +kernel

theorem k1629_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1629) 3).1 2).2 3).2
      4644668669403299379534306641414914749796040811490571041132135267779733860092681706706182693082774792052997).isSome = true := by
  decide +kernel

theorem k1629_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).1 3).1 1).1
      15329817365532859220922027666285407797667529046720606671692002540667559083547160946).isSome = true := by
  decide +kernel

theorem k1629_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).1 3).1 1).2
      1004420367969698515277353734040020975692424719848609595303588748089102817162318877525382).isSome = true := by
  decide +kernel

theorem k1629_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).1 3).2 1).1
      61322300353975722889267786770673802028436305566159632176161883234870682767621268914).isSome = true := by
  decide +kernel

theorem k1629_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).1 3).2 1).2
      3919945853423418936433774696989850990556940982399986104851267580605519859384103327538).isSome = true := by
  decide +kernel

theorem k1629_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).2 3).1
      22443186695302386603270163722416962459891028422111563906212765184393385903664996070086023873380327349235620346112613667444894298165).isSome = true := by
  decide +kernel

theorem k1629_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).2 3).2 1).1
      15327553299452098192748227421629787796317876879547242582240367714581335153405989234).isSome = true := by
  decide +kernel

theorem k1629_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1629) 3).2 2).2 3).2 1).2
      15692187149158474522686641585720688054676321122759829696021650708061865831644055426866).isSome = true := by
  decide +kernel

theorem k1630_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).1 3).1 1).1
      15675595792776192303266042243893328468923067531806410029390578333673952382162501141897).isSome = true := by
  decide +kernel

theorem k1630_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).1 3).1 1).2
      3916341160649877865462495915872951817657108425055081675169217436452062348396886415154).isSome = true := by
  decide +kernel

theorem k1630_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).1 3).2 1).1
      3912513980613769003031969960232088007698312376174919938549351726985750065051146557234).isSome = true := by
  decide +kernel

theorem k1630_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).1 3).2 1).2
      3920829812040935856412937894050442140860626056222948516651866137390888302828179707698).isSome = true := by
  decide +kernel

theorem k1630_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).2 3).1 1).1
      979491184405988197015519437851796389773005900692397757919981820560270178602925293385).isSome = true := by
  decide +kernel

theorem k1630_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).2 3).1 1).2
      3919077105186020366204535765430940552046384000268348146145258166523938384893722515250).isSome = true := by
  decide +kernel

theorem k1630_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).2 3).2 1).1
      3918406625565309046807166736659203281647457610469501227743931570520060543849622591281).isSome = true := by
  decide +kernel

theorem k1630_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).1 2).2 3).2 1).2
      3915649963298144687856871976440009617000802940065304382945241027616944900658390423346).isSome = true := by
  decide +kernel

theorem k1630_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).1 1).1 3).1
      977462596106801810856755365729820609102558727963391361226404603528776718201416394210).isSome = true := by
  decide +kernel

theorem k1630_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).1 1).1 3).2
      244220691352644623434135837507445356817300326902673670263483218297010830396677809634).isSome = true := by
  decide +kernel

theorem k1630_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).1 1).2 3).1
      15632864408462265349155894855328393973766029827844618673633408041491951463902675785633).isSome = true := by
  decide +kernel

theorem k1630_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).1 1).2 3).2
      734529886248371344824899479015259303715700755250).isSome = true := by
  decide +kernel

theorem k1630_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).2 3).1 1).1
      3911976904342219024835066976703919207734661330375074082252914400489343466793785595698).isSome = true := by
  decide +kernel

theorem k1630_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).2 3).1 1).2
      62589962310744864433601334000897416238532941091807610632407390563690137862163925850930).isSome = true := by
  decide +kernel

theorem k1630_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).2 3).2 1).1
      244355695091224910433982537762637078424692377157808749786968869642315777354864109026).isSome = true := by
  decide +kernel

theorem k1630_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1630) 3).2 2).2 3).2 1).2
      3908547645629406367678217850742149839292144558409065869884963661642536086148170111692).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1603 1631 :=
  (Cover.one (box := dirCellBox) (n := 1603)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1603_0) (.leaf _ k1603_1)) (.split 2 (.leaf _ k1603_2) (.leaf _ k1603_3))) (.split 3 (.split 1 (.leaf _ k1603_4) (.leaf _ k1603_5)) (.split 1 (.leaf _ k1603_6) (.leaf _ k1603_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1604)
      (.split 2 (.split 3 (.split 1 (.leaf _ k1604_0) (.leaf _ k1604_1)) (.leaf _ k1604_2)) (.split 3 (.split 1 (.leaf _ k1604_3) (.leaf _ k1604_4)) (.leaf _ k1604_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1605)
      (.split 2 (.split 2 (.leaf _ k1605_0) (.leaf _ k1605_1)) (.split 3 (.leaf _ k1605_2) (.leaf _ k1605_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1606)
      (.split 2 (.leaf _ k1606_0) (.split 3 (.leaf _ k1606_1) (.leaf _ k1606_2)))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 1629)
      (.split 3 (.split 2 (.split 3 (.leaf _ k1629_0) (.leaf _ k1629_1)) (.split 3 (.leaf _ k1629_2) (.leaf _ k1629_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k1629_4) (.leaf _ k1629_5)) (.split 1 (.leaf _ k1629_6) (.leaf _ k1629_7))) (.split 3 (.leaf _ k1629_8) (.split 1 (.leaf _ k1629_9) (.leaf _ k1629_10)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1630)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k1630_0) (.leaf _ k1630_1)) (.split 1 (.leaf _ k1630_2) (.leaf _ k1630_3))) (.split 3 (.split 1 (.leaf _ k1630_4) (.leaf _ k1630_5)) (.split 1 (.leaf _ k1630_6) (.leaf _ k1630_7)))) (.split 2 (.split 1 (.split 3 (.leaf _ k1630_8) (.leaf _ k1630_9)) (.split 3 (.leaf _ k1630_10) (.leaf _ k1630_11))) (.split 3 (.split 1 (.leaf _ k1630_12) (.leaf _ k1630_13)) (.split 1 (.leaf _ k1630_14) (.leaf _ k1630_15))))))

end C4.Cert.Dir012
