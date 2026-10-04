module

public import C4Check

public section

/-! Cells `1183 ≤ n < 1239` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir005

theorem k1183_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1183) 2).1 2).1
      7143906639367177940387802223204623262188725703).isSome = true := by
  decide +kernel

theorem k1183_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1183) 2).1 2).2
      25041213279595860401594511376805515572956117147449402076920944565728944774160320240395779554788915582459144819481452028712567743880451574951477527).isSome = true := by
  decide +kernel

theorem k1183_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1183) 2).2 3).1 2).1
      15592018213300543434233560056305035548813183265229193205340888507019470239306880139085).isSome = true := by
  decide +kernel

theorem k1183_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1183) 2).2 3).1 2).2
      62370881882565475245032551298020899014990256469706644179551104138765402518191245389197).isSome = true := by
  decide +kernel

theorem k1183_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1183) 2).2 3).2 2).1
      60883816178606436476688651075400264954054075951827019627204019801447476528695924145).isSome = true := by
  decide +kernel

theorem k1183_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1183) 2).2 3).2 2).2
      3896291575824316741674018896647095467482603197505428967514174764511166782270805989169).isSome = true := by
  decide +kernel

theorem k1184_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1184) 2).1
      79185824104025609103361798).isSome = true := by
  decide +kernel

theorem k1184_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1184) 2).2 2).1
      71789805266306894168300716438479540779589128029386489357614049479180948640137210851076525644012811965895).isSome = true := by
  decide +kernel

theorem k1184_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1184) 2).2 2).2
      339036445334557372133406850970522824461662231999497044727369187748322114535747770504682495741227682956398952103772572179010759).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 1185 1210 [
    662728481161660814772230721687415758326335187951597723939059819543027206, 1314, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209102] = true := by
  decide +kernel

theorem k1210_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1210) 2).1 3).1
      18451580595172945777957229942134606520595058191099453847630561814699651636776125344429644474702287652089969).isSome = true := by
  decide +kernel

theorem k1210_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1210) 2).1 3).2 1).1
      243852716078282627725712739193511712424945437732867119318653498519733065878123802190).isSome = true := by
  decide +kernel

theorem k1210_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1210) 2).1 3).2 1).2
      5438840163203223126322692224064867233952833667949123286140167550134117570776279780969888710603169255803284736347897527393899979).isSome = true := by
  decide +kernel

theorem k1210_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1210) 2).2 3).1
      18462636447029822038442811525998086299205688544558853738318479509513456805880190163330581780570381243740273).isSome = true := by
  decide +kernel

theorem k1210_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1210) 2).2 3).2 1).1
      3306236593348457144678921076459715401961229202700097860747902215).isSome = true := by
  decide +kernel

theorem k1210_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1210) 2).2 3).2 1).2 3).1
      61062150385683629029582476253919001661838277587967611800922585239010530924954387826).isSome = true := by
  decide +kernel

theorem k1210_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1210) 2).2 3).2 1).2 3).2
      244033877551753842220700884497615722193148667328297258133627082496023124846568850913).isSome = true := by
  decide +kernel

theorem k1211_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).1 3).1 2).1
      18428703242715023941185981944429780333135776862237576490865265660769267527394276846838383174056908003923405).isSome = true := by
  decide +kernel

theorem k1211_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).1 3).1 2).2
      21787895992585405307005688538290160508533647777089685256309218534756568603853054285223003086636978821411655428942040173594084813).isSome = true := by
  decide +kernel

theorem k1211_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).1 3).2 2).1
      15588150562186472440721612184795672347718103575143961390091701890211393812881454588301).isSome = true := by
  decide +kernel

theorem k1211_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).1 3).2 2).2
      249360174102771873628606338833431126168979642960028283913450226032664995880593027533197).isSome = true := by
  decide +kernel

theorem k1211_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).2 3).1 1).1
      5434777542766491914875023196995587570403179853389089062308838889159929164009052463477557327449037957361422413970736343380870603).isSome = true := by
  decide +kernel

theorem k1211_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).2 3).1 1).2
      1206756026416732916700071300719244003716604798250831973057128572334582406887788052683697956054343217748956059527).isSome = true := by
  decide +kernel

theorem k1211_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).2 3).2 1).1
      15958001432653155932103985196328848679373745681542715466694075220860608621022134926341767).isSome = true := by
  decide +kernel

theorem k1211_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1211) 2).2 3).2 1).2
      62348068843907749743204861958219132440432341661266395857114007126438348297112072707299).isSome = true := by
  decide +kernel

theorem k1212_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).1 3).1 2).1
      3894292666041059131220161893818111797907375766085733027286348852715711118316744038193).isSome = true := by
  decide +kernel

theorem k1212_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).1 3).1 2).2
      15579994956270498821721925416976005658673578541566681081808903682357936695562179730657).isSome = true := by
  decide +kernel

theorem k1212_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1212) 2).1 3).2
      18820394983233067585685665377306287862368477288967780319467341461777785740600085208442554787532797377385780425).isSome = true := by
  decide +kernel

theorem k1212_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).2 3).1 1).1
      996984155531808739196699235317581526747535576740478437214790129751577446882964333753138).isSome = true := by
  decide +kernel

theorem k1212_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).2 3).1 1).2
      249276350357143016480075749022488878725188423493519819910348673845277538556118822908723).isSome = true := by
  decide +kernel

theorem k1212_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).2 3).2 1).1
      249111310618564332290674219211975724961473295249711543339214317212713217677136624573666).isSome = true := by
  decide +kernel

theorem k1212_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1212) 2).2 3).2 1).2
      52742779020517166456138706993143789595815618145500424808361842595).isSome = true := by
  decide +kernel

theorem k1213_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1213) 2).1 3).1
      18371740962602569015548724165710202458892326342456372583419835334301419275639026514529878022692965610137033).isSome = true := by
  decide +kernel

theorem k1213_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1213) 2).1 3).2
      62221889740996944465048716869631555688429950574769485823775254478150090535446418857801).isSome = true := by
  decide +kernel

theorem k1213_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1213) 2).2 3).1
      16318504995356310053411813032469462303116838229008493578183396334161146300231908330193589129).isSome = true := by
  decide +kernel

theorem k1213_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1213) 2).2 3).2
      1019517491067171169860230972736737733494125346316909922985919885558065555069548625950872453).isSome = true := by
  decide +kernel

theorem k1214_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1214) 2).1
      102333252001959169423758340880458323884004223949442859258251554969806530020281530926697732573263794091506243345567869758648749217663247285666898981150).isSome = true := by
  decide +kernel

theorem k1214_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1214) 2).2 3).1
      15553714559390454046328722702340783189150571429691113476622634152403563637418243153121).isSome = true := by
  decide +kernel

theorem k1214_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1214) 2).2 3).2
      3887220400054323225818554403588313156438594855836798504124724739864642929244229064497).isSome = true := by
  decide +kernel

theorem k1215_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1215) 2).1
      13164419732521072462000822007267447402222547364066860119885705478).isSome = true := by
  decide +kernel

theorem k1215_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1215) 2).2
      1353954539954436551052905405209418018422949714854935291030529837794204808521125896372315541797888071572209033595152934015275911).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1216 1238 [
    604277933596384054952198, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem k1238_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1238) 3).1 2).1
      18474508049411685572174098520930076458795179387193091171208398999219623698830210422436602810981482421645425).isSome = true := by
  decide +kernel

theorem k1238_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1238) 3).1 2).2
      15689459832934074613825233796699934569468151748998066238974041309524276253721711988849).isSome = true := by
  decide +kernel

theorem k1238_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).1 1).1
      3307822088720667250831765685022388570452704554046528736131554567).isSome = true := by
  decide +kernel

theorem k1238_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).1 1).2 3).1
      244283164350895074844531704121261906640857259104233421084216121439934937304728485233).isSome = true := by
  decide +kernel

theorem k1238_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).1 1).2 3).2
      244157886017388779068091440527119138553099499377290593839759274199105576413551642081).isSome = true := by
  decide +kernel

theorem k1238_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).2 1).1
      3309393796228935055563197932829923093223203886524398267480977671).isSome = true := by
  decide +kernel

theorem k1238_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).2 1).2 3).1
      61115422464488902688475256035033744000356015325857630011190069431782663620526190961).isSome = true := by
  decide +kernel

theorem k1238_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1238) 3).2 2).2 1).2 3).2
      244283295974269558124857996002598199519313069356804572186814556286569371075902469601).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1183 1239 :=
  (Cover.one (box := dirCellBox) (n := 1183)
      (.split 2 (.split 2 (.leaf _ k1183_0) (.leaf _ k1183_1)) (.split 3 (.split 2 (.leaf _ k1183_2) (.leaf _ k1183_3)) (.split 2 (.leaf _ k1183_4) (.leaf _ k1183_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1184)
      (.split 2 (.leaf _ k1184_0) (.split 2 (.leaf _ k1184_1) (.leaf _ k1184_2)))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 1210)
      (.split 2 (.split 3 (.leaf _ k1210_0) (.split 1 (.leaf _ k1210_1) (.leaf _ k1210_2))) (.split 3 (.leaf _ k1210_3) (.split 1 (.leaf _ k1210_4) (.split 3 (.leaf _ k1210_5) (.leaf _ k1210_6)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1211)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1211_0) (.leaf _ k1211_1)) (.split 2 (.leaf _ k1211_2) (.leaf _ k1211_3))) (.split 3 (.split 1 (.leaf _ k1211_4) (.leaf _ k1211_5)) (.split 1 (.leaf _ k1211_6) (.leaf _ k1211_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1212)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1212_0) (.leaf _ k1212_1)) (.leaf _ k1212_2)) (.split 3 (.split 1 (.leaf _ k1212_3) (.leaf _ k1212_4)) (.split 1 (.leaf _ k1212_5) (.leaf _ k1212_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1213)
      (.split 2 (.split 3 (.leaf _ k1213_0) (.leaf _ k1213_1)) (.split 3 (.leaf _ k1213_2) (.leaf _ k1213_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1214)
      (.split 2 (.leaf _ k1214_0) (.split 3 (.leaf _ k1214_1) (.leaf _ k1214_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1215)
      (.split 2 (.leaf _ k1215_0) (.leaf _ k1215_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 1238)
      (.split 3 (.split 2 (.leaf _ k1238_0) (.leaf _ k1238_1)) (.split 2 (.split 1 (.leaf _ k1238_2) (.split 3 (.leaf _ k1238_3) (.leaf _ k1238_4))) (.split 1 (.leaf _ k1238_5) (.split 3 (.leaf _ k1238_6) (.leaf _ k1238_7))))))

end C4.Cert.Dir005
