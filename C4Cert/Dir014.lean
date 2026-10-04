module

public import C4Check

public section

/-! Cells `1658 ≤ n < 1685` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir014

theorem k1658_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).1 3).1 1).1
      245032161296965103204789580224805149942849155221345992595884981066934230601172172145).isSome = true := by
  decide +kernel

theorem k1658_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).1 3).1 1).2
      3921547053580849250267712892245634235539858614821691038733995779244325274136625977138).isSome = true := by
  decide +kernel

theorem k1658_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).1 3).2 1).1
      244813933803785290866552627697739778812629256561323475779856824340623185755833327404).isSome = true := by
  decide +kernel

theorem k1658_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).1 3).2 1).2
      245081697808498490745325540638338121806540299353464088642369554269316284266847887052).isSome = true := by
  decide +kernel

theorem k1658_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).2 3).1
      100880318783520886259613603737424647524468871775731307042950207464251641278380279581187112805081002455199209185702131140669209790463191312107855281).isSome = true := by
  decide +kernel

theorem k1658_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1658) 3).1 2).2 3).2
      349661823904466642487357385535848675316729465632322701325756267594564953389084514758713500794316042265175361245185260845604475593).isSome = true := by
  decide +kernel

theorem k1658_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).2 2).1 3).1 1).1
      61244293575573251733497933102213804715748085440343581588106819727012268713913472972).isSome = true := by
  decide +kernel

theorem k1658_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1658) 3).2 2).1 3).1 1).2
      244623760336584885996194553556041799087846805198823865057897620147353728085153767116).isSome = true := by
  decide +kernel

theorem k1658_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1658) 3).2 2).1 3).2
      21823798656933790734111242190597288740121325444998737287499268417306276656385638096251318140033775751071003879144710904537894705).isSome = true := by
  decide +kernel

theorem k1658_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1658) 3).2 2).2 3).1
      1610700550919903539451689372824456011898233861809458857866555884073792103577384605754550942840556994349202410842472000983774067012164659315910074161).isSome = true := by
  decide +kernel

theorem k1658_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1658) 3).2 2).2 3).2
      5453058210111566714808298239300651704536868550575463187330083500822629322919142547042706774622492691112437240171698650576444209).isSome = true := by
  decide +kernel

theorem k1659_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).1 2).1 1).1
      5443286401612821348476207180773670983394837925837996187010803361998227087383774849576667551637817333269267469149349770496957235).isSome = true := by
  decide +kernel

theorem k1659_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).1 2).1 1).2
      295312836285418149161280983587053619271264885764695868005225683251166218652876374361602121444336915916905267).isSome = true := by
  decide +kernel

theorem k1659_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).1 2).2 1).1
      87159644948097777851911380943581984989939870422007938276665509993147913345184166522101958196338502709969088425997613987570077490).isSome = true := by
  decide +kernel

theorem k1659_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).1 2).2 1).2
      5448194199511195823378486345333986332718477618792314107705640311828313055494513241942706283530751326066368984830713061143075634).isSome = true := by
  decide +kernel

theorem k1659_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).2 2).1 1).1
      3994136477050180002140705424383660408008051073009100010494971931128907875182879047011123).isSome = true := by
  decide +kernel

theorem k1659_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).2 2).1 1).2
      999616612261752842558854572775601569507999167977374048991237001394656681775647212008243).isSome = true := by
  decide +kernel

theorem k1659_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).2 2).2 1).1
      4091102320607853255995856830583456750570844946968060826244433947157534324616899358076783815).isSome = true := by
  decide +kernel

theorem k1659_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1659) 3).2 2).2 1).2
      3995694755115831110568057725409288527505984878788719724577825383881868555028990829906739).isSome = true := by
  decide +kernel

theorem k1660_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).1 2).1 1).1
      998761209318343704589142440908490098070644732766233218691150916070217448794255708746547).isSome = true := by
  decide +kernel

theorem k1660_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).1 2).1 1).2
      15985152710112012044004146672808710459986325328971884211797502995959128828163789533066034).isSome = true := by
  decide +kernel

theorem k1660_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).1 2).2 1).1
      998225970576604126851633458754230415335386005903962876476676335310536811427665034179378).isSome = true := by
  decide +kernel

theorem k1660_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).1 2).2 1).2
      998122377415370660912951980572942555029929834246710653238153416039742051288494655238963).isSome = true := by
  decide +kernel

theorem k1660_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).2 2).1 1).1
      998169270894953412391754592969285492871209260970685446676960074324825313762399518815027).isSome = true := by
  decide +kernel

theorem k1660_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).2 2).1 1).2
      15584554942918551203540645778188008279494511133580688644334280627064209236406759255244).isSome = true := by
  decide +kernel

theorem k1660_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).2 2).2 1).1
      15586437461769409812473233065017499899718806062321357571111487943506960973053084232908).isSome = true := by
  decide +kernel

theorem k1660_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1660) 3).2 2).2 1).2
      15586951513513193476892946330800582559752854532784424729505326473526470490453829958860).isSome = true := by
  decide +kernel

theorem k1661_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1661) 3).1 2).1 1).1
      52814136892567384202312677010026973880879007200965755799296883916).isSome = true := by
  decide +kernel

theorem k1661_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1661) 3).1 2).1 1).2
      973500927632497046128105657167629743987778279521451164419800381334118439205524569292).isSome = true := by
  decide +kernel

theorem k1661_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1661) 3).1 2).2
      22232103529826061187483552656977465971001854728010476151563388766299220104310094477792360449238033046812276117724553007957680649009).isSome = true := by
  decide +kernel

theorem k1661_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1661) 3).2 2).1 1).1
      13184415342083068331789763944851529632458536347899454173010685132).isSome = true := by
  decide +kernel

theorem k1661_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1661) 3).2 2).1 1).2
      973002325086765846628300835691710285816466701494006108525822324300898258318348090572).isSome = true := by
  decide +kernel

theorem k1661_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1661) 3).2 2).2
      1388809691154921289647375665629553977061282268945106284001404760171454419075364368465326758508905093248815337870894172118980604721).isSome = true := by
  decide +kernel

theorem k1662_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1662) 3).1 2).1
      3983523511426388121480153984647089964290076286514534547690837687339905327404338561528625).isSome = true := by
  decide +kernel

theorem k1662_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1662) 3).1 2).2
      4703423184922282966994793735582612291507228923013545832883325002451138810106847037031151347364744373787800369).isSome = true := by
  decide +kernel

theorem k1662_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1662) 3).2 2).1
      995549688859598840878521035078512547824379061208649310200680843442603158550340129354545).isSome = true := by
  decide +kernel

theorem k1662_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1662) 3).2 2).2
      995678856325587166796063270749979228044000509623881248644113759232087631427291867345713).isSome = true := by
  decide +kernel

theorem k1663_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1663) 2).1 3).1
      13500514354897922113220738407555618469624555283455583636609083732785).isSome = true := by
  decide +kernel

theorem k1663_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1663) 2).1 3).2
      210696993284711954256749116895447459404832720012999383144734709553).isSome = true := by
  decide +kernel

theorem k1663_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1663) 2).2 3).1
      995377436085217732360414720883381384786264769080588081565172195457149440227430777058097).isSome = true := by
  decide +kernel

theorem k1663_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1663) 2).2 3).2
      210702170716829668583783887410116839647418400409584292583291393841).isSome = true := by
  decide +kernel

theorem k1664_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1664) 2).1
      24977315492150579660333352434516958100315970494349073551768622460082463042774623308932098561495257698230673142258251602369785798897173606167961395).isSome = true := by
  decide +kernel

theorem k1664_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1664) 2).2
      1354023898838821012726260323289446856119350754933309989343418346331201204813492245459363079029420112497264997921892442166654407).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 1665 1685 [
    44589484716193897214690169557524602568723718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 219964907354813076659971434909541023073948910024579377270283467506659] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1658 1685 :=
  (Cover.one (box := dirCellBox) (n := 1658)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k1658_0) (.leaf _ k1658_1)) (.split 1 (.leaf _ k1658_2) (.leaf _ k1658_3))) (.split 3 (.leaf _ k1658_4) (.leaf _ k1658_5))) (.split 2 (.split 3 (.split 1 (.leaf _ k1658_6) (.leaf _ k1658_7)) (.leaf _ k1658_8)) (.split 3 (.leaf _ k1658_9) (.leaf _ k1658_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1659)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1659_0) (.leaf _ k1659_1)) (.split 1 (.leaf _ k1659_2) (.leaf _ k1659_3))) (.split 2 (.split 1 (.leaf _ k1659_4) (.leaf _ k1659_5)) (.split 1 (.leaf _ k1659_6) (.leaf _ k1659_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1660)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1660_0) (.leaf _ k1660_1)) (.split 1 (.leaf _ k1660_2) (.leaf _ k1660_3))) (.split 2 (.split 1 (.leaf _ k1660_4) (.leaf _ k1660_5)) (.split 1 (.leaf _ k1660_6) (.leaf _ k1660_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1661)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1661_0) (.leaf _ k1661_1)) (.leaf _ k1661_2)) (.split 2 (.split 1 (.leaf _ k1661_3) (.leaf _ k1661_4)) (.leaf _ k1661_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1662)
      (.split 3 (.split 2 (.leaf _ k1662_0) (.leaf _ k1662_1)) (.split 2 (.leaf _ k1662_2) (.leaf _ k1662_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1663)
      (.split 2 (.split 3 (.leaf _ k1663_0) (.leaf _ k1663_1)) (.split 3 (.leaf _ k1663_2) (.leaf _ k1663_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1664)
      (.split 2 (.leaf _ k1664_0) (.leaf _ k1664_1))).trans <|
  (Cover.dir c7)

end C4.Cert.Dir014
