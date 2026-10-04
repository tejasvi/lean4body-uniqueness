module

public import C4Check

public section

/-! Cells `4940 ≤ n < 4977` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir152

theorem k4940_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4940) 2).1
      1019881835874454435518075097184317866276024581983850789640427173855256344673525960339157233).isSome = true := by
  decide +kernel

theorem k4940_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4940) 2).2
      3984136596278695022017766005870826458899237566851648172243027449024258594157684891270204).isSome = true := by
  decide +kernel

theorem k4941_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4941) 2).1
      3889188127425324236270494539086483226257735611978727577485720403514600377355618073660).isSome = true := by
  decide +kernel

theorem k4941_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4941) 2).2
      62229293806186899764564550931884995636714775558498274054643048415531966207984068770876).isSome = true := by
  decide +kernel

theorem k4942_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4942) 2).1
      15552537192773642603600335200751766805055101299520543156284132150413667665453954614076).isSome = true := by
  decide +kernel

theorem k4942_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4942) 2).2
      972188885663546531189094028763545086475517443739263761125307612687205110087319125052).isSome = true := by
  decide +kernel

theorem k4943_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4943) 1).1
      842932277433484894753312532471837255803406324212145025131700798268).isSome = true := by
  decide +kernel

theorem k4943_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4943) 1).2
      842945549972797916745362539292157137400344037177524795998282838588).isSome = true := by
  decide +kernel

theorem k4944_0 : (checkBoxH dirMode depth (dirCellBox 4944)
      1637306197594829803410005000844857099668039501322735559705038403002817076247010290334763829719155276533885481929701488270239814315742488385933864153916).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 4945 4946 [
    21666729061581261204439451524831275478073334418453368545137714356814783377376711555383510528288533969437858077288212795703993148] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4946 4947 [
    994789572156739024924932176129057513296874033327706021079838614389418461343325929746684] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4947 4949 [
    248680524910783336405105829620880465037925446714712935170331534228956979552496933704945,
    51422976147866526983059250019357642719881251163991993579606097] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4949 4960 [
    147566374789824420564, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2854860107853909114036273701359833536276771] = true := by
  decide +kernel

theorem k4960_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4960) 3).1
      13416364304435119175857054426149703502902465971029788843254519602).isSome = true := by
  decide +kernel

theorem k4960_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4960) 3).2
      15789664150409406399914390095816245900575360037255382982456895208213242914600282970930).isSome = true := by
  decide +kernel

theorem k4961_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4961) 3).1
      1008919833652512427345465449554776585701339781437284488000523840121713430513834165629746).isSome = true := by
  decide +kernel

theorem k4961_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4961) 3).2
      4749761992264524654509054905651032308991352556994594629899305141619833472145881045095727243226668215624332082).isSome = true := by
  decide +kernel

theorem k4962_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4962) 2).1
      22376914884242932509417462457753420566237594458812643657433096481507599199651368337540592184986030084642671448487130161428198388531).isSome = true := by
  decide +kernel

theorem k4962_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4962) 2).2
      1398611699306889585529499401005086530596010114319631450566704764683812083372557757775854231493520356526150205614169449595588686643).isSome = true := by
  decide +kernel

theorem k4963_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4963) 2).1 3).1
      53050930159298040332332354044371941587005391405881824024299678924).isSome = true := by
  decide +kernel

theorem k4963_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4963) 2).1 3).2
      52992146327540446375563912289335976557442851759911431811022826700).isSome = true := by
  decide +kernel

theorem k4963_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4963) 2).2
      1395302372431692169922987782358891937332948288550467750865204627020042620009615604266915908119765034779498464232282602941703893811).isSome = true := by
  decide +kernel

theorem k4964_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4964) 2).1
      5571053369261000064234775369266071113481326630486509935669215937545556207789417124069803686635001625287337569936349676221755142963).isSome = true := by
  decide +kernel

theorem k4964_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4964) 2).2
      1392894388914370005061668114206974172568622078519605247035809276613101748867908608270125820259738387822560214326122663728302109491).isSome = true := by
  decide +kernel

theorem k4965_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4965) 2).1
      18851908279423154018866581995527426558543141024622460580538558378295006428012780925296389779660749515417039667).isSome = true := by
  decide +kernel

theorem k4965_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4965) 2).2
      1391489455830854710961508875114140604787147822461085557991421887334743085846423819050920889059129649127866909256926508864591737649).isSome = true := by
  decide +kernel

theorem k4966_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4966) 2).1
      255259519657568503643913579856503615188258105846714221269840051741206607646887527675513651).isSome = true := by
  decide +kernel

theorem k4966_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4966) 2).2
      63819516311166752131444841831906121041228960394860296765786067837964477042971494825177907).isSome = true := by
  decide +kernel

theorem k4967_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4967) 2).1
      15945331562422579760203843024400127067055437561950843107521529533845490876582163080661809).isSome = true := by
  decide +kernel

theorem k4967_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4967) 2).2
      63785690347927620515780066042878354857200797614358595290147694821120242773089205882374961).isSome = true := by
  decide +kernel

theorem k4968_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4968) 2).1
      996094037664631168615351161386877622254606769987985513561623261164078791871143530085436).isSome = true := by
  decide +kernel

theorem k4968_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4968) 2).2
      864004534968157028497073079095298834209919393488487537687242585291836).isSome = true := by
  decide +kernel

theorem k4969_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4969) 2).1
      62231526856632798802386556994248154405934206893872799726184907310353799236615063092284).isSome = true := by
  decide +kernel

theorem k4969_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4969) 2).2
      62233660123245179782319329492475006377595043420273646002999696840266367363351590616124).isSome = true := by
  decide +kernel

theorem k4970_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4970) 3).1
      3372843375325592189250017683408629435726936005560314411186746244156).isSome = true := by
  decide +kernel

theorem k4970_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4970) 3).2
      52694071997123011997287944647397785947873334911313357935881305148).isSome = true := by
  decide +kernel

theorem c20 : allCells dirCell 4971 4972 [
    1387119890724871979565034158990483122688996368176358700605280415705215087066117190027503208886734207575079785248917638102385673020] = true := by
  decide +kernel

theorem c21 : allCells dirCell 4972 4973 [
    86679705887897982601787421475971510621876284843396757454195355657831852582077894790219609774134487840135217203680969897284715324] = true := by
  decide +kernel

theorem c22 : allCells dirCell 4973 4974 [
    1174574404146174320137255347840098747336802875494981863000726114197114397363293044086376506390863233840784188] = true := by
  decide +kernel

theorem c23 : allCells dirCell 4974 4975 [
    994797957819933080805538433418925033258354961517191175975541779345806280900569805762812] = true := by
  decide +kernel

theorem c24 : allCells dirCell 4975 4977 [
    15542588184492883007590028303962810350912224098987212073657348809276149884221030615409,
    51422987833152283455998057289822808592906191845876337509389969] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4940 4977 :=
  (Cover.one (box := dirCellBox) (n := 4940)
      (.split 2 (.leaf _ k4940_0) (.leaf _ k4940_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4941)
      (.split 2 (.leaf _ k4941_0) (.leaf _ k4941_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4942)
      (.split 2 (.leaf _ k4942_0) (.leaf _ k4942_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4943)
      (.split 1 (.leaf _ k4943_0) (.leaf _ k4943_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4944)
      (.leaf _ k4944_0)).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4960)
      (.split 3 (.leaf _ k4960_0) (.leaf _ k4960_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4961)
      (.split 3 (.leaf _ k4961_0) (.leaf _ k4961_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4962)
      (.split 2 (.leaf _ k4962_0) (.leaf _ k4962_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4963)
      (.split 2 (.split 3 (.leaf _ k4963_0) (.leaf _ k4963_1)) (.leaf _ k4963_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4964)
      (.split 2 (.leaf _ k4964_0) (.leaf _ k4964_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4965)
      (.split 2 (.leaf _ k4965_0) (.leaf _ k4965_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4966)
      (.split 2 (.leaf _ k4966_0) (.leaf _ k4966_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4967)
      (.split 2 (.leaf _ k4967_0) (.leaf _ k4967_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4968)
      (.split 2 (.leaf _ k4968_0) (.leaf _ k4968_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4969)
      (.split 2 (.leaf _ k4969_0) (.leaf _ k4969_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4970)
      (.split 3 (.leaf _ k4970_0) (.leaf _ k4970_1))).trans <|
  (Cover.dir c20).trans <|
  (Cover.dir c21).trans <|
  (Cover.dir c22).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24)

end C4.Cert.Dir152
