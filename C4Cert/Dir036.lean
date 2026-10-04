module

public import C4Check

public section

/-! Cells `2356 ≤ n < 2382` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir036

theorem k2356_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).1 3).1 1).1
      3932453953669495981204140918757891546903203980943298437075096119275292544803475953457).isSome = true := by
  decide +kernel

theorem k2356_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).1 3).1 1).2
      245730168558990680034262083974068926570989163296714687152085413830654452751366840108).isSome = true := by
  decide +kernel

theorem k2356_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).1 3).2
      1368396974617263396934836191134345467956395170262894985593811459146599784092004372887829749193277984425257545866812331598550917).isSome = true := by
  decide +kernel

theorem k2356_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).2 3).1 1).1
      3934442333632433120924924452168330773407281552950651317118231958813495265704400508723).isSome = true := by
  decide +kernel

theorem k2356_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).2 3).1 1).2
      3933631170245021710163153123093280461978188956731083789319762177717567748051944871729).isSome = true := by
  decide +kernel

theorem k2356_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).2 3).2
      1616124279979350354416147992007420231691889312906759499043449898629833200386942297984426749246261310847170952963713551466190358132229306577147350833).isSome = true := by
  decide +kernel

theorem k2356_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).1 1).1
      250811225214247524833393205539253180148290796006189713811903223160930000984501553235143).isSome = true := by
  decide +kernel

theorem k2356_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).1 1).2
      18073566349012663040223237843409931131680093988035228520975334232856345102586076115305698552776225414579).isSome = true := by
  decide +kernel

theorem k2356_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).2 1).1
      341483604329864945490485576140909418370503112515082975432730381993736034737193245240162856611969351323587940638864167893688115).isSome = true := by
  decide +kernel

theorem k2356_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).2 1).2
      1002922334204609659713655664103941071840673831828028534884997654730726254312586849311923).isSome = true := by
  decide +kernel

theorem k2356_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).1 1).1
      15750830486844979213671462888791490785478869653139385318555626977876961465799090068275).isSome = true := by
  decide +kernel

theorem k2356_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).1 1).2
      1163422918636082805751192512617732079821407443588528105211250832377573861130332436465964384783281348768716).isSome = true := by
  decide +kernel

theorem k2356_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).2 1).1
      63059244721201847543102754139854684838985465851350483925542825218511163169700231469875).isSome = true := by
  decide +kernel

theorem k2356_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).2 1).2
      297849968383402405819039511890698028055401306007324930868775563534215570337534006677218687951575602414284492).isSome = true := by
  decide +kernel

theorem k2356_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).1 1).1
      3931431261679609406190490210553176371939833408755980193762167285888119179788839737139).isSome = true := by
  decide +kernel

theorem k2356_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).1 1).2
      53268818829908388610170853470352853957447443369737186180572457932).isSome = true := by
  decide +kernel

theorem k2356_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).2 1).1
      62939629553473321298833223957379376601024061903782364428634381367802190521176097381171).isSome = true := by
  decide +kernel

theorem k2356_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).2 1).2
      291199848117943317860398349310091198299574911799725049033155500014982407683762220995594753702469828566732).isSome = true := by
  decide +kernel

theorem k2356_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).1 3).1
      1615031369086300782436756999502476659856151799153352364424629052635669175800201775940690459684335583579142150511042608573930076060347820109997756209).isSome = true := by
  decide +kernel

theorem k2356_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).1 3).2
      4628667155302881289041051874649773185442571987713446447092199984375733000104219507482676171918521527556913).isSome = true := by
  decide +kernel

theorem k2356_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).2 3).1
      6463073887390089556082271051526421185407288723418270306926708218960976579243705866435973642769374336070249543706619219908687774963933414764991839025).isSome = true := by
  decide +kernel

theorem k2356_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).2 3).2
      403515521079768168686310055553723250749588877768479449273700241488412974945780106019247431559388154393979861467681668085943547243115064602770398001).isSome = true := by
  decide +kernel

theorem k2357_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).1 3).1
      6287567610282088647332538448428109282136415343552678171859162324570488392062814677004787160763057407781724284668031967399827072570515638045816269).isSome = true := by
  decide +kernel

theorem k2357_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).1 3).2
      5738961727247906840948681007168069974635667781).isSome = true := by
  decide +kernel

theorem k2357_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).2 3).1 1).1
      978608323087370070082615417255467686033867089807942840092699072113023746926285184179).isSome = true := by
  decide +kernel

theorem k2357_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).2 3).1 1).2
      61149361786676043367237667675553062878769589505952627670012544512877885458144441779).isSome = true := by
  decide +kernel

theorem k2357_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).2 3).2
      21324132793728416968954903325147759393665401375068468702171417559845937777663660029727661691700762589105819644320586307823053).isSome = true := by
  decide +kernel

theorem k2357_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).1 1).1
      3914263396413239970638438008177541983559821419285081816630684916648143298666466170675).isSome = true := by
  decide +kernel

theorem k2357_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).1 1).2
      62611301026410112449676076814159225253872688602589262689795936815401207426753780604083).isSome = true := by
  decide +kernel

theorem k2357_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).2 3).1
      4626154172972082148734595065593841138450622043322520849455129428140123993978885737555089892404970378353457).isSome = true := by
  decide +kernel

theorem k2357_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).2 3).2
      3914776818546160591542989714715156788752528370501526568509069309446605205047430321969).isSome = true := by
  decide +kernel

theorem k2357_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).2 2).1
      100508015753137376752571956261359253111933389422268112471706893525885814864848907949203783777705911608651050965873159247661382344281433899278361805).isSome = true := by
  decide +kernel

theorem k2357_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).2 2).2 1).1
      3909628675118239415137950938869340641421062723766326414903978163675527270844833306419).isSome = true := by
  decide +kernel

theorem k2357_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).2 2).2 1).2
      52970436455672357579394765850072930019295315510705473268178032435).isSome = true := by
  decide +kernel

theorem k2358_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2358) 2).1
      8387500934392084962415700104484446059817081350914945740048525485015746928104185144756184289374).isSome = true := by
  decide +kernel

theorem k2358_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2358) 2).2 3).1 2).1
      72039683676419572046697994380552963103065465566570148603722582822990456928671772820787761215351931667917).isSome = true := by
  decide +kernel

theorem k2358_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2358) 2).2 3).1 2).2
      295147802064389704765706322470559400437193768571156312250466178305498276469483967219491292278521993668441293).isSome = true := by
  decide +kernel

theorem k2358_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2358) 2).2 3).2 2).1
      15243638339710942849976335136969551272438078733262864864052660870255795592848088433).isSome = true := by
  decide +kernel

theorem k2358_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2358) 2).2 3).2 2).2
      17998098823302496259686472726911325440833407901596050173687399142734564862926810201448661014267577951693).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2359 2381 [
    846763986662749904470777157817689226028327664294725715523841883945904813386001132097193248955223413221635150650886,
    16871522, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2381 2382 [
    623037436950093492872882253169877503507160243301371671550533259309320253937694519492058573885147697303388194320983479821787917632530708562550212904932367577117121147504008500022976571237001999] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2356 2382 :=
  (Cover.one (box := dirCellBox) (n := 2356)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2356_0) (.leaf _ k2356_1)) (.leaf _ k2356_2)) (.split 3 (.split 1 (.leaf _ k2356_3) (.leaf _ k2356_4)) (.leaf _ k2356_5))) (.split 2 (.split 1 (.leaf _ k2356_6) (.leaf _ k2356_7)) (.split 1 (.leaf _ k2356_8) (.leaf _ k2356_9)))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2356_10) (.leaf _ k2356_11)) (.split 1 (.leaf _ k2356_12) (.leaf _ k2356_13))) (.split 2 (.split 1 (.leaf _ k2356_14) (.leaf _ k2356_15)) (.split 1 (.leaf _ k2356_16) (.leaf _ k2356_17)))) (.split 2 (.split 3 (.leaf _ k2356_18) (.leaf _ k2356_19)) (.split 3 (.leaf _ k2356_20) (.leaf _ k2356_21)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2357)
      (.split 2 (.split 2 (.split 3 (.leaf _ k2357_0) (.leaf _ k2357_1)) (.split 3 (.split 1 (.leaf _ k2357_2) (.leaf _ k2357_3)) (.leaf _ k2357_4))) (.split 3 (.split 2 (.split 1 (.leaf _ k2357_5) (.leaf _ k2357_6)) (.split 3 (.leaf _ k2357_7) (.leaf _ k2357_8))) (.split 2 (.leaf _ k2357_9) (.split 1 (.leaf _ k2357_10) (.leaf _ k2357_11)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2358)
      (.split 2 (.leaf _ k2358_0) (.split 3 (.split 2 (.leaf _ k2358_1) (.leaf _ k2358_2)) (.split 2 (.leaf _ k2358_3) (.leaf _ k2358_4))))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4)

end C4.Cert.Dir036
