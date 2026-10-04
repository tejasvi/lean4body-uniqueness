module

public import C4Check

public section

/-! Cells `2164 ≤ n < 2197` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir031

theorem k2164_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2164) 3).1 2).1
      1023896304225960111674358360171727521513500943190405293094519995619234179427878663198716145).isSome = true := by
  decide +kernel

theorem k2164_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2164) 3).1 2).2
      3999755526263241043950095405836680062785138824066110303106718996747586006194953513647164).isSome = true := by
  decide +kernel

theorem k2164_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2164) 3).2 2).1
      255751265902204061890459533502440680353466078149909143117302881496992128401689145720298289).isSome = true := by
  decide +kernel

theorem k2164_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2164) 3).2 2).2
      866450935437807731225156359151627768768891929190222729921665782463548).isSome = true := by
  decide +kernel

theorem k2165_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2165) 3).1 2).1
      1178406183619656653042101683304773056016662200486002331474537274554991570271295914809733742924174483825245244).isSome = true := by
  decide +kernel

theorem k2165_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2165) 3).1 2).2
      249800945724463325577944572504907498620597722714923471033721494320867099130894086454332).isSome = true := by
  decide +kernel

theorem k2165_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2165) 3).2 2).1
      997515964519968336831561332234835589312876619546724810389907139526134473416038535281724).isSome = true := by
  decide +kernel

theorem k2165_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2165) 3).2 2).2
      249383288985010684956867320802440687795620525234943023538715949931147053408117415361596).isSome = true := by
  decide +kernel

theorem k2166_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2166) 3).1 1).1
      62302245398758417039266739682818731369033382671915358681184684124192335207622699232316).isSome = true := by
  decide +kernel

theorem k2166_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2166) 3).1 1).2
      249249957057444010216609044202457581641666475721656349465855330292738193567116298697788).isSome = true := by
  decide +kernel

theorem k2166_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2166) 3).2 2).1
      249092192999049119247178593722206052951682941562058745643976942344569065255776799833148).isSome = true := by
  decide +kernel

theorem k2166_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2166) 3).2 2).2
      210997530225772995515082985196596865315881258793244560687331949628).isSome = true := by
  decide +kernel

theorem k2167_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2167) 3).1
      5553075921199220169688102209118412909714154447019136448330524761678376413334664708389242000292079633741979837848412309175108743409).isSome = true := by
  decide +kernel

theorem k2167_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2167) 3).2
      1387775356767525873613971778912648175820066088736242309537840009628382989857375458766885885544947028163456091431723578174295879921).isSome = true := by
  decide +kernel

theorem k2168_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2168) 3).1
      293779357127121773112853885121343301566888401389365646653768738194415199169508317866595123654903903429549233).isSome = true := by
  decide +kernel

theorem k2168_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2168) 3).2
      1147273643950577845980575785461316745846770851883154541839751046740263593386596850744703635110326080789937).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2169 2188 [
    62166552354723802798391963100229669994613230763002606138628143019752555670480757099597,
    147576880898243426100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2188 2189 [
    839117301821941757135194060421794809033710615820648965587736355] = true := by
  decide +kernel

theorem k2189_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2189) 3).1
      1342735985312767370421959033769223606564677612063474207493114653871998241390113293262780818978227014039777548180290735797746).isSome = true := by
  decide +kernel

theorem k2189_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2189) 3).2 2).1
      18163017498114433113783042493108468390446285111315239707431353890553058537535924600389349791794129106172).isSome = true := by
  decide +kernel

theorem k2189_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2189) 3).2 2).2
      3843931271083444542379846750731388952099323790782735911934365035762348372341120380).isSome = true := by
  decide +kernel

theorem k2190_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2190) 3).1 2).1
      62872171948824930213872289576049545078596357111123896128299934935171459406037925190844).isSome = true := by
  decide +kernel

theorem k2190_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2190) 3).1 2).2
      72481915329432036612412865701585962893524292541858123633377796373022556909025886270137178542776761932988).isSome = true := by
  decide +kernel

theorem k2190_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2190) 3).2 2).1
      3401731674035007468003515059340837857448555412974155634970420128572).isSome = true := by
  decide +kernel

theorem k2190_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2190) 3).2 2).2
      3401682489804962978162086469583266270208429556606629217814425062204).isSome = true := by
  decide +kernel

theorem k2191_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2191) 3).1 2).1
      1002496874252167815183688967750642588900408318666743103961443065548062538803501049275196).isSome = true := by
  decide +kernel

theorem k2191_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2191) 3).1 2).2
      3396550361241971965066277082727960861151470547179920788652501721916).isSome = true := by
  decide +kernel

theorem k2191_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2191) 3).2 2).1
      73874594131911420181292502385076416544945880392901341059826666679631892590988558952861162069563458243773244).isSome = true := by
  decide +kernel

theorem k2191_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2191) 3).2 2).2
      54273256135303583455562725361179219423321525762487938951528423826236).isSome = true := by
  decide +kernel

theorem k2192_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2192) 3).1 2).1
      216831598519818468285483137333082466065853842667600070242662161235004).isSome = true := by
  decide +kernel

theorem k2192_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2192) 3).1 2).2
      62503748095139952037602015985150792207232716241231996124973313747153698371177407167548).isSome = true := by
  decide +kernel

theorem k2192_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2192) 3).2 1).1
      999023257009769962041330903512286803036886580933983787569792585724839128589415916977212).isSome = true := by
  decide +kernel

theorem k2192_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2192) 3).2 1).2
      3998654300882615314392452171297499662985498822968354232214660244153270570893790483889212).isSome = true := by
  decide +kernel

theorem k2193_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2193) 3).1 1).1
      216447052922831267433908262857146663269376382844267885920304835542076).isSome = true := by
  decide +kernel

theorem k2193_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2193) 3).1 1).2
      54146394578463370881746536034495273366916826199584748684068556848188).isSome = true := by
  decide +kernel

theorem k2193_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2193) 3).2 1).1
      216291509756565316185133568410350761476736825248298989194955654904892).isSome = true := by
  decide +kernel

theorem k2193_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2193) 3).2 1).2
      54082413888290234616579616753345744881307136634514031061010895551548).isSome = true := by
  decide +kernel

theorem k2194_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2194) 3).1 1).1
      45819021333268202207913315946271911205445975100).isSome = true := by
  decide +kernel

theorem k2194_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2194) 3).1 1).2
      54102887986331939384401172521434483399267375151489567796699367881788).isSome = true := by
  decide +kernel

theorem k2194_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2194) 3).2
      4183849433573853076598621811684734861380102208318153314219001429764930708145666081328190517489).isSome = true := by
  decide +kernel

theorem k2195_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2195) 1).1
      1175895061212073110846895902865812828680953521140877903496631185730615772681110858833584537858991346255573235).isSome = true := by
  decide +kernel

theorem k2195_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2195) 1).2
      16321873621274767045623736956172849053341266445327141888566887224395310144413413001458413811).isSome = true := by
  decide +kernel

theorem k2196_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2196) 1).1
      971678516199177010341609054499143569523213685801089064967863371587710907076962901171).isSome = true := by
  decide +kernel

theorem k2196_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2196) 1).2
      62194086874069520200221756544156431819775046916313202497639669374842895378979962182835).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2164 2197 :=
  (Cover.one (box := dirCellBox) (n := 2164)
      (.split 3 (.split 2 (.leaf _ k2164_0) (.leaf _ k2164_1)) (.split 2 (.leaf _ k2164_2) (.leaf _ k2164_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2165)
      (.split 3 (.split 2 (.leaf _ k2165_0) (.leaf _ k2165_1)) (.split 2 (.leaf _ k2165_2) (.leaf _ k2165_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2166)
      (.split 3 (.split 1 (.leaf _ k2166_0) (.leaf _ k2166_1)) (.split 2 (.leaf _ k2166_2) (.leaf _ k2166_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2167)
      (.split 3 (.leaf _ k2167_0) (.leaf _ k2167_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2168)
      (.split 3 (.leaf _ k2168_0) (.leaf _ k2168_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2189)
      (.split 3 (.leaf _ k2189_0) (.split 2 (.leaf _ k2189_1) (.leaf _ k2189_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2190)
      (.split 3 (.split 2 (.leaf _ k2190_0) (.leaf _ k2190_1)) (.split 2 (.leaf _ k2190_2) (.leaf _ k2190_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2191)
      (.split 3 (.split 2 (.leaf _ k2191_0) (.leaf _ k2191_1)) (.split 2 (.leaf _ k2191_2) (.leaf _ k2191_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2192)
      (.split 3 (.split 2 (.leaf _ k2192_0) (.leaf _ k2192_1)) (.split 1 (.leaf _ k2192_2) (.leaf _ k2192_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2193)
      (.split 3 (.split 1 (.leaf _ k2193_0) (.leaf _ k2193_1)) (.split 1 (.leaf _ k2193_2) (.leaf _ k2193_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2194)
      (.split 3 (.split 1 (.leaf _ k2194_0) (.leaf _ k2194_1)) (.leaf _ k2194_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2195)
      (.split 1 (.leaf _ k2195_0) (.leaf _ k2195_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2196)
      (.split 1 (.leaf _ k2196_0) (.leaf _ k2196_1)))

end C4.Cert.Dir031
