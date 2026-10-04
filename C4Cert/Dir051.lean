module

public import C4Check

public section

/-! Cells `2532 ≤ n < 2580` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir051

theorem k2532_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2532) 3).1
      1601429513617821272117412344931975506907109615430253786962112318884859732037340607083242778602992362301042012996310911406952255455149845794672466737).isSome = true := by
  decide +kernel

theorem k2532_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2532) 3).2
      5419140231885276979753609300333080726378016449397698185250890785030525119851948922569747086031691134802839334437097604666219313).isSome = true := by
  decide +kernel

theorem k2533_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2533) 3).1
      4589187104623060764277846039290522070580513935862862817192062058661215732220220726828249431751842137937713).isSome = true := by
  decide +kernel

theorem k2533_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2533) 3).2
      15546251846182096950472448569758748387230397619797822350691419787052077781083056397489).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 2534 2552 [
    4589312848044553104691558495592040487263418837498647080377721933391724179083974935842156974162786468355397,
    2360788947216318798657, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k2552_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2552) 3).1
      62141820759992257756551936391152928304461026775787826327254967388282562635483659078).isSome = true := by
  decide +kernel

theorem k2552_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2552) 3).2
      30075245313604482129197901161376671588684446530768746490468289915588616178980900200822440400713313358829199400724623528503065162038345123291285347781552363359080641990).isSome = true := by
  decide +kernel

theorem k2553_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2553) 3).1 2).1
      344101502154115610327065630818365041710810104837109773156694325874888049276579838150192180098627158709552978457680977192645873).isSome = true := by
  decide +kernel

theorem k2553_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2553) 3).1 2).2
      85938829701756810081960753756686374097699337941286073089202990023239904557223612591846305377703682322086394796399557730988284).isSome = true := by
  decide +kernel

theorem k2553_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2553) 3).2 2).1
      76191361133295169097861835313854794122161908393709618788553353311113224247017053518546268097535599548566198513).isSome = true := by
  decide +kernel

theorem k2553_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2553) 3).2 2).2
      1162627937382799917406201154775150137591754347340137221790294717384345540803407901338413590882769851731772).isSome = true := by
  decide +kernel

theorem k2554_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2554) 3).1 2).1
      4751006227335884455087065481087282609864862681342622838663249835669256255026681678908359606152500779580437308).isSome = true := by
  decide +kernel

theorem k2554_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2554) 3).1 2).2
      74236646053416866825737923215553971796386247645372277987389557210224492766838625989280940846300135683306300).isSome = true := by
  decide +kernel

theorem k2554_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2554) 3).2 2).1
      263219908279257200663368957095043985926410136315682333423682873901471789961161932279845431537).isSome = true := by
  decide +kernel

theorem k2554_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2554) 3).2 2).2
      64267623026003362796403686541812776546465691348909307458759759574041450679738094157865788).isSome = true := by
  decide +kernel

theorem k2555_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2555) 3).1 2).1
      75750050893230707138489305798917860877729104826054229962490012448593995421810077569564415637887117602714493756).isSome = true := by
  decide +kernel

theorem k2555_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2555) 3).1 2).2
      16042596880327410106827087220522893069252305098024843910975352067467090518806858255287100).isSome = true := by
  decide +kernel

theorem k2555_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2555) 3).2 2).1
      75686282175767634978468488228831652226552273253553693121125164706759031427972143421797379173004946169070863164).isSome = true := by
  decide +kernel

theorem k2555_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2555) 3).2 2).2
      64113394099173588781541625552851389800165880816677658727668626349194256980878001626399548).isSome = true := by
  decide +kernel

theorem k2556_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2556) 3).1 2).1
      75566577198231058780958367162415301998106427867174857230850369274753230894729445429775104026909080609699445820).isSome = true := by
  decide +kernel

theorem k2556_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2556) 3).1 2).2
      54243904081160536563619462510320117526301373801852857395335776091196).isSome = true := by
  decide +kernel

theorem k2556_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2556) 3).2 2).1
      18872895623794045132121686700514218652825610718089707709389129912320330775408558737590705441433637464853658684).isSome = true := by
  decide +kernel

theorem k2556_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2556) 3).2 2).2
      3996997403161517112430263937435860293690095902176573482688092964408707870544286854102076).isSome = true := by
  decide +kernel

theorem k2557_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2557) 3).1 2).1
      63894696375978115672530940229784330804313440201941255834092948510799892397539937052408892).isSome = true := by
  decide +kernel

theorem k2557_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2557) 3).1 2).2
      865995897184830181172053619816150773578559197328362451932987831565372).isSome = true := by
  decide +kernel

theorem k2557_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2557) 3).2 2).1
      15962434102164107212927018271856067967922350742775642888116981263260870653624057307216956).isSome = true := by
  decide +kernel

theorem k2557_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2557) 3).2 2).2
      216353479514396134641519374081907482120861223412186015107904628735036).isSome = true := by
  decide +kernel

theorem k2558_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2558) 3).1 2).1
      249289068614573202828135133420107859191609934537799439470228090932776492417290849369148).isSome = true := by
  decide +kernel

theorem k2558_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2558) 3).1 2).2
      54057739957210135509301698104387466196788027334944445243350303783996).isSome = true := by
  decide +kernel

theorem k2558_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2558) 3).2 1).1
      249153584459487486846996712523416919889102491364951256257562153141011897809551708535868).isSome = true := by
  decide +kernel

theorem k2558_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2558) 3).2 1).2
      54032563305612863113748474756292419750921636192814615493429215771708).isSome = true := by
  decide +kernel

theorem k2559_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2559) 3).1 1).1
      15565238101372204981985126468619585817507914281842096813752261656367363055524945701948).isSome = true := by
  decide +kernel

theorem k2559_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2559) 3).1 1).2
      54009106479462236890458545219648715126796748849957849128208300391484).isSome = true := by
  decide +kernel

theorem k2559_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2559) 3).2
      5552470494639518450139157730641952434430247757455063190827205591961431285773496546893197212265688580655896510400557020463010525425).isSome = true := by
  decide +kernel

theorem k2560_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2560) 1).1
      1174978044862422123170526818858595113658082517967740096126416057080813691067696397647371432357186242229416179).isSome = true := by
  decide +kernel

theorem k2560_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2560) 1).2
      1387344235302433930959628105842843741945485830630096081005824518407893281315827479349800877208338068525494982951038897402440167667).isSome = true := by
  decide +kernel

theorem k2561_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2561) 3).1
      62228602006321885065398877261281554444891956830539086294080196761901903381796258995377).isSome = true := by
  decide +kernel

theorem k2561_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2561) 3).2
      842770247390721489634698048921447719745588772824566914708175639217).isSome = true := by
  decide +kernel

theorem c13 : allCells dirCell 2562 2580 [
    17918183613614422173901687868330100952369098401644146016951967360893167986050057068297047463318386428273,
    147537520512274003988, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2532 2580 :=
  (Cover.one (box := dirCellBox) (n := 2532)
      (.split 3 (.leaf _ k2532_0) (.leaf _ k2532_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2533)
      (.split 3 (.leaf _ k2533_0) (.leaf _ k2533_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 2552)
      (.split 3 (.leaf _ k2552_0) (.leaf _ k2552_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2553)
      (.split 3 (.split 2 (.leaf _ k2553_0) (.leaf _ k2553_1)) (.split 2 (.leaf _ k2553_2) (.leaf _ k2553_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2554)
      (.split 3 (.split 2 (.leaf _ k2554_0) (.leaf _ k2554_1)) (.split 2 (.leaf _ k2554_2) (.leaf _ k2554_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2555)
      (.split 3 (.split 2 (.leaf _ k2555_0) (.leaf _ k2555_1)) (.split 2 (.leaf _ k2555_2) (.leaf _ k2555_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2556)
      (.split 3 (.split 2 (.leaf _ k2556_0) (.leaf _ k2556_1)) (.split 2 (.leaf _ k2556_2) (.leaf _ k2556_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2557)
      (.split 3 (.split 2 (.leaf _ k2557_0) (.leaf _ k2557_1)) (.split 2 (.leaf _ k2557_2) (.leaf _ k2557_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2558)
      (.split 3 (.split 2 (.leaf _ k2558_0) (.leaf _ k2558_1)) (.split 1 (.leaf _ k2558_2) (.leaf _ k2558_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2559)
      (.split 3 (.split 1 (.leaf _ k2559_0) (.leaf _ k2559_1)) (.leaf _ k2559_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2560)
      (.split 1 (.leaf _ k2560_0) (.leaf _ k2560_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2561)
      (.split 3 (.leaf _ k2561_0) (.leaf _ k2561_1))).trans <|
  (Cover.dir c13)

end C4.Cert.Dir051
