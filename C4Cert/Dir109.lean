module

public import C4Check

public section

/-! Cells `3560 ≤ n < 3563` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir109

theorem k3560_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).1 3).1
      1618819786684257044354021256610471174009797219786840037608431777307392961526004535317685095132185794364507978809936735167662052900445229978709085105).isSome = true := by
  decide +kernel

theorem k3560_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).1 3).2
      6312259406258850173895114272968039697111308852899597686541790010443205644742974973880092333211084291234994815923938514866616040634957252290533297).isSome = true := by
  decide +kernel

theorem k3560_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).2 3).1
      101318719200268985840583461999238920047318019631670656331632668683415444350280098975181106584633398552853212109089226267661685379127971357265360561).isSome = true := by
  decide +kernel

theorem k3560_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).2 3).2
      101114620653596157791816868568121393885576977854276159060397663800436964018096155411083231416739531481455720104513315207285140933897286155080431281).isSome = true := by
  decide +kernel

theorem k3560_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 2).1 3).1
      72376689398516823195180740705403668647836429370341908383159532641751375359703318870522162333053799724273).isSome = true := by
  decide +kernel

theorem k3560_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 2).1 3).2
      72289604439422128089510830660572727207917712880358486462279407781940527551668396807167721992812008404209).isSome = true := by
  decide +kernel

theorem k3560_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 2).2 3).1
      21371949837319637844371612068164419144925407690617962035922298761489440932091169764932425309568400577995586598921372411387313).isSome = true := by
  decide +kernel

theorem k3560_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 2).2 3).2
      72331105366007063476863144664991035729957610729077268641725758509196401906282898057770772806646986333617).isSome = true := by
  decide +kernel

theorem k3560_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).1 3).1 1).1
      246696566738163779770217604625712890790961909389141747267775155080329620428143820204).isSome = true := by
  decide +kernel

theorem k3560_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).1 3).1 1).2
      4548615878963519960613329787172069350731770964337940216096084220137856346519852522785254887768041414508).isSome = true := by
  decide +kernel

theorem k3560_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).1 3).2
      101215001663523048544069223351144786320793631524727961726366993319010658054308208100552043525138774929421821729574582602249453532912011352039880369).isSome = true := by
  decide +kernel

theorem k3560_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).2 3).1 1).1
      53600915518023518708911006091768579273084913379759717139215662252).isSome = true := by
  decide +kernel

theorem k3560_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).2 3).1 1).2
      13380605703208129454793211458281269468459968444706463934859279532).isSome = true := by
  decide +kernel

theorem k3560_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).2 3).2 1).1
      13354879608606942303768567351104687590929938388727354271397936300).isSome = true := by
  decide +kernel

theorem k3560_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).2 3).2 1).2
      15393061536083984397056947705327739866025568160125765474866973875032112662778306412).isSome = true := by
  decide +kernel

theorem k3560_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).1 3).1
      21908065439081295884155346449261822339892175391996910336922204256823438699571372293355225172810640954524329604061303208145188529).isSome = true := by
  decide +kernel

theorem k3560_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).1 3).2
      21362953906197608789679464365325753661863013541766024543114642658139774832323154407563223861019334854693694258246052488895921).isSome = true := by
  decide +kernel

theorem k3560_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).2 3).1
      21927084647536317395058862495608109928970961160573661962960788814487477774656720811410017095460485364683036095993403508470970033).isSome = true := by
  decide +kernel

theorem k3560_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).2 3).2
      85514974440268823665007628231505667520605989974185731861315410558833558650715634705971411453449851437774757968617792323811761).isSome = true := by
  decide +kernel

theorem k3561_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).1 3).1
      288872455017235215728002521433098964449959636340612510505704569132652635708949172589142791279309167645425).isSome = true := by
  decide +kernel

theorem k3561_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).1 3).2
      1331096770577574167853220610738810558319625712859335617331072164841152803686172469500209032986165841982454056779845274793457).isSome = true := by
  decide +kernel

theorem k3561_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).2 3).1
      15667952776693099131889911675237702589964245268698738157582664208925208296834514187505).isSome = true := by
  decide +kernel

theorem k3561_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).2 3).2
      15653414732510063096665857829208198563320960717079337524803401886051727189295439705329).isSome = true := by
  decide +kernel

theorem k3561_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).2 2).1
      6278924082029316746991182151510659929818709705509459982361278084801765158411627362692057150843460987010453735079624969799930327506765648054478285).isSome = true := by
  decide +kernel

theorem k3561_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).2 2).2 1).1
      3908460459603241296053327487326489159752582580308825686854781073137423903065883382515).isSome = true := by
  decide +kernel

theorem k3561_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).2 2).2 1).2
      3817582784329089318433112279371283193747418963010657384498438024809911252799348092).isSome = true := by
  decide +kernel

theorem k3561_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).1 3).1
      15675807048204114003845380828419995721828075831951556205361832060118874242152122326449).isSome = true := by
  decide +kernel

theorem k3561_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).1 3).2
      978823524503775186808312961149484891530471285818205179067422988067978997096338713009).isSome = true := by
  decide +kernel

theorem k3561_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).2 3).1
      4629571224667289349672073178575809338499672433581827604435441593067717355761807056865898075278139237637553).isSome = true := by
  decide +kernel

theorem k3561_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).2 3).2
      1156096822198374105006085639250371492019585075000822560117208519176852679566000934262402424044998716844465).isSome = true := by
  decide +kernel

theorem k3561_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 2).1 1).1
      15644010272720523855035720139996235111175667169424892115663026857471163098009920434876).isSome = true := by
  decide +kernel

theorem k3561_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 2).1 1).2
      15269632384654119336915529974693565592134330403302498633756959703103340170522292595).isSome = true := by
  decide +kernel

theorem k3561_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 2).2 1).1
      3917518742676330098272117592886287103411426992606562852350288871856391113310241019708).isSome = true := by
  decide +kernel

theorem k3561_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 2).2 1).2
      61102249078876214166645771426867598286806290807833383757604329169609610721636246963).isSome = true := by
  decide +kernel

theorem k3562_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3562) 2).1 2).1
      7400948961718458109403985435342248211914440565825613961642191678178665253381104088124584179067787456489975687281087402095362011866298657635448576592489493422456903447).isSome = true := by
  decide +kernel

theorem k3562_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).1 2).2 3).1
      1568429745150411937149556682106337074285244345095723744057227676911188074658185822068489119862017640276986072732865923590688653604414884229772785).isSome = true := by
  decide +kernel

theorem k3562_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).1 2).2 3).2
      15240016388123348411122438933852208895955810852268116646445681724663877269605459313).isSome = true := by
  decide +kernel

theorem k3562_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).1 2).1
      463108057791941642441050847922720704102856615574022992446793911955155393650393188207024725031288268532322310460195294889702293691244675732917110345890728020585579981).isSome = true := by
  decide +kernel

theorem k3562_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).1 2).2 1).1
      3907095768421397913464770821554514359908096542847026234508895175807339678957538598076).isSome = true := by
  decide +kernel

theorem k3562_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).1 2).2 1).2
      3815366098008083483152383886235159039608908156927313277287133968315732386544967036).isSome = true := by
  decide +kernel

theorem k3562_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).2 1).1
      5438504687604289774211914949426099602965595293627580111985509979982609024376054750880101116210761535237369972816631468446307059).isSome = true := by
  decide +kernel

theorem k3562_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).2 1).2
      391981842372639550778817425889641958488348244037768689723968492868153932679929047918349981447919854985096769232614039149479585690957019624199666).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3560 3563 :=
  (Cover.one (box := dirCellBox) (n := 3560)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3560_0) (.leaf _ k3560_1)) (.split 3 (.leaf _ k3560_2) (.leaf _ k3560_3))) (.split 2 (.split 3 (.leaf _ k3560_4) (.leaf _ k3560_5)) (.split 3 (.leaf _ k3560_6) (.leaf _ k3560_7)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3560_8) (.leaf _ k3560_9)) (.leaf _ k3560_10)) (.split 3 (.split 1 (.leaf _ k3560_11) (.leaf _ k3560_12)) (.split 1 (.leaf _ k3560_13) (.leaf _ k3560_14)))) (.split 2 (.split 3 (.leaf _ k3560_15) (.leaf _ k3560_16)) (.split 3 (.leaf _ k3560_17) (.leaf _ k3560_18)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3561)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3561_0) (.leaf _ k3561_1)) (.split 3 (.leaf _ k3561_2) (.leaf _ k3561_3))) (.split 2 (.leaf _ k3561_4) (.split 1 (.leaf _ k3561_5) (.leaf _ k3561_6)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3561_7) (.leaf _ k3561_8)) (.split 3 (.leaf _ k3561_9) (.leaf _ k3561_10))) (.split 2 (.split 1 (.leaf _ k3561_11) (.leaf _ k3561_12)) (.split 1 (.leaf _ k3561_13) (.leaf _ k3561_14)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3562)
      (.split 2 (.split 2 (.leaf _ k3562_0) (.split 3 (.leaf _ k3562_1) (.leaf _ k3562_2))) (.split 3 (.split 2 (.leaf _ k3562_3) (.split 1 (.leaf _ k3562_4) (.leaf _ k3562_5))) (.split 1 (.leaf _ k3562_6) (.leaf _ k3562_7)))))

end C4.Cert.Dir109
