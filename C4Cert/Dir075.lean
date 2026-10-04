module

public import C4Check

public section

/-! Cells `2925 ≤ n < 2953` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir075

theorem k2925_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2925) 3).1
      1174972750074849651686437297315496991623967168042317244512592823186027998680275078505514258257817997128620849).isSome = true := by
  decide +kernel

theorem k2925_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2925) 3).2
      5420553078132779480102636390758601048969183318995262231107456137803167225687784120724751655772088481506942351983690917770738748).isSome = true := by
  decide +kernel

theorem k2926_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2926) 3).1
      15546605236402101415782477964114017279441548045738041480912449536245836558364569851697).isSome = true := by
  decide +kernel

theorem k2926_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2926) 3).2
      52667934586811490848754657387624470801336642835920681748093400241).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 2927 2944 [
    3885378900589339362666857335155444875441487267634717531840852466769462681548089567601,
    147549062704281636356, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155628815776754226450531] = true := by
  decide +kernel

theorem k2944_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2944) 3).1
      21640549087850068665638917337878019553707164702733703750936508996215328002029863046905723375152458287731473718336552040265158).isSome = true := by
  decide +kernel

theorem k2944_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2944) 3).2 2).1
      86218851800599352434707211746258538080687490698780419677944842648086934186830181680648825109156852474904199775201496289080561).isSome = true := by
  decide +kernel

theorem k2944_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2944) 3).2 2).2
      61908177879555794509325597773578615236447960445567551419683769250867075264610038129).isSome = true := by
  decide +kernel

theorem k2945_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2945) 3).1 2).1
      4657944787906432481881686501084332266103453962921173806551663415899801473648840261065723353759585084792241).isSome = true := by
  decide +kernel

theorem k2945_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2945) 3).1 2).2
      291202189296174721480178663802778052106997033673021591081782059643578761884240030995456428860076495196988).isSome = true := by
  decide +kernel

theorem k2945_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2945) 3).2 2).1
      304596858666397823636985682897183596693455306624390846470325716968616429437396183716365017717621479994165355324).isSome = true := by
  decide +kernel

theorem k2945_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2945) 3).2 2).2
      251930927658428958026784487847951744760075516844276935665945754752339338337645748908721).isSome = true := by
  decide +kernel

theorem k2946_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2946) 3).1 2).1
      21910083447296469165775959515664004790346725063092567981319361914904039031179614443941741348256012381101442125149503265565307452).isSome = true := by
  decide +kernel

theorem k2946_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2946) 3).1 2).2
      296951292817657147923356330456972794764950685313335733366574619579899516571898996073739351835631352666387004).isSome = true := by
  decide +kernel

theorem k2946_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2946) 3).2 2).1
      303449226059067580284214173188267483476830287702720337908831262793254749233420209385327308770516605420083474673).isSome = true := by
  decide +kernel

theorem k2946_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2946) 3).2 2).2
      4016937486418680297371978762160790958334035021165483126049778532140880990771780768824380).isSome = true := by
  decide +kernel

theorem k2947_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2947) 2).1 3).1
      1397414770969390492608825879334444553277954481850956530417842205588713645256855751280307087293276530388721535243404008189284760636).isSome = true := by
  decide +kernel

theorem k2947_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2947) 2).1 3).2 1).1
      848048113778513859134925408152585936094712024949404846526518049852).isSome = true := by
  decide +kernel

theorem k2947_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2947) 2).1 3).2 1).2
      11492986929212791892541636755454161425459199036).isSome = true := by
  decide +kernel

theorem k2947_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2947) 2).2 3).1
      3478600044901287307740531273586130776758976794054899958041050811644988).isSome = true := by
  decide +kernel

theorem k2947_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2947) 2).2 3).2
      256343694187511729758986100761126370300654251905635844488235264929118753579106686650334268).isSome = true := by
  decide +kernel

theorem k2948_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2948) 2).1 3).1
      1209096750620001149674659031834477055372348555444906661396581937786562762756659191319141296870722038980485626940).isSome = true := by
  decide +kernel

theorem k2948_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2948) 2).1 3).2
      75496113463795758426527843260658817377188148711694595682856523435352809904222339331462308642311023591227604028).isSome = true := by
  decide +kernel

theorem k2948_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2948) 2).2 3).1
      4723672146277897153500453398592456155259351497227154086092094196192579725578516527659509322875455964097330236).isSome = true := by
  decide +kernel

theorem k2948_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2948) 2).2 3).2
      63956545966420910533540132013071818583238223700335733736645397288256393652968547534191676).isSome = true := by
  decide +kernel

theorem k2949_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2949) 2).1 3).1
      4089488780434859642497606155106233926251249971104793687918568800550642677473631534729870396).isSome = true := by
  decide +kernel

theorem k2949_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2949) 2).1 3).2
      4086804924548790004645573037968091995345445990134924810117370466698270676669509934112193596).isSome = true := by
  decide +kernel

theorem k2949_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2949) 2).2 1).1
      1022137016921762073658551657183262200598723876096111259383923214953170144963829904165780540).isSome = true := by
  decide +kernel

theorem k2949_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2949) 2).2 1).2
      255796754044512581002062195249436523421560097859578143973557199775620260325114122168646716).isSome = true := by
  decide +kernel

theorem k2950_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2950) 3).1 2).1
      3459763634451560117586804452401722054171775064512702144751563776343100).isSome = true := by
  decide +kernel

theorem k2950_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2950) 3).1 2).2
      216258413461428421759178130001637151932794584850091047024063889947708).isSome = true := by
  decide +kernel

theorem k2950_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2950) 3).2 2).1
      54037246450346297118755191352643047460975665647347521632416520617020).isSome = true := by
  decide +kernel

theorem k2950_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2950) 3).2 2).2
      54039518610533113832542472127546907465989617328723826734252309232700).isSome = true := by
  decide +kernel

theorem k2951_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2951) 3).1 1).1
      54014106291428399627097608062955394003733246789301259412597097511996).isSome = true := by
  decide +kernel

theorem k2951_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2951) 3).1 1).2
      13504501814768313891790965744560837892733797714659441752929079802940).isSome = true := by
  decide +kernel

theorem k2951_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2951) 3).2
      419595934048681047331834089526374266430190934044898844980184450365501959054566361592504485765176847675343945588119416253994686442842560419691030372891708).isSome = true := by
  decide +kernel

theorem k2952_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2952) 3).1 2).1
      210856570452207634019582300549425107605035233620928275743897959484).isSome = true := by
  decide +kernel

theorem k2952_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2952) 3).1 2).2
      210863930746344728355832093441809651789194508418924520875719277628).isSome = true := by
  decide +kernel

theorem k2952_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2952) 3).2
      1387624304187541120387000187761568509702838762218722982812326329297946717580579144384792524224653000865660601434236536459420872945).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2925 2953 :=
  (Cover.one (box := dirCellBox) (n := 2925)
      (.split 3 (.leaf _ k2925_0) (.leaf _ k2925_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2926)
      (.split 3 (.leaf _ k2926_0) (.leaf _ k2926_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 2944)
      (.split 3 (.leaf _ k2944_0) (.split 2 (.leaf _ k2944_1) (.leaf _ k2944_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2945)
      (.split 3 (.split 2 (.leaf _ k2945_0) (.leaf _ k2945_1)) (.split 2 (.leaf _ k2945_2) (.leaf _ k2945_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2946)
      (.split 3 (.split 2 (.leaf _ k2946_0) (.leaf _ k2946_1)) (.split 2 (.leaf _ k2946_2) (.leaf _ k2946_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2947)
      (.split 2 (.split 3 (.leaf _ k2947_0) (.split 1 (.leaf _ k2947_1) (.leaf _ k2947_2))) (.split 3 (.leaf _ k2947_3) (.leaf _ k2947_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2948)
      (.split 2 (.split 3 (.leaf _ k2948_0) (.leaf _ k2948_1)) (.split 3 (.leaf _ k2948_2) (.leaf _ k2948_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2949)
      (.split 2 (.split 3 (.leaf _ k2949_0) (.leaf _ k2949_1)) (.split 1 (.leaf _ k2949_2) (.leaf _ k2949_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2950)
      (.split 3 (.split 2 (.leaf _ k2950_0) (.leaf _ k2950_1)) (.split 2 (.leaf _ k2950_2) (.leaf _ k2950_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2951)
      (.split 3 (.split 1 (.leaf _ k2951_0) (.leaf _ k2951_1)) (.leaf _ k2951_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2952)
      (.split 3 (.split 2 (.leaf _ k2952_0) (.leaf _ k2952_1)) (.leaf _ k2952_2)))

end C4.Cert.Dir075
