module

public import C4Check

public section

/-! Cells `2862 ≤ n < 2868` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir071

theorem k2862_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).1 1).1 2).1
      3401655495122909299500180638135848748076963959222788418196708572220).isSome = true := by
  decide +kernel

theorem k2862_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).1 1).1 2).2
      850617694020540819358919172465269946762289271111525567681036860476).isSome = true := by
  decide +kernel

theorem k2862_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).1 1).2 3).1
      3403761531803958385567097685326920932101985981004757019674468531260).isSome = true := by
  decide +kernel

theorem k2862_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).1 1).2 3).2
      849986612258588046198227822506684955851292210827710002713019071548).isSome = true := by
  decide +kernel

theorem k2862_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).2 1).1
      89627806004710578794535994319323916965854038605511227521060720948907481547174463991897191292542107165009372554758135887779098247996).isSome = true := by
  decide +kernel

theorem k2862_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2862) 3).1 2).2 1).2
      75978142298175535079807639644560087793311543493484734582019551060187055769284567070763120655942349161445112892).isSome = true := by
  decide +kernel

theorem k2862_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2862) 3).2 2).1 1).1
      4103576660470389021197739839349594024819596799585534080974092338497315131564891639778687795).isSome = true := by
  decide +kernel

theorem k2862_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).2 2).1 1).2 3).1
      849273691605825665034422288694491597291355999816416881742959819836).isSome = true := by
  decide +kernel

theorem k2862_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2862) 3).2 2).1 1).2 3).2
      2874686052274995480438037451519024895000915660).isSome = true := by
  decide +kernel

theorem k2862_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2862) 3).2 2).2 1).1
      296268273061558792983483108923065124383375552321845925171900805483796838488429367898499729484457146094238780).isSome = true := by
  decide +kernel

theorem k2862_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2862) 3).2 2).2 1).2
      296236462917287940817776527330728449076696681096142683489082257356926119895542997617899887531978078899977276).isSome = true := by
  decide +kernel

theorem k2863_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).1 2).1 1).1
      4730953110227613547563994468203461699193142342277986193510448555830189421200963773887371283815205604899468236).isSome = true := by
  decide +kernel

theorem k2863_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).1 2).1 1).2
      87182935631628822730007823891799137265722666331739131285668555028435197070613363642572370446580814986431695425306699985177066556).isSome = true := by
  decide +kernel

theorem k2863_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).1 2).2 1).1
      256313523415232472956524863147041162667642497402553952536688551782584746070448154253933628).isSome = true := by
  decide +kernel

theorem k2863_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).1 2).2 1).2
      295501661504437672733298020609990391080855077672933633950246887116030057432191559554738016620607237837765692).isSome = true := by
  decide +kernel

theorem k2863_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).2 2).1 1).1
      999699719951188730827625141211626040355765180311573171804222879727469737801025741835980).isSome = true := by
  decide +kernel

theorem k2863_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).2 2).1 1).2
      15994351530134365954529211329264727208536599172786944864901678664018274208013288292006972).isSome = true := by
  decide +kernel

theorem k2863_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).2 2).2 1).1
      15999702503053397220014943734836217369296045481060933183441495257250940864595822516560844).isSome = true := by
  decide +kernel

theorem k2863_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2863) 3).2 2).2 1).2
      54208947278156542716241598779110123915769203996147269798425324633148).isSome = true := by
  decide +kernel

theorem k2864_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).1 3).1 1).1
      3383682494128416710924408886393030048034222385285378268094634208972).isSome = true := by
  decide +kernel

theorem k2864_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).1 3).1 1).2
      249671536948261945118216231871413262453822952258323254822949181870624749673413577849916).isSome = true := by
  decide +kernel

theorem k2864_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).1 3).2 1).1
      3381100850864964436804751516159557054681013526934532762752442511052).isSome = true := by
  decide +kernel

theorem k2864_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).1 3).2 1).2
      3381176028574057124808114779246455884876176285892294124604346907708).isSome = true := by
  decide +kernel

theorem k2864_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).2 3).1 1).1
      846201424970809747735344640582104385541202904826843679603833130700).isSome = true := by
  decide +kernel

theorem k2864_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).2 3).1 1).2
      62439949143398470545342775882900217845072217296905729985366484187368839857465497959484).isSome = true := by
  decide +kernel

theorem k2864_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).2 3).2 1).1
      211380124284091259903502311128699388865162027130468396037257550540).isSome = true := by
  decide +kernel

theorem k2864_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2864) 2).2 3).2 1).2
      62390249441811319926261054141353831188361146490753648851826217158661237226844718578748).isSome = true := by
  decide +kernel

theorem k2865_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2865) 2).1 3).1
      16339842519288424501098523153709433387156500699829733344440577913779664883183910050140220209).isSome = true := by
  decide +kernel

theorem k2865_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2865) 2).1 3).2
      18829531182140805229044857862373609423194094864521483728734477694181065370827033883286783701811288589122001713).isSome = true := by
  decide +kernel

theorem k2865_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2865) 2).2 3).1 1).1
      211239906483592604758497561097403803220925211969197313312821861068).isSome = true := by
  decide +kernel

theorem k2865_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2865) 2).2 3).1 1).2
      45803107283945270944199879403181181368775404604).isSome = true := by
  decide +kernel

theorem k2865_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2865) 2).2 3).2
      4708327267898227153724514301247159301743024308763718792086710659005514494279795845795235051670001711756729137).isSome = true := by
  decide +kernel

theorem k2866_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2866) 3).1 2).1
      73525833244343879304935042732732484743520389780012656444284569538906471704410140096591284401417001320700721).isSome = true := by
  decide +kernel

theorem k2866_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2866) 3).1 2).2
      294157786771536685414331409046423583963575855633041743729027054597381061105959605617243172978401494164094012).isSome = true := by
  decide +kernel

theorem k2866_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2866) 3).2 2).1
      18375332770184035813667967183536855282719379100753419452620334983332524375224817949244236538570831171017521).isSome = true := by
  decide +kernel

theorem k2866_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2866) 3).2 2).2
      73512926004438798619619655946735853968030884783186561002276788868208524929521771306304521076884033150696508).isSome = true := by
  decide +kernel

theorem k2867_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2867) 2).1 3).1
      3890153437215525338019384428311498815801965421059018400712311578562277869123485620017).isSome = true := by
  decide +kernel

theorem k2867_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2867) 2).1 3).2
      972341839774569096660574078982096536124338584225147540265446035879782751902522768444).isSome = true := by
  decide +kernel

theorem k2867_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2867) 2).2 3).1
      18372532029813831785360044542243252661786383276546459923160253774976799610066759839100158634756713217834044).isSome = true := by
  decide +kernel

theorem k2867_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2867) 2).2 3).2
      52737223638671565715097243491740605316666157765513390364504702012).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2862 2868 :=
  (Cover.one (box := dirCellBox) (n := 2862)
      (.split 3 (.split 2 (.split 1 (.split 2 (.leaf _ k2862_0) (.leaf _ k2862_1)) (.split 3 (.leaf _ k2862_2) (.leaf _ k2862_3))) (.split 1 (.leaf _ k2862_4) (.leaf _ k2862_5))) (.split 2 (.split 1 (.leaf _ k2862_6) (.split 3 (.leaf _ k2862_7) (.leaf _ k2862_8))) (.split 1 (.leaf _ k2862_9) (.leaf _ k2862_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2863)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2863_0) (.leaf _ k2863_1)) (.split 1 (.leaf _ k2863_2) (.leaf _ k2863_3))) (.split 2 (.split 1 (.leaf _ k2863_4) (.leaf _ k2863_5)) (.split 1 (.leaf _ k2863_6) (.leaf _ k2863_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2864)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2864_0) (.leaf _ k2864_1)) (.split 1 (.leaf _ k2864_2) (.leaf _ k2864_3))) (.split 3 (.split 1 (.leaf _ k2864_4) (.leaf _ k2864_5)) (.split 1 (.leaf _ k2864_6) (.leaf _ k2864_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2865)
      (.split 2 (.split 3 (.leaf _ k2865_0) (.leaf _ k2865_1)) (.split 3 (.split 1 (.leaf _ k2865_2) (.leaf _ k2865_3)) (.leaf _ k2865_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2866)
      (.split 3 (.split 2 (.leaf _ k2866_0) (.leaf _ k2866_1)) (.split 2 (.leaf _ k2866_2) (.leaf _ k2866_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2867)
      (.split 2 (.split 3 (.leaf _ k2867_0) (.leaf _ k2867_1)) (.split 3 (.leaf _ k2867_2) (.leaf _ k2867_3))))

end C4.Cert.Dir071
