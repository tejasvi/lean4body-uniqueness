module

public import C4Check

public section

/-! Cells `2745 ≤ n < 2746` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir057

theorem k2745_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).1
      8870353905344048187592917676973051014925033069777250505007923658036331445682331914811134340804615156563387222527637104601223870742985116492790532146775865299536917333291).isSome = true := by
  decide +kernel

theorem k2745_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).1
      28039533997435927959372942797828637179305802050203149340051846387798809840233509123652289450521394215397050343350979742736929781599032333711753543).isSome = true := by
  decide +kernel

theorem k2745_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).2
      80799128049264461335409597323820196769656251611229773952419914174608575523827485186777410900141288426315).isSome = true := by
  decide +kernel

theorem k2745_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).1
      2008172581086711237330893433073173707830692875973485790354650534309736731684130681025818460694831897621348680106110497338743654948108395106120678548979900055433455054).isSome = true := by
  decide +kernel

theorem k2745_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).2
      23151649812731592882530499542569688719050149696519490766915352429263041591664200760201341873252028402636935858701487257771079).isSome = true := by
  decide +kernel

theorem k2745_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).1
      1966240769155629134029342283116716981634104752515251854087972468398198585486353965270592468182897102635713741727352621687658489877155793761436340406438164613610563022).isSome = true := by
  decide +kernel

theorem k2745_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).2
      123464060249509676319343285700688217880758391812903555219394501076240040971397807553305664974118276611768145884335092531524487070072295917691552930199204252357064179).isSome = true := by
  decide +kernel

theorem k2745_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).1 3).1
      844251456165509396035440951452840739124872711).isSome = true := by
  decide +kernel

theorem k2745_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).1 3).2
      33524367024456120976010899524369736166621611821364448784580689852407258042917451956767602698490513583728568037173400981908135606444064043537339907267627006020617220379).isSome = true := by
  decide +kernel

theorem k2745_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).1 2).1
      23444645967825997297023970708669752818682439500174521733816523054197605849230313631382815388740739118367363382398631042295110).isSome = true := by
  decide +kernel

theorem k2745_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).1 2).2
      16767401468964992288792667073580539077658128747031035490803113077585123602979636595).isSome = true := by
  decide +kernel

theorem k2745_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).1
      124802015856904633603365859190133518478065060376071885910346098578397143706777510941621896466337657102697458528790611556664702121140322679228453881084956691241465330).isSome = true := by
  decide +kernel

theorem k2745_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).2
      1429696530054135308714265651738705283448108341999131755378622644227373710065126212888010429136957578223532119407984383924083).isSome = true := by
  decide +kernel

theorem k2745_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).1
      30007299766076168616546568614902987267280645328199950174190475962581594174732251581401611316879539751759489581884275785367793968515172297248142618).isSome = true := by
  decide +kernel

theorem k2745_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).2 2).1
      1542960039801516826108818496109647063097689861513382182182555197493280190528247578203214874132351694946215008425955831150066).isSome = true := by
  decide +kernel

theorem k2745_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).2 2).2
      17764025274460842358500404036105292392344702839216918209998131659085135632892312945).isSome = true := by
  decide +kernel

theorem k2745_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).1
      445286257756052012328355513373364423208311910150969035768114844875244822409131759952139993529676919256070516738363859177071432320919051002017266).isSome = true := by
  decide +kernel

theorem k2745_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).2
      379036855951436189918430864723709147563316246524712400038971756817787624226334717923153029446610076586693438636265225112548850).isSome = true := by
  decide +kernel

theorem k2745_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).2
      2075758670468058764349120730150557429351855919532875614943715186789905942099474969789823771195271514656535910714032492996660786643484404754981044142625426307624248782).isSome = true := by
  decide +kernel

theorem k2745_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 2).1
      4969530346034866602074742602786677936187505277295955895274359892076677456687453861327587742442146962630131).isSome = true := by
  decide +kernel

theorem k2745_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 2).2
      5018158596433174707979273077201818717688256962999137758915506314358727739463231060071546326008720935773681).isSome = true := by
  decide +kernel

theorem k2745_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).1
      67327386996738119439470559066293024387541089074666913812629209172753906841833068146).isSome = true := by
  decide +kernel

theorem k2745_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).2
      19609482645814984395988142258386688519322119095585756007355003843132759698275438161797648807705939961330).isSome = true := by
  decide +kernel

theorem k2745_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 2).1
      16500556619385120526509843852375407115080209759721813400399821265949729808237918905587).isSome = true := by
  decide +kernel

theorem k2745_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 2).2
      4158380395031576348832349694184161474486568264957431726165724720738355461248769316668).isSome = true := by
  decide +kernel

theorem k2745_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 2).1
      4171209181529767179031504970795955909998850338707436653590994314671896835178675264700).isSome = true := by
  decide +kernel

theorem k2745_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 2).2
      4182924368365875794643486563218237097496675711450560716250443939064050711049296370876).isSome = true := by
  decide +kernel

theorem k2745_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).1
      398644489222229684651208640853165360512917218744821729282891954410781577992736381435674710580556642218122781866434821998977307).isSome = true := by
  decide +kernel

theorem k2745_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).2 3).1
      20668209901743531616774519335239057497904114717187529736532519594232997838140430925476603156700133609030).isSome = true := by
  decide +kernel

theorem k2745_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).2 3).2
      1498603398166145504187328044697703282936215396277667437846960197904695244898823263090663800793047352715796661433776383292914).isSome = true := by
  decide +kernel

theorem k2745_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).1
      109721317084626354118364579871817345373444524587405076422897992003292938342288845145090234902658879183273889773153670451354962817517194401241019847).isSome = true := by
  decide +kernel

theorem k2745_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).2
      1730181734463866715226015705939150258911599192006449586768474238727849729130937125689337296787942381798037322494300304824008308071233574964144717).isSome = true := by
  decide +kernel

theorem k2745_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).1
      5825257433494970611817632805388144533631739096598547572196246663000448949471179882573630214127557083093303277160573791195227635).isSome = true := by
  decide +kernel

theorem k2745_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).2
      318293563328090892536603985387560095853266971914247552795613692262974667899687524143902037078203562808866289).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2745 2746 :=
  (Cover.one (box := dirCellBox) (n := 2745)
      (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k2745_0) (.split 2 (.leaf _ k2745_1) (.leaf _ k2745_2))) (.split 3 (.split 2 (.leaf _ k2745_3) (.leaf _ k2745_4)) (.split 2 (.leaf _ k2745_5) (.leaf _ k2745_6)))) (.split 3 (.split 3 (.leaf _ k2745_7) (.leaf _ k2745_8)) (.split 3 (.split 2 (.leaf _ k2745_9) (.leaf _ k2745_10)) (.split 2 (.leaf _ k2745_11) (.leaf _ k2745_12))))) (.split 2 (.split 3 (.split 3 (.split 3 (.leaf _ k2745_13) (.split 2 (.leaf _ k2745_14) (.leaf _ k2745_15))) (.split 2 (.split 3 (.leaf _ k2745_16) (.leaf _ k2745_17)) (.leaf _ k2745_18))) (.split 3 (.split 2 (.split 2 (.leaf _ k2745_19) (.leaf _ k2745_20)) (.split 3 (.leaf _ k2745_21) (.leaf _ k2745_22))) (.split 2 (.split 2 (.leaf _ k2745_23) (.leaf _ k2745_24)) (.split 2 (.leaf _ k2745_25) (.leaf _ k2745_26))))) (.split 3 (.split 3 (.leaf _ k2745_27) (.split 3 (.leaf _ k2745_28) (.leaf _ k2745_29))) (.split 3 (.split 2 (.leaf _ k2745_30) (.leaf _ k2745_31)) (.split 2 (.leaf _ k2745_32) (.leaf _ k2745_33)))))))

end C4.Cert.Dir057
