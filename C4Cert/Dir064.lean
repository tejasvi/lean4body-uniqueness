module

public import C4Check

public section

/-! Cells `2802 ≤ n < 2804` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir064

theorem k2802_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).1 2).1 1).1
      19299917999659215523900661594064946339408444102319939305654379798767258728307764983524741527811980059726).isSome = true := by
  decide +kernel

theorem k2802_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).1 2).1 1).2
      1419202874485776532378269768153859344580649484926773146952184762035077455936327618340109020357296116556302550756820929574386).isSome = true := by
  decide +kernel

theorem k2802_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).1 2).2
      77260990112227393991526858416228824390438706298661111153323709107849463062420757683780025956431678925897).isSome = true := by
  decide +kernel

theorem k2802_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).1 1).1 2).1
      4768177161198196360883917452026213926587196360058533987287150098803402972506363640782911286151137791345).isSome = true := by
  decide +kernel

theorem k2802_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).1 1).1 2).2
      4043334095365588099475793644508642917707843688340830047583733570864555883799731580).isSome = true := by
  decide +kernel

theorem k2802_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).1 1).2 2).1
      19005101384364618440261649258946750242768345810506018440796372082702098365610448588286589476958321166707).isSome = true := by
  decide +kernel

theorem k2802_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).1 1).2 2).2
      4034716795289742158186029277764415933132629930548326925014168521927786722001640828).isSome = true := by
  decide +kernel

theorem k2802_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2802) 3).1 3).2 2).2
      1963247981684962166808617772969114203417337742019646797419946818977483514071989054970018033526220753684231506205523329362396321507737733691244097869732906670469866953).isSome = true := by
  decide +kernel

theorem k2802_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 1).1 2).1
      16365612692397857757700155574932408457121468037452662735392280652224862469726599214332).isSome = true := by
  decide +kernel

theorem k2802_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 1).1 2).2
      3472171627570097766803429501258161049673272940852803181963498748).isSome = true := by
  decide +kernel

theorem k2802_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 1).2 2).1
      4083726161201029378133274216191676734224782192799894170558453823253837939261908178748).isSome = true := by
  decide +kernel

theorem k2802_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).1 1).2 2).2
      63989920937441501740742860506738818774985910964901449958850354691638711855666812732).isSome = true := by
  decide +kernel

theorem k2802_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 1).1 2).1
      253620941478149613287020220860367138188908706538609336175002713056208020362583760316).isSome = true := by
  decide +kernel

theorem k2802_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 1).1 2).2
      254124684107055850923659205274457033803407119514511406498432879481213070571055242684).isSome = true := by
  decide +kernel

theorem k2802_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 1).2 2).1
      4059330522969091037868987586385951741773801457448162118306457382313522491598380882354).isSome = true := by
  decide +kernel

theorem k2802_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).1 3).2 1).2 2).2
      253921955226734944150879435912109151300936142143705546537198368640535655477058967356).isSome = true := by
  decide +kernel

theorem k2802_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).1 1).1
      1392833070754657213994740054615418646868282876920096555735381044699517254949684220500762981400368237443349598622292143338994).isSome = true := by
  decide +kernel

theorem k2802_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).1 1).2
      411812490925322015547376930241694428874286295966973921175022611063108616000123693205441725629600851837700585235607920916611407678262152187704818).isSome = true := by
  decide +kernel

theorem k2802_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).2 1).1
      88679888144469067402429712187972631702768628548441313983080794614363105475943533174017133851437871371914389212636114822469362).isSome = true := by
  decide +kernel

theorem k2802_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2802) 3).2 2).2 3).2 1).2
      307428358442496679235172997296855940785692014418431130322358062779743072887632618403024261115220125771486130).isSome = true := by
  decide +kernel

theorem k2803_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).1 1).1
      64540757723615781587775002933602940518782695234963850425781020624483410029017072786236).isSome = true := by
  decide +kernel

theorem k2803_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).1 1).2
      4758961097910013113088388961754794950135058784234685653856753203151244620777400104522079607322568975545148).isSome = true := by
  decide +kernel

theorem k2803_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).2 1).1
      13682367689945090744558017776764603090049981316272001064550161596).isSome = true := by
  decide +kernel

theorem k2803_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).1 2).2 1).2
      54639097364500471151802006238763045939079714532659922429661825852).isSome = true := by
  decide +kernel

theorem k2803_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).1 1).1
      16052696092497896267666422095515792223799855389536833905956309549605965934913384970812).isSome = true := by
  decide +kernel

theorem k2803_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).1 1).2
      64132641094354845025579440301309628677072245085551373208450559167707931588605824093756).isSome = true := by
  decide +kernel

theorem k2803_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).2 1).1
      217694747395371784542317518781913110464006719657314765584163822396).isSome = true := by
  decide +kernel

theorem k2803_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).1 3).2 2).2 1).2
      1003275723102345045902559921391596233357003892014526053904079605408796177556106110636).isSome = true := by
  decide +kernel

theorem k2803_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).1 1).1
      1222499664887930154012149616996963904017388830582060244678355160636130552753227582518412267413640789861430002).isSome = true := by
  decide +kernel

theorem k2803_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).1 1).2
      1220620281731562129405509710087601551748816779146111732869701226386375272839942517997079411542548269250352050).isSome = true := by
  decide +kernel

theorem k2803_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).2 2).1
      22396303780113473234645751818991808262786394649274257668489620258007366861955508709449325283545448835086041171281805629288242417).isSome = true := by
  decide +kernel

theorem k2803_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).1 2).2 3).2 2).2
      5603602175155732474446308950914249979926092200605166926566816265484732355857506623951504102570471767152265570911130118005349617).isSome = true := by
  decide +kernel

theorem k2803_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).1 1).1
      865638472848229407473533252842552293844962892844151554350830315180).isSome = true := by
  decide +kernel

theorem k2803_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).1 1).2
      63838873842799648279797977779486387128370737969176880840080974871176226429717819939388).isSome = true := by
  decide +kernel

theorem k2803_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).2 1).1
      3388373162263295756380806638630554677183253553666910403418252972).isSome = true := by
  decide +kernel

theorem k2803_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).1 2).2 1).2
      15977822438070508562353232588195315026049164117420817616880429721010363358710725581372).isSome = true := by
  decide +kernel

theorem k2803_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).1 1).1
      63619901217580796751532510108209494831674605953672368510589296506232350005880199445676).isSome = true := by
  decide +kernel

theorem k2803_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).1 1).2
      3452085333434723366316891099662709167817798767174960964911981130300).isSome = true := by
  decide +kernel

theorem k2803_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).2 1).1
      215812537548762861486433276127058768742994802229579145483628444076).isSome = true := by
  decide +kernel

theorem k2803_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).1 3).2 2).2 1).2
      46809085959356349623883231007870776602676660796).isSome = true := by
  decide +kernel

theorem k2803_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 3).1 2).1
      4833956105627891385470145118102549030319587406862971764718741198413908763564861644959393222908855927792282865).isSome = true := by
  decide +kernel

theorem k2803_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 3).1 2).2
      22311002645458745949955562282934012813439805876080004305575981648354199613924450861787447633846755662731389466558064801397497073).isSome = true := by
  decide +kernel

theorem k2803_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 3).2 2).1 1).1
      843768254530276102257346382880508679745523041016677454577236396).isSome = true := by
  decide +kernel

theorem k2803_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 3).2 2).1 1).2
      215879651045624021210459381839613322561640381087048232383987812924).isSome = true := by
  decide +kernel

theorem k2803_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2803) 3).2 2).2 3).2 2).2
      301195855853046194118760446992695401187908254675895161694840898774534613988249283080634357999623427094849201).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2802 2804 :=
  (Cover.one (box := dirCellBox) (n := 2802)
      (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2802_0) (.leaf _ k2802_1)) (.leaf _ k2802_2)) (.split 2 (.split 1 (.split 2 (.leaf _ k2802_3) (.leaf _ k2802_4)) (.split 2 (.leaf _ k2802_5) (.leaf _ k2802_6))) (.leaf _ k2802_7))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k2802_8) (.leaf _ k2802_9)) (.split 2 (.leaf _ k2802_10) (.leaf _ k2802_11))) (.split 1 (.split 2 (.leaf _ k2802_12) (.leaf _ k2802_13)) (.split 2 (.leaf _ k2802_14) (.leaf _ k2802_15)))) (.split 3 (.split 1 (.leaf _ k2802_16) (.leaf _ k2802_17)) (.split 1 (.leaf _ k2802_18) (.leaf _ k2802_19)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2803)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2803_0) (.leaf _ k2803_1)) (.split 1 (.leaf _ k2803_2) (.leaf _ k2803_3))) (.split 2 (.split 1 (.leaf _ k2803_4) (.leaf _ k2803_5)) (.split 1 (.leaf _ k2803_6) (.leaf _ k2803_7)))) (.split 3 (.split 1 (.leaf _ k2803_8) (.leaf _ k2803_9)) (.split 2 (.leaf _ k2803_10) (.leaf _ k2803_11)))) (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2803_12) (.leaf _ k2803_13)) (.split 1 (.leaf _ k2803_14) (.leaf _ k2803_15))) (.split 2 (.split 1 (.leaf _ k2803_16) (.leaf _ k2803_17)) (.split 1 (.leaf _ k2803_18) (.leaf _ k2803_19)))) (.split 3 (.split 2 (.leaf _ k2803_20) (.leaf _ k2803_21)) (.split 2 (.split 1 (.leaf _ k2803_22) (.leaf _ k2803_23)) (.leaf _ k2803_24))))))

end C4.Cert.Dir064
