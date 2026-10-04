module

public import C4Check

public section

/-! Cells `1239 ≤ n < 1268` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir006

theorem k1239_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).1 2).1 1).1
      5436655877390026212399207409227026204255353195758941008395634804146842678197307231503146780307679557305753988361924817340360139).isSome = true := by
  decide +kernel

theorem k1239_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1239) 3).1 2).1 1).2 3).1
      244344347013762990173090083648737689614931951562083958439235492782661385521420787512).isSome = true := by
  decide +kernel

theorem k1239_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1239) 3).1 2).1 1).2 3).2
      3304910779354979249614658921145540924856231834819995652563786444).isSome = true := by
  decide +kernel

theorem k1239_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).1 2).2 1).1
      294827288906860754515219272311685194534754866342630899181012586276375899393495442095846426821821881049007559).isSome = true := by
  decide +kernel

theorem k1239_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).1 2).2 1).2
      87131054680737651005631981950086817632971036829714370676494666444453888443178328122222062544706651015166546091110402589015748403).isSome = true := by
  decide +kernel

theorem k1239_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).2 2).1 1).1
      73695851079490309680751515554181755859614251706035028510476248017214984207441778095321415853698887630409523).isSome = true := by
  decide +kernel

theorem k1239_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).2 2).1 1).2
      15965102715115386380407856732627832453925551779523169572659140513802503828437240335160199).isSome = true := by
  decide +kernel

theorem k1239_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).2 2).2 1).1
      1180407689180055962396065039178169246677221232868208599669682565877187246072304841939505276938770403372257075).isSome = true := by
  decide +kernel

theorem k1239_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1239) 3).2 2).2 1).2
      255511281197387835249588572783416598184002224417271919906450666806600988062740643010727111).isSome = true := by
  decide +kernel

theorem k1240_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).1 2).1 1).1
      62311060302774867067654949737145276510415150567167188219197283762876731590028011724003).isSome = true := by
  decide +kernel

theorem k1240_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).1 2).1 1).2
      997216866137380956247262696918764957903840782654494828453828890186926962577454625813299).isSome = true := by
  decide +kernel

theorem k1240_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).1 2).2 1).1
      62323457959208083777876659234328964348912509882972437191503745131440188026583466663139).isSome = true := by
  decide +kernel

theorem k1240_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).1 2).2 1).2
      997415519973164244675424469216814591402158437643533247031025684364098272418702201025331).isSome = true := by
  decide +kernel

theorem k1240_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).2 2).1 1).1
      996662049731357184358104216960445902356778992373997747752477121348081137168691788084018).isSome = true := by
  decide +kernel

theorem k1240_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).2 2).1 1).2
      996803253089196395045306978368142574134256524089297327986468520466570955662402832921394).isSome = true := by
  decide +kernel

theorem k1240_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).2 2).2 1).1
      997784320093432119597970624924716607524625275618410393452788538666050010651943112110898).isSome = true := by
  decide +kernel

theorem k1240_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1240) 3).2 2).2 1).2
      249470106997618930778259634427179679134294412592903959918273702275776619184951421399859).isSome = true := by
  decide +kernel

theorem k1241_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1241) 2).1 3).1 1).1
      54002573598083083443611246378990340941163994918751905569653039902258).isSome = true := by
  decide +kernel

theorem k1241_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1241) 2).1 3).1 1).2
      45781187973838638521508583239642968418052887346).isSome = true := by
  decide +kernel

theorem k1241_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1241) 2).1 3).2
      16330743338914418458934441221395030738246879347137979079427641908795164963959071944668040393).isSome = true := by
  decide +kernel

theorem k1241_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1241) 2).2 3).1 1).1
      997330414640421978739501946823961612397038131572711063244077677466117443881613146288946).isSome = true := by
  decide +kernel

theorem k1241_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1241) 2).2 3).1 1).2
      210983976294839223841547541128616705884111897114832373719133121740).isSome = true := by
  decide +kernel

theorem k1241_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1241) 2).2 3).2
      77053488570226259407608243857715124827019345023126871815782013735625079437521638005419822024234705057785828686021).isSome = true := by
  decide +kernel

theorem k1242_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1242) 2).1 3).1
      995418198602923106857760499757717082913578169221787344289829272129258023050896970707761).isSome = true := by
  decide +kernel

theorem k1242_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1242) 2).1 3).2
      248808353470417870930631196238909902875997562396711022823303043361870393185907993047857).isSome = true := by
  decide +kernel

theorem k1242_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1242) 2).2 3).1
      63715201103684326315362704272551301564338228499168185041758689633307099433670854401538609).isSome = true := by
  decide +kernel

theorem k1242_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1242) 2).2 3).2
      995238735224078556134832811592566647518455434393636290290318864293624027384567626298161).isSome = true := by
  decide +kernel

theorem k1243_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1243) 2).1
      4697184235947305417910327047044998654100088260112975576572729236576733685609319510113870317911116126064041159).isSome = true := by
  decide +kernel

theorem k1243_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1243) 2).2
      4697150322628821574253342635987556306474943237383979325838772691249342734565333048418367427978213135155485895).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 1244 1266 [
    44585658595638857076194190106413551805006086, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51] = true := by
  decide +kernel

theorem k1266_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1266) 3).1
      105635693829864521654291169696239685227117785454205305338078256620557755375468313015612388394319168639928385688785293826956032411257919706292846009663774).isSome = true := by
  decide +kernel

theorem k1266_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1266) 3).2 2).1 3).1
      978983049367751385000696368152121960813809385759620451355102688828323422776242499473).isSome = true := by
  decide +kernel

theorem k1266_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1266) 3).2 2).1 3).2
      62548815128720812986036824336965511928460181574478519257650696807286645802573721884489).isSome = true := by
  decide +kernel

theorem k1266_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1266) 3).2 2).2
      103074060186670498028854687893094914182901655390730666125210112946058300372854604457528679607559591841979088734039103759032315152192368525824255514695).isSome = true := by
  decide +kernel

theorem k1267_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).1 2).1 1).1
      999255076937624625374785676113165745040987551640058731441462608287561740778333107828807).isSome = true := by
  decide +kernel

theorem k1267_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).1 2).1 1).2
      401576848644965926784640978082967988242498751960136930775299896304480656365677908057745030462424834269754191754221583943461506248841187306985971507).isSome = true := by
  decide +kernel

theorem k1267_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).1 2).2 3).1
      1153753034598341477146568699273565081041543703434416718237031680740290909679197390464133490780970616506181).isSome = true := by
  decide +kernel

theorem k1267_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).1 2).2 3).2
      18445606957255083839483663416639943431118945454043812753057208479711122684611763708757091775744637981711537).isSome = true := by
  decide +kernel

theorem k1267_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).2 2).1 1).1
      249569544843990851491786039425726595547212381568351446543601669676150705196971011175139).isSome = true := by
  decide +kernel

theorem k1267_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).2 2).1 1).2
      1022323887816524523688931992050869316417453357902871775443180666875981502082790568970505415).isSome = true := by
  decide +kernel

theorem k1267_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).2 2).2 1).1
      62410189765837578056946717961666006337993867651118174502873332365593950807127242332979).isSome = true := by
  decide +kernel

theorem k1267_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1267) 3).2 2).2 1).2
      5440362598758732558760757019246507245856918179864312326512365857675359180571127062351823443265945480087706422178232327523916594).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1239 1268 :=
  (Cover.one (box := dirCellBox) (n := 1239)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1239_0) (.split 3 (.leaf _ k1239_1) (.leaf _ k1239_2))) (.split 1 (.leaf _ k1239_3) (.leaf _ k1239_4))) (.split 2 (.split 1 (.leaf _ k1239_5) (.leaf _ k1239_6)) (.split 1 (.leaf _ k1239_7) (.leaf _ k1239_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1240)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1240_0) (.leaf _ k1240_1)) (.split 1 (.leaf _ k1240_2) (.leaf _ k1240_3))) (.split 2 (.split 1 (.leaf _ k1240_4) (.leaf _ k1240_5)) (.split 1 (.leaf _ k1240_6) (.leaf _ k1240_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1241)
      (.split 2 (.split 3 (.split 1 (.leaf _ k1241_0) (.leaf _ k1241_1)) (.leaf _ k1241_2)) (.split 3 (.split 1 (.leaf _ k1241_3) (.leaf _ k1241_4)) (.leaf _ k1241_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1242)
      (.split 2 (.split 3 (.leaf _ k1242_0) (.leaf _ k1242_1)) (.split 3 (.leaf _ k1242_2) (.leaf _ k1242_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1243)
      (.split 2 (.leaf _ k1243_0) (.leaf _ k1243_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 1266)
      (.split 3 (.leaf _ k1266_0) (.split 2 (.split 3 (.leaf _ k1266_1) (.leaf _ k1266_2)) (.leaf _ k1266_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1267)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1267_0) (.leaf _ k1267_1)) (.split 3 (.leaf _ k1267_2) (.leaf _ k1267_3))) (.split 2 (.split 1 (.leaf _ k1267_4) (.leaf _ k1267_5)) (.split 1 (.leaf _ k1267_6) (.leaf _ k1267_7)))))

end C4.Cert.Dir006
