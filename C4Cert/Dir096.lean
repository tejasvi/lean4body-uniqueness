module

public import C4Check

public section

/-! Cells `3260 ≤ n < 3283` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir096

theorem k3260_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3260) 2).1
      21169448644335787190186727732852194284367039315920823936685761677580000035153816945576976131134357378729922057816375835319731).isSome = true := by
  decide +kernel

theorem k3260_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3260) 2).2 3).1
      3888981984933894329970154659317618700869104905839312017243625746466780436368566121020).isSome = true := by
  decide +kernel

theorem k3260_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3260) 2).2 3).2
      13174033616577447641741852640432095799792094195113286139530048060).isSome = true := by
  decide +kernel

theorem k3261_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3261) 2).1
      84653911563540233434550711844059638084434781368498453946566075716972366913325970723163826539073565028380525160417621975332081).isSome = true := by
  decide +kernel

theorem k3261_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3261) 2).2
      4589651656168386955930671735554396513350234877984320918000654617568743271369127382627628027342670186503345).isSome = true := by
  decide +kernel

theorem k3262_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3262) 2).1
      15181866843440108360088732406373733293670393726915746753626854952383923454062246257).isSome = true := by
  decide +kernel

theorem k3262_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3262) 2).2
      248746471978987831556993233296176649865005399465701110647895711777635381481261664093389).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3263 3264 [
    21157361221952720626157470746209795963190285982083252121272350489999193947316665854118985501734617619805577421755310582239814] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3264 3279 [
    205692683290472006571175077668207028281975585372809116079836818, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 46581374718034747866479756535733294770254387] = true := by
  decide +kernel

theorem k3279_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3279) 3).1 2).1
      21910520138782481079889543900300315141201378406741993130581678349879553161395518065577420960203219971210387497854662230568263).isSome = true := by
  decide +kernel

theorem k3279_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3279) 3).1 2).2
      62867184161135514018161351414644644608935765412763584398822017363835195621835516275).isSome = true := by
  decide +kernel

theorem k3279_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3279) 3).2 2).1 1).1
      18415550364318051636507603220235474717003480565416235202734626643874855177505531105598982771712852796787).isSome = true := by
  decide +kernel

theorem k3279_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3279) 3).2 2).1 1).2
      64031028007118835990120030387219400293064803228710113461490000306861063578820125547698).isSome = true := by
  decide +kernel

theorem k3279_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3279) 3).2 2).2
      1892218633370347085025698150670250991262862662602244047429003984344594960303938659346764200758747818173081221084994344179279998218892309444227605888379853427617592777).isSome = true := by
  decide +kernel

theorem k3280_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).1 2).1 1).1
      63614363432165775795400757179552532699142793723866750842134075881440783816220032130226).isSome = true := by
  decide +kernel

theorem k3280_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).1 2).1 1).2
      63594574795680279864390905207633949446481498566427818842243710693048723145151667870514).isSome = true := by
  decide +kernel

theorem k3280_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).1 2).2 1).1
      3976275200338752351370904585558108962718344911553797774713547196997853598523393037116).isSome = true := by
  decide +kernel

theorem k3280_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).1 2).2 1).2
      3978789833621624911276237620580547660320865810725698421207706623163533823632741914418).isSome = true := by
  decide +kernel

theorem k3280_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).2 2).1 2).1
      4786672305379935364500942038909159023984856628598454588468881021837458984537828015838823438697846304472953073).isSome = true := by
  decide +kernel

theorem k3280_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).2 2).1 2).2
      299221700627795030974268585949679101849264887021314924389487169902974820689795545388563570044761698960243889).isSome = true := by
  decide +kernel

theorem k3280_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).2 2).2 1).1
      1169378865385084412083411192959461221981248365587363861685555550573232264180627759168727117005330150980780).isSome = true := by
  decide +kernel

theorem k3280_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3280) 3).2 2).2 1).2
      253506668441383901711343392691948785853347681792567918537192957804789517089959637261106).isSome = true := by
  decide +kernel

theorem k3281_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).1 2).1 1).1
      66209534284829186474425086669756068127866663741731373045994525386792336570790803653918912754).isSome = true := by
  decide +kernel

theorem k3281_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).1 2).1 1).2
      1010113196187077334575823376774413247551362543129366541802809467010366956543570601941810).isSome = true := by
  decide +kernel

theorem k3281_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).1 2).2 1).1
      63162290707385978973866871445835245037579525383583990470926708714172201069409425751100).isSome = true := by
  decide +kernel

theorem k3281_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).1 2).2 1).2
      252593419707243527445600866858373324201304260922918310884967557641509092261126521797692).isSome = true := by
  decide +kernel

theorem k3281_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).2 2).1 1).1
      21937697442446631807062467588264225643596012341547198112820558122320029022019044383905991218203610167022061867313820898667445308).isSome = true := by
  decide +kernel

theorem k3281_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).2 2).1 1).2
      4028788332466341531134929268834750375840696793695794594739947387426459440108913190923058).isSome = true := by
  decide +kernel

theorem k3281_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).2 2).2 1).1
      62981179084775369788003856393921202069527167010970489077008754565814825885112456821820).isSome = true := by
  decide +kernel

theorem k3281_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3281) 3).2 2).2 1).2
      251872672310888018915512716996311805703501708809231713341924226342414718141825627667516).isSome = true := by
  decide +kernel

theorem k3282_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).1 3).1 1).1
      296607398357830246380712768078998601778172108114744121965835174638383231550971007385625365060238024264956988).isSome = true := by
  decide +kernel

theorem k3282_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).1 3).1 1).2
      16067208676005944877863075466490857659794371171167250266985579864606241314409899766475571).isSome = true := by
  decide +kernel

theorem k3282_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).1 3).2 1).1
      16048205404476479743347210861224742500703633476352999126461800209991940229142207956466748).isSome = true := by
  decide +kernel

theorem k3282_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).1 3).2 1).2
      73998807656232825766590717679519785996171678779387761869504548333551025100103779140824604858583548451140556).isSome = true := by
  decide +kernel

theorem k3282_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).2 3).1 1).1
      3408069522420542939570104564961930610210670440214199390827083250748).isSome = true := by
  decide +kernel

theorem k3282_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).2 3).1 1).2
      1005123714598345267782183587338958881522061451919230374317430168510794762581159468774348).isSome = true := by
  decide +kernel

theorem k3282_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).2 3).2 1).1
      3399536794393302637470057566952837462876962180029777255508058258492).isSome = true := by
  decide +kernel

theorem k3282_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3282) 2).2 3).2 1).2
      54384217718070963110708604126985487561689305309499178259551546958796).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3260 3283 :=
  (Cover.one (box := dirCellBox) (n := 3260)
      (.split 2 (.leaf _ k3260_0) (.split 3 (.leaf _ k3260_1) (.leaf _ k3260_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3261)
      (.split 2 (.leaf _ k3261_0) (.leaf _ k3261_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3262)
      (.split 2 (.leaf _ k3262_0) (.leaf _ k3262_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 3279)
      (.split 3 (.split 2 (.leaf _ k3279_0) (.leaf _ k3279_1)) (.split 2 (.split 1 (.leaf _ k3279_2) (.leaf _ k3279_3)) (.leaf _ k3279_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3280)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3280_0) (.leaf _ k3280_1)) (.split 1 (.leaf _ k3280_2) (.leaf _ k3280_3))) (.split 2 (.split 2 (.leaf _ k3280_4) (.leaf _ k3280_5)) (.split 1 (.leaf _ k3280_6) (.leaf _ k3280_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3281)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3281_0) (.leaf _ k3281_1)) (.split 1 (.leaf _ k3281_2) (.leaf _ k3281_3))) (.split 2 (.split 1 (.leaf _ k3281_4) (.leaf _ k3281_5)) (.split 1 (.leaf _ k3281_6) (.leaf _ k3281_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3282)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3282_0) (.leaf _ k3282_1)) (.split 1 (.leaf _ k3282_2) (.leaf _ k3282_3))) (.split 3 (.split 1 (.leaf _ k3282_4) (.leaf _ k3282_5)) (.split 1 (.leaf _ k3282_6) (.leaf _ k3282_7)))))

end C4.Cert.Dir096
