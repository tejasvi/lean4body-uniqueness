module

public import C4Check

public section

/-! Cells `1773 ≤ n < 1827` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir019

theorem k1773_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1773) 1).1
      1177471698792376504755350056882944514531652038726057527576961736184786208246586033748056514399078052673829948).isSome = true := by
  decide +kernel

theorem k1773_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1773) 1).2
      73610801954372986270637355932454798689901032387668249448394537089819295974344887699064284280392370240044092).isSome = true := by
  decide +kernel

theorem k1774_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1774) 1).1
      972934267837340995498750491893368995899991601150467771450738365347297680448638778428).isSome = true := by
  decide +kernel

theorem k1774_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1774) 1).2
      210991281469060343069640523627053064612824679038313337342091639868).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 1775 1776 [
    73442282043925684494821133665101780691996690938358982848726852728068787286500950307632332868676676103817459] = true := by
  decide +kernel

theorem c3 : allCells dirCell 1776 1797 [
    51437083751053218979804688296986159738478646917261704528797585, 147501405266149810996, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1797 1798 [
    6326189593175047517977358657960865675244921062330249115173834688228038165335110995670628808304860047320638227773785531860916215490315458504734279] = true := by
  decide +kernel

theorem k1798_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1798) 3).1
      4528426775661604793185172142860420145552722726191575981773003464894890595946749711764113580536502851058).isSome = true := by
  decide +kernel

theorem k1798_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1798) 3).2
      1575208406643762571000610383667368177781303242145091567412596183503722511223131982859788882098389423980845636755873829946418067918331574482728188).isSome = true := by
  decide +kernel

theorem k1799_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1799) 3).1
      5328701215400766588559204726109243552351928533349960583885725250837744575388515284007945783994598770442275144994425111303996).isSome = true := by
  decide +kernel

theorem k1799_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1799) 3).2
      288484452840982859927245345231960571130402869709053963626327762070301655274938009431390409185266534699836).isSome = true := by
  decide +kernel

theorem k1800_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1800) 3).1
      15620398651970688371855655759442309876010605352869927009477322656366846956663849075516).isSome = true := by
  decide +kernel

theorem k1800_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1800) 3).2
      15606495025409655701558954331110588086278703771939480768699664909214234985217391918140).isSome = true := by
  decide +kernel

theorem k1801_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1801) 2).1
      211231734089787995336628873030646049805668623262587090474938711100).isSome = true := by
  decide +kernel

theorem k1801_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1801) 2).2
      15589189325949519108827463519026083752364453339395122506033208149501528610614067839804).isSome = true := by
  decide +kernel

theorem k1802_0 : (checkBoxH dirMode depth (dirCellBox 1802)
      1890361381223004373343070825450861510472979216377685747175466109605942298196001692875322473930314281536450782105272086104845317058856579515902140777389950813697438659388).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 1803 1804 [
    84694248579475796041416840863880911970317009213071832029299786483538617253069533479211734259671083791552850130520989979472124] = true := by
  decide +kernel

theorem c11 : allCells dirCell 1804 1826 [
    51435218057473437297361014057371397385088760100546605109917777, 147499284995457047220, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    61507979103905063721011287147991121666620203256317827632956864422252134002312815187] = true := by
  decide +kernel

theorem k1826_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1826) 3).1
      15342475142792981095401445852028091200245948598516749337764568111197012511182458225).isSome = true := by
  decide +kernel

theorem k1826_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1826) 3).2
      393784741663188700904772233484965541678708507877440456322468677263416975960850345225787372661480052345496109343611955136773046190819697815377393).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1773 1827 :=
  (Cover.one (box := dirCellBox) (n := 1773)
      (.split 1 (.leaf _ k1773_0) (.leaf _ k1773_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1774)
      (.split 1 (.leaf _ k1774_0) (.leaf _ k1774_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1798)
      (.split 3 (.leaf _ k1798_0) (.leaf _ k1798_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1799)
      (.split 3 (.leaf _ k1799_0) (.leaf _ k1799_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1800)
      (.split 3 (.leaf _ k1800_0) (.leaf _ k1800_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1801)
      (.split 2 (.leaf _ k1801_0) (.leaf _ k1801_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1802)
      (.leaf _ k1802_0)).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 1826)
      (.split 3 (.leaf _ k1826_0) (.leaf _ k1826_1)))

end C4.Cert.Dir019
